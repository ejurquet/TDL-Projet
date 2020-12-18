(* Module de la passe de génération de code *)
module PasseCodeRatToTam : Passe.Passe with type t1 = Ast.AstPlacement.programme and type t2 = string =
struct

  open Tds
  open Ast
  open AstType
  open AstPlacement
  open Type
  open Code

  type t1 = AstPlacement.programme
  type t2 = string

  (* expression -> string *)
  (* Produit le code correspondant à l'instruction. L’exécution de ce code laissera
   * en sommet de pile le résultat de l’évaluation de cette expression. *)
  let rec analyse_code_expression e =
    match e with
      | AppelFonction (info, le) ->
        begin
          match info_ast_to_info info with 
            | InfoFun(n, _, _) ->
              begin
                let gen = List.fold_right (fun t qt -> (analyse_code_expression t) ^ qt ) le "" in
                gen ^ "CALL (SB) " ^ n ^ "\n"
              end
            | _ -> failwith "Erreur interne."
        end
      | Rationnel (e1, e2) ->
        (analyse_code_expression e1) ^ (analyse_code_expression e2)
      | Numerateur e1 ->
        (analyse_code_expression e1) ^ "POP (0) 1\n"
      | Denominateur e1 ->
        (analyse_code_expression e1) ^ "POP (1) 1\n"
      | Ident info ->
        begin
          match (info_ast_to_info info) with
            | InfoVar(_, t, dep, reg) -> "LOAD (" ^ (string_of_int (getTaille t)) ^ ") " ^ (string_of_int dep) ^ "[" ^ reg ^ "]\n"
            | InfoConst(_, v) -> "LOADL" ^ (string_of_int v) ^ "\n"
            | _ -> failwith "Erreur interne."
        end
      | True -> "LOADL 1\n"
      | False -> "LOADL 0\n"
      | Entier i -> "LOADL " ^ (string_of_int i) ^ "\n"
      | Binaire (b, e1, e2) ->
        begin
          let gen_e1 = analyse_code_expression e1 in
          let gen_e2 = analyse_code_expression e2 in
          let gen = gen_e1 ^ gen_e2 in
          let ope =
            match b with
              | PlusInt -> "SUBR IAdd"
              | PlusRat -> "CALL (ST) RAdd"
              | EquInt -> "SUBR IEq"
              | EquBool -> "SUBR BEq"
              | MultInt -> "SUBR IMul"
              | MultRat -> "CALL (ST) RMUL"
              | Inf ->  "SUBR ILss"
          in gen ^ ope ^ "\n"
        end

  (* instruction -> -> string *)
  let rec analyse_code_instruction i =
    match i with
      | Declaration (e, info) ->
        begin
          match (info_ast_to_info info) with 
            | InfoVar(_, t, dep, reg) ->
              "PUSH " ^ (string_of_int (getTaille t)) ^ "\n" ^
              (analyse_code_expression e) ^
              "STORE (" ^ (string_of_int (getTaille t)) ^ ") " ^ (string_of_int dep) ^ "[" ^ reg ^ "]\n"
            | _ -> failwith "Erreur interne."
        end
      | Affectation (e, info) ->
        begin
          match (info_ast_to_info info) with
            | InfoVar(_, t, dep, reg) ->
              begin
                (analyse_code_expression e) ^ "STORE (" ^ (string_of_int (getTaille t)) ^ ") " ^ (string_of_int dep) ^ "[" ^ reg ^ "]\n"
              end
            | _ -> failwith "Erreur interne."
        end
      | AffichageInt e ->
        (analyse_code_expression e) ^"SUBR IOut\n"
      | AffichageRat e ->
        (analyse_code_expression e) ^"CALL (SB) ROut\n"
      | AffichageBool e ->
        (analyse_code_expression e) ^"SUBR BOut\n"
      | Conditionnelle (cond, bloc_then, bloc_else) ->
        begin
          let lelse = getEtiquette() in
          let lfinelse = getEtiquette() in 
          (analyse_code_expression cond)
          ^ "JUMPIF (0) " ^ lelse ^ "\n"
          ^ (analyse_code_bloc bloc_then)
          ^ "JUMP " ^ lfinelse ^ "\n"
          ^ lelse ^ "\n"
          ^ (analyse_code_bloc bloc_else)
          ^ lfinelse ^ "\n"
        end
      | TantQue (c, b) ->
        begin
          let ldebutelse = getEtiquette() in
          let lfinelse = getEtiquette() in
          ldebutelse ^ "\n"
          ^ (analyse_code_expression c)
          ^ "JUMPIF (0) " ^ lfinelse ^ "\n"
          ^ (analyse_code_bloc b)
          ^ "JUMP " ^ ldebutelse ^ "\n"
          ^ lfinelse ^ "\n"
        end
      | Empty -> ""
    

  (* - Déterminer la taille occupée par les variables locales de ce bloc
   *   (il peut être utile d’introduire une fonction auxiliaire qui donne
   *   la taille occupée par une instruction : Decl => taille du type / autre => 0)
   * - Générer le code pour la liste d’instructions
   *   suivi de la libération des variables locales (POP (0) taillevarloc) *)
  and analyse_code_bloc li =
    let taille = List.fold_right (fun i ti -> (taille_variables_declarees i) + ti) li 0 in
    let popfinal = "POP (0) " ^ (string_of_int taille) ^ "\n" in
    (analyse_code_li li) ^ popfinal


  (* une liste d’instruction est un bloc dont on ignore la taille des variables locales *)
  and analyse_code_li li =
    String.concat "" (List.map analyse_code_instruction li)

  (* AstPlacement.fonction -> string *)
  let analyse_code_fonction (Fonction(info, _, li, e)) =
    match (info_ast_to_info info) with
      | InfoFun(nom, typeRet, typeParams) ->
        begin
          (* déterminer la taille des variables locales *)
          let taille_varloc = List.fold_right (fun i ti -> (taille_variables_declarees i) + ti) li 0 in
          (* déterminer la taille occup ́ee par les paramètres *)
          let taille_parametres = List.fold_right (fun i ti -> (getTaille i) + ti) typeParams 0 in
          nom ^ "\n"
          ^ (analyse_code_bloc li)
          ^ (analyse_code_expression e)
          ^ "POP (" ^ (string_of_int (getTaille typeRet)) ^ ") " ^ (string_of_int taille_varloc) ^ "\n"
          ^ "RETURN (" ^ (string_of_int (getTaille typeRet)) ^ ") " ^ (string_of_int taille_parametres) ^ "\n"
        end
      | _ -> failwith "Erreur interne."

    let analyser (AstPlacement.Programme(fonctions, prog)) =
      let entete = getEntete() in
      let corps_fonction = String.concat "" (List.map analyse_code_fonction fonctions) in
      let corps_prog = analyse_code_bloc prog in
      entete ^ corps_fonction ^ "\nmain" ^ "\n" ^ corps_prog ^ "\n" ^ "HALT"

end