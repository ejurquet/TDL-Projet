(* Auteurs : Benjamin Coupry & Eliès Jurquet *)

(* Module de la passe de gestion des identifiants *)
module PassePlacementRat : Passe.Passe with type t1 = Ast.AstType.programme and type t2 = Ast.AstPlacement.programme =
struct

  open Tds
  (* open Exceptions *)
  open Ast
  open AstType
  open AstPlacement
  open Type

  type t1 = AstType.programme
  type t2 = AstPlacement.programme

  
(* analyse_placement_instruction : instruction -> int -> string -> int *)
(* Paramètre i : l'instruction a placer en memoire *)
(* Paramètre base : l'e deplacement initial dans le registre *)
(* Paramètre reg : le registre de travail *)
(* Calcule les deplacements des instructions *)
  let rec analyse_placement_instruction i base reg =
    match i with
    | Declaration(_, info) ->
      begin
        match info_ast_to_info info with
        | InfoVar(_, t, _, _) -> 
          begin
            modifier_adresse_info base reg info;
            getTaille t
          end
        | _ -> failwith "Erreur interne."
      end
    | Conditionnelle (_, t, e) ->
      begin
        analyse_placement_bloc t base reg;
        analyse_placement_bloc e base reg;
        0
      end
    | TantQue(_, b) ->
      begin
        analyse_placement_bloc b base reg;
        0
      end
	  | Switch (_, cl) ->
	    (* Analyse de l expression comparee *)
	    let _ = analyse_placement_listcase cl base reg in
      0
    | _ -> 0
	
  (* analyse_placement_listcase : case list -> int -> string -> unit *)
  (* Paramètre cl : liste de case a placer en memoire *)
  (* Paramètre base : le deplacement initial dans le registre *)
  (* Paramètre reg : le registre de travail *)
  (* Calcule les deplacements des case *)
  (* renvoie unit *)
  and analyse_placement_listcase cl base reg  =
		let _ = List.map (analyse_placement_case base reg) cl in ()
  (* analyse_placement_case : int -> string -> case -> unit *)
  (* Paramètre case : lcase a placer en memoire *)
  (* Paramètre base : le deplacement initial dans le registre *)
  (* Paramètre reg : le registre de travail *)
  (* Calcule les deplacements du case *)
  (* renvoie unit *)
  and analyse_placement_case base reg case=
    match case with
      | CaseTid(_, il, _) -> 
        begin
          analyse_placement_bloc il base reg;
        end
      | CaseEntier(_, il, _) -> 
        begin
          analyse_placement_bloc il base reg;
        end
      | CaseTrue (il, _) -> 
        begin
          analyse_placement_bloc il base reg;
        end
      | CaseFalse (il, _) -> 
        begin
          analyse_placement_bloc il base reg;
        end
      | CaseDefault(il, _) -> 
        begin
          analyse_placement_bloc il base reg;
        end
      
	
  (* analyse_placement_bloc : AstType.bloc -> int -> string -> unit *)
  (* Paramètre li : bloc d'instructions a placer en memoire *)
  (* Paramètre base : le deplacement initial dans le registre *)
  (* Paramètre reg : le registre de travail *)
  (* calcule les deplacements des instructions *)
  (*renvoie unit*)
  and analyse_placement_bloc li base reg =
    let _ = List.fold_left (fun t qt -> t + (analyse_placement_instruction qt t reg)) base li in ()

  (* Solution alternative : 
  Sinon on reverse la liste d'instructions pour pouvoir appliquer un fold_right dessus.
  Dans le fold_right la queue traitée réprésente la position où l'on écrit l'instruction et
  la tête représente l'instruction à traiter. De plus, analyse_placement_instruction nous renvoie
  la taille de l'instruction à traitrer. Ainsi, l'écriture suivante se fait à qt + taille.
  
  let _ = List.fold_right (fun t qt -> qt + (analyse_placement_instruction t qt reg)) (List.rev li) base in ()*)


  (* analyse_placement_parametre : info_ast -> int -> int *)
  (* Paramètre info : l'info faisant reference au parametre a placer *)
  (* Paramètre base : le deplacement initial dans le registre *)
  (* Calcule les deplacement et le placement memoire d'un bloc de parametres *)
  (* renvoie unit *)
  let analyse_placement_parametre info base =
    match info_ast_to_info info with
    | InfoVar(_, t, _, _) ->
      begin
        let _ = modifier_adresse_info (base - getTaille t) "LB" info in getTaille t 
      end
    | _ -> failwith ("Erreur interne : erreur placement paramètre.")

  (* analyse_placement_parametre : info_ast list -> int *)
  (* Paramètre info : liste de case a placer en memoire *)
  (* Paramètre base : le deplacement initial dans le registre *)
  (* calcule les deplacement et le placement memoire d'un bloc de parametres *)
  (*renvoie unit*)
  let analyse_placement_parametres lp =
    List.fold_left (fun d p -> d + analyse_placement_parametre p (-d)) 0 (List.rev lp)

  (* analyse_placement_fonction : AstType.fonction -> AstPlacement.fonction *)
  (* Paramètre AstType.Fonction : fonction dont il faut placer les parametres et le corps *)
  (*renvoie unit*)
  let analyse_placement_fonction (AstType.Fonction(info, lp, li, e)) =
    let _ = analyse_placement_parametres lp in
    analyse_placement_bloc li 3 "LB";
    Fonction(info, lp, li, e)
      
  (* analyser : t1 -> t2 *)
  let analyser (AstType.Programme(fonctions, prog)) =
    let nfonctions = List.map analyse_placement_fonction fonctions in
    analyse_placement_bloc prog 0 "SB";
    Programme (nfonctions, prog)

end
