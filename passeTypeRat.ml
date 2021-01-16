(* Auteurs : Benjamin Coupry & Eliès Jurquet *)

(* Module de la passe de typage *)
module PasseTypeRat : Passe.Passe with type t1 = Ast.AstTds.programme and type t2 = Ast.AstType.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstType
  open Type

  type t1 = AstTds.programme
  type t2 = AstType.programme
    
  (* type_trouve_exprenum : AstTds.expression -> typ list -> typ *)
  (* Paramètre e : expression d'enum à typer *)
  (* Paramètre enums : ensemble des types d'enums *)
  (* Calcule le type d'une expression d'enum et renvoie le type calculé *)
  let type_trouve_exprenum e (enums:(typ list)) =
    match e with
    | (AstTds.ExpressionEnum(id)) -> 
      begin
        let predicat = fun enum ->
            begin
              match enum with
              | TypeEnum(_, lid) -> List.exists (fun idl -> id = idl ) lid
              | _ -> failwith "Erreur Interne"
            end
            in 
            match List.find_opt predicat enums with
            | None -> raise (MauvaiseUtilisationIdentifiant id)
            | Some r -> r
      end
    | _ -> failwith "Erreur interne"

  (* exprenum_toint : AstTds.expression -> typ -> int *)
  (* Paramètre e : expression d'enum à typer *)
  (* paramètre v : type de cette expression *)
  (* Calcule l'equivalent entier d'une expression d'enum *)
  (* renvoie la valeur de l'enum : int *)
  (* Erreur si l'enum n'est pas incluse dans son type *)
  let exprenum_toint e v =
    match e, v with
    | AstTds.ExpressionEnum(id), TypeEnum(_, lid) ->
      begin
        let rec indexOf i li n =
          match li with
          | t::q ->
            begin
              if t=i then n
              else indexOf i q (n+1)
            end
          | []-> raise (MauvaiseUtilisationIdentifiant id)
        in indexOf id lid 0
      end
    | _ -> failwith "Erreur interne"

  (* analyse_type_affectable : AstTds.affectable -> affectable * typ *)
  (* Paramètre af : l'affectable à analyser *)
  (* Vérifie la bonne utilisation des types et calcule le type de l'expression *)
  (* renvoie un tuple de l'affectable traité et de son type *)
  (* Erreur si tentative de prendre la valeur d'autre chose sur un pointeur *)
  let rec analyse_type_affectable (af:AstTds.affectable) : (affectable * typ)  =
    match af with
    | Ident info ->
      begin
        match info_ast_to_info info with
        | InfoVar (_,t,_,_) -> (Ident info, t)
        | InfoConst _ -> (Ident info, Int)
        | _ -> failwith "Erreur interne : symbole non trouvé"
      end
    | Valeur aff ->
      begin
        match (analyse_type_affectable aff) with
        | (naf, Pointeur tp) -> (Valeur naf, tp)
        | _ -> let (_,ts) = analyse_type_affectable aff in
         raise (PasUnPointeur (string_of_type ts))
      end

  (* analyse_type_expression : typ list -> AstTds.expression -> expression * typ *)
  (* Paramètre tpEnums : la liste des types des enums *)
  (* Paramètre e : l'expression à analyser *)
  (* Vérifie la bonne utilisation des types et calcule le type de l'expression *)
  (* renvoie un tuple de l'expression traitee et de son type *)
  (* Erreur si types incompatibles *)
  let rec analyse_type_expression tpEnums e =
    match e with
    | AstTds.AppelFonction(info, le) ->
      begin
        match info_ast_to_info info with
        | InfoFunSurcharges(lif) ->
          begin
            let nlet = List.map(fun ei -> analyse_type_expression tpEnums ei) le in
            let nle = List.map(fst) nlet in
            let ltype = List.map(snd) nlet in
            let funsigmatch = (
              fun i -> 
                begin
                  match i with
                  | InfoFun (_, _, typeParams) -> est_compatible_list typeParams ltype
                  | _ -> failwith "Erreur interne"
                end
              ) in
            (*trouver la signature qui correspond*)
            let signaturematch = List.find_opt (funsigmatch) lif in
            match signaturematch with
            (*Pas de signature trouvee*)
            | None -> raise (TypesParametresInattendus([], ltype))
            (*Signature trouvee*)
            | Some info -> 
              begin
                match info with
                | InfoFun (_, typeret, _) -> (AppelFonction (info_to_info_ast info, nle), typeret)
                | _ -> failwith "Erreur interne"
              end
          end
        | _ -> failwith "Erreur interne."
      end
  | AstTds.Rationnel(e1, e2) ->
      begin
        let (ne1, t1) = analyse_type_expression tpEnums e1 in
        let (ne2, t2) = analyse_type_expression tpEnums e2 in
        if t1 = Int then 
          if t2 = t1 then
            (Rationnel(ne1, ne2), Rat)
          else
            raise (TypeInattendu(t2, Int))
        else
          raise (TypeInattendu(t1, Int))
      end
  | AstTds.Numerateur(e1) ->
      begin
        let (ne1, t1) = analyse_type_expression tpEnums e1 in
        if t1 = Rat then
          (Numerateur ne1, Int)
        else 
          raise (TypeInattendu(t1, Rat))
      end
  | AstTds.Denominateur(e1) ->
      begin
        let (ne1, t1) = analyse_type_expression tpEnums e1 in
        if t1 = Rat then
          (Denominateur ne1, Int)
        else 
          raise (TypeInattendu(t1, Rat))
      end
  | AstTds.Ident(info) ->
      begin
        match info_ast_to_info info with
          | InfoVar(_, t, _, _) -> (Ident info, t)
          | InfoConst(_, _) -> (Ident info, Int)
          | _ -> failwith("Internal error : symbol not found")
      end
  | AstTds.True ->
      begin
        (True, Bool)
      end
  | AstTds.False ->
      begin
        (False, Bool)
      end
  | AstTds.Entier(i) ->
      begin
        (Entier i, Int)
      end
  | AstTds.Binaire(b, e1, e2) ->
      begin
        let (ne1, t1) = analyse_type_expression tpEnums e1 in
        let (ne2, t2) = analyse_type_expression tpEnums e2 in
        match (t1, b, t2) with
          | (Int, Plus, Int) ->
            begin
              (Binaire(PlusInt, ne1, ne2), Int)
            end
          | (Rat, Plus, Rat) ->
            begin
              (Binaire(PlusRat, ne1, ne2), Rat)
            end
          | (Int, Equ, Int) ->
            begin
              (Binaire(EquInt, ne1, ne2), Bool)
            end
          | (Bool, Equ, Bool) ->
            begin
              (Binaire(EquBool, ne1, ne2), Bool)
            end
          | (Int, Mult, Int) ->
            begin
              (Binaire(MultInt, ne1, ne2), Int)
            end
          | (Rat, Mult, Rat) ->
            begin
              (Binaire(MultRat, ne1, ne2), Rat)
            end
          | (Int, Inf, Int) ->
            begin
              (Binaire(Inf, ne1, ne2), Bool)
            end
    | (TypeEnum(_, _), Equ,TypeEnum(_, _)) ->
            begin
    (*Les deux enums doivent etre compatibles*)
      if est_compatible t1 t2 then
        (Binaire(EquEnum, ne1, ne2), Bool)
      else
        raise (TypeBinaireInattendu(b, t1, t2))
            end
          | _ -> raise (TypeBinaireInattendu(b, t1, t2))
      end
  | AstTds.Affectable a -> let (na,t) = analyse_type_affectable a in (Affectable na, t)
  | AstTds.Null -> Null, Pointeur Undefined
  | AstTds.New t -> New t, Pointeur t
  | AstTds.Adresse info ->
    begin
      match info_ast_to_info info with
      | InfoVar (_, t, _, _) -> (Adresse info, Pointeur t)
      | _ -> failwith ("Internal error : symbol not found")
    end
  | AstTds.ExpressionEnum e -> 
    (*Trouver le type d'enum*)
    let typTrouve = (type_trouve_exprenum (AstTds.ExpressionEnum e) tpEnums) in
    (*Convertir l'enum en entier*)
    let intCorresp = exprenum_toint (AstTds.ExpressionEnum e) typTrouve in
    (ExpressionEnum (intCorresp), typTrouve )


  (* analyse_type_expression : typ list -> AstTds.instruction -> instruction *)
  (* Paramètre tpEnums : la liste des types des enums *)
  (* Paramètre i : l'instruction à analyser *)
  (* Vérifie la bonne utilisation des types*)
  (* renvoie une instruction analysée *)
  (* Erreur si types incompatibles *)
  let rec analyse_type_instruction tpEnums i =
    match i with
    | AstTds.Declaration(t, e, info) -> 
      begin
        let (ne, te) = analyse_type_expression tpEnums e in
        if est_compatible te t then
          begin 
            modifier_type_info t info;
            (Declaration(ne, info))
          end
        else raise (TypeInattendu(te, t))
      end
    | AstTds.Affectation(e, affectable) ->
      begin
        let (af, typaf) = analyse_type_affectable affectable in
        let (exp, typexp) = analyse_type_expression tpEnums e in
        if est_compatible typexp typaf then
          Affectation (exp, af)
        else
          raise (TypeInattendu(typexp, typaf))
      end
    | AstTds.Affichage(e) ->
      begin
        let (ne, te) = analyse_type_expression tpEnums e in
        match te with
        | Rat ->
          begin
            AffichageRat(ne)
          end
        | Int ->
          begin
            AffichageInt(ne)
          end
        | Bool ->
          begin
            AffichageBool(ne)
          end
        | _ -> failwith "Type non pris en charge."
      end
    | AstTds.Conditionnelle(c, b1, b2) ->
      begin
        let (nc, tc) = analyse_type_expression tpEnums c in
        if tc = Bool then
          begin
            let bt1 = List.map(analyse_type_instruction tpEnums) b1 in
            let bt2 = List.map(analyse_type_instruction tpEnums) b2 in
            Conditionnelle(nc, bt1, bt2)
          end
        else raise (TypeInattendu(tc, Bool))
      end
    | AstTds.TantQue(c, b) ->
      begin
        let (nc, tc) = analyse_type_expression tpEnums c in
        if tc = Bool then 
          begin
            let bt = List.map(analyse_type_instruction tpEnums) b in
            TantQue(nc, bt)
          end
        else raise (TypeInattendu(tc, Bool))
      end
    | AstTds.Empty ->
      begin
        Empty
      end
    | AstTds.Switch (expr, cl) ->
      (* Analyse de l'expression comparée *)
      let (nc, tc) = analyse_type_expression tpEnums expr in
      (* Analyse du bloc *)
      let ncl = analyse_type_listcase tpEnums tc cl  in
      (* Renvoie la nouvelle structure de la boucle *)
      Switch(nc, ncl)
      
  (* analyse_type_listcase : typ list -> typ -> AstTds.case list -> case list *)
  (* Paramètre tpEnums : la liste des types des enums *)
  (* Paramètre tc : le type de la cible du switch/case *)
  (* Paramètre cl : la liste des case du switch/case *)
  (* Vérifie la bonne utilisation des types *)
  (* renvoie une liste de case traites *)
  and analyse_type_listcase tpEnums tc cl  =
      List.map (analyse_type_case tpEnums tc) cl
        
  (* analyse_type_case : typ list -> typ -> AstTds.case -> case *)
  (* Paramètre tpEnums : la liste des types des enums *)
  (* Paramètre tc : le type de la cible du switch/case *)
  (* Paramètre case : le case du switch/case *)
  (* Vérifie la bonne utilisation des types *)
  (* renvoie un de case traite *)
  and analyse_type_case tpEnums tc case =
    match case with
    | AstTds.CaseTid(s, il, b) -> 
      begin
        let (ex,t) = (analyse_type_expression tpEnums (AstTds.ExpressionEnum(s))) in
          if est_compatible t tc then CaseTid(ex,List.map(analyse_type_instruction tpEnums) il, analyse_type_break b)
          else raise (TypeInattendu(t, tc))
      end
    | AstTds.CaseEntier(i, il, b) -> 
      begin
        if est_compatible tc Int then CaseEntier(i, List.map(analyse_type_instruction tpEnums) il, analyse_type_break b)
        else raise (TypeInattendu(Int, tc))
      end
    | AstTds.CaseTrue (il, b) -> 
      begin
        if est_compatible tc Bool then CaseTrue(List.map(analyse_type_instruction tpEnums) il, analyse_type_break b)
        else raise (TypeInattendu(Bool, tc))
      end
    | AstTds.CaseFalse (il, b) -> 
      begin
        if est_compatible tc Bool then CaseFalse(List.map(analyse_type_instruction tpEnums) il, analyse_type_break b)
        else raise (TypeInattendu(Bool, tc))
      end
    | AstTds.CaseDefault(il, b) -> 
      begin
        CaseDefault(List.map(analyse_type_instruction tpEnums) il, analyse_type_break b)
      end

  (* analyse_type_break : AstTds.break -> break *)
  (* Paramètre b : le break a analyser *)
  (* fait remonter le type de break dans les passes*)
  (* renvoie un break traite *)
  and analyse_type_break b =
    match b with
    | AstTds.Break -> Break
    | AstTds.Lambda -> Lambda

  (* analyse_type_fonction : typ list -> AstTds.fonction -> fonction *)
  (* Paramètre tpEnums : la liste des types des enums *)
  (* Paramètre AstTds.Fonction : la fonction a analyser *)
  (* Vérifie la bonne utilisation des types, s'assure que les parametres sont de bon type *)
  (* et que le return est du type annoncé *)
  (* renvoie une Fonction traitee *)
  (* Erreur si types incompatibles *)  
  let analyse_type_fonction tpEnums (AstTds.Fonction(t, _, infoseule, lp, li, e)) =
    let ltypeparam = List.map(fst) lp in
      modifier_type_fonction_info t ltypeparam infoseule;
      let lpt = List.map(fun (typeinfo, i) ->
      begin
        modifier_type_info typeinfo i;
        i
      end
      ) lp in
      let lit = List.map(analyse_type_instruction tpEnums) li in
      let (ne, te) = analyse_type_expression tpEnums e in
      if te = t then
        begin
          Fonction (infoseule, lpt, lit, ne)
        end
      else raise (TypeInattendu(te, t))

  (* analyser : t1 -> t2 *)
  (* Paramètre AstTds.Programme : le programme à analyser *)
  let analyser (AstTds.Programme(tpEnums,fonctions, prog)) =
    let ft= List.map (analyse_type_fonction tpEnums) fonctions in
    let pt = List.map (analyse_type_instruction tpEnums) prog in
    Programme (ft, pt)

end
