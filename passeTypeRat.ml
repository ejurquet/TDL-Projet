(* Module de la passe de typage *)

module PasseTypeRat : Passe.Passe with type t1 = Ast.AstTds.programme and type t2 = Ast.AstType.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstType

  type t1 = AstTds.programme
  type t2 = AstType.programme

  let rec analyse_type_expression e =
    match e with
      | AstTds.AppelFonction(info, le) ->
          begin
            match info_ast_to_info info with
              | InfoFun(_, typeRet, typeParams) ->
                let nlet = List.map(fun ei -> analyse_type_expression ei) le in
                let nle = List.map(fst) nlet in
                let ltype = List.map(snd) nlet in
                if ltype = typeParams then (AppelFonction (info, nle), typeRet)
                else raise (TypesParametresInattendus(typeParams, ltype))
              | _ -> failwith "Erreur interne."
          end
      | AstTds.Rationnel(e1,e2) ->
          begin
            let (ne1, t1) = analyse_type_expression e1 in
            let (ne2, t2) = analyse_type_expression e2 in
            if t1 = Int then 
              if t2 = t1 then
                (Rationnel(ne1, ne2), Rat)
              else
                raise (TypeInattendu(t1, t2))
            else
              raise (TypeInattendu(t1, t2))
          end
      | AstTds.Numerateur(e1) ->
          begin
            let (ne1, t1) = analyse_type_expression e1 in
            if t1 = Rat then
              (Numerateur ne1, Int)
            else 
              raise (TypeInattendu(t1, t1))
          end
      | AstTds.Denominateur(e1) ->
          begin
            let (ne1, t1) = analyse_type_expression e1 in
            if t1 = Rat then
              (Denominateur ne1, Int)
            else 
              raise (TypeInattendu(t1, t1))
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
            let (ne1, t1) = analyse_type_expression e1 in
            let (ne2, t2) = analyse_type_expression e2 in
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
              | (Int, AstSyntax.Inf, Int) ->
                begin
                  (Binaire(Inf, ne1, ne2), Bool)
                end
              | _ -> raise (TypeBinaireInattendu(b, t1, t2))
          end

  
  let rec analyse_type_instruction i =
    match i with 
      | AstTds.Declaration(t,e,info) -> 
        begin
          let (ne, te) = analyse_type_expression e in
          if te = t then 
          modifier_type_info t info;
          (Declaration(ne, info))
          else raise (TypeInnatendu(t, te))
        end
      | AstTds.Affectation(e, info) ->
        begin
          let (ne, te) = analyse_type_expression e in
          match info_ast_to_info info with
            | InfoVar(_, t, _, _) -> 
              begin
                if t = te then (Affectation(ne, info)) 
                else raise (TypeInnatendu(t, te))
              end
            | _ -> failwith "Erreur interne."
        end
      | AstTds.Affichage(e) ->
        begin
          let (ne, te) = analyse_type_expression e in
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
        end
      | AstTds.Conditionnelle(c,b1,b2) ->
        begin
          let (nc, tc) = analyse_type_expression c in
          (** TODO **)
        end
      | AstTds.TantQue(c,b) ->
        begin
          let (nc, tc) = analyse_type_expression c in
          if tc = Bool then 
            let bt = List.map(analyse_type_instruction) b in
            (** TODO **)
          else raise (TypeInnatendu(tc,))
        end
      | AstTds.Empty() ->
        begin
          Empty
        end
  

  let analyse_type_fonction (AstTds.Fonction(t,info,lp,li,e))  = ...
    (** TODO **)

  let analyser (AstTds.Programme (fonctions, prog)) = ...
    (** TODO **)

end
