(* Module de la passe de gestion des identifiants *)
module PasseTdsRat : Passe.Passe with type t1 = Ast.AstSyntax.programme and type t2 = Ast.AstTds.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstTds
  open Type

  type t1 = Ast.AstSyntax.programme
  type t2 = Ast.AstTds.programme

(* analyse_tds_expression : *)
let rec analyse_tds_affectable tds (a:AstSyntax.affectable) modif =
  match a with
  | AstSyntax.Valeur af -> Valeur (analyse_tds_affectable tds af modif)
  | AstSyntax.Ident n ->
    begin
      match (chercherGlobalement tds n) with
      | None -> raise (IdentifiantNonDeclare n)
      | Some info ->
        begin
          match (info_ast_to_info info) with
          | InfoVar _ -> Ident info
          | InfoConst _ -> if modif then 
                                raise (MauvaiseUtilisationIdentifiant n)
                              else 
                                Ident info
          |  _ -> raise (MauvaiseUtilisationIdentifiant n)
        end
    end 

(* analyse_tds_expression : AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_expression tds e =
    match e with
    |AstSyntax.AppelFonction (id,le) ->
        begin
          match chercherGlobalement tds id with
          | None ->
              raise (IdentifiantNonDeclare id)
          | Some info ->
          begin
            (* Printf.printf "%s\n" (string_of_info (info_ast_to_info info)) ;*)
            match info_ast_to_info info with
            | InfoFunSurcharges(_) ->  
              let leTraite = (List.map (analyse_tds_expression tds) le) in
              AppelFonction(info,leTraite)
            | _ ->
              (* Modification d'une constante ou d'une fonction *)  
              raise (MauvaiseUtilisationIdentifiant id)
          end
        end
  |AstSyntax.Ident (n) ->
    begin
    match chercherGlobalement tds n with
        | None ->
            raise (IdentifiantNonDeclare n)
        | Some info ->
        begin
            match info_ast_to_info info with
            | InfoVar _ ->  
                Ident(info)
            | InfoConst (_,v) ->  
                Entier(v)
            |  _ ->
              (* Modification d'une constante ou d'une fonction *)  
              raise (MauvaiseUtilisationIdentifiant n) 
        end
            
    end
  |AstSyntax.Rationnel (e1,e2) -> 
    Rationnel(analyse_tds_expression tds e1 , analyse_tds_expression tds e2)
  |AstSyntax.Numerateur (e1) -> 
    Numerateur(analyse_tds_expression tds e1)
  |AstSyntax.Denominateur (e1) ->
    Denominateur(analyse_tds_expression tds e1)
  |AstSyntax.True -> 
    True
  |AstSyntax.False ->
    False
  |AstSyntax.Entier (e1) ->
    Entier(e1)
  |AstSyntax.Binaire (b,e1,e2) ->
    Binaire(b,analyse_tds_expression tds e1 , analyse_tds_expression tds e2)
  |AstSyntax.Affectable af ->
    Affectable (analyse_tds_affectable tds af false)
  |AstSyntax.Null ->
    Null
  |AstSyntax.New t ->
    New t
  |AstSyntax.Adresse n ->
    begin
      match (chercherGlobalement tds n) with
      | None -> raise (IdentifiantNonDeclare n)
      | Some info ->
        begin
          match info_ast_to_info info with
          | InfoVar _ -> Adresse info
          | _ -> raise (MauvaiseUtilisationIdentifiant n)
        end
    end
  | AstSyntax.ExpressionEnum _ -> Null (* TODO *)


(* analyse_tds_instruction : AstSyntax.instruction -> tds -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds i =
  match i with
  | AstSyntax.Declaration (t, n, e) ->
      begin
        match chercherLocalement tds n with
        | None ->
            (* L'identifiant n'est pas trouvé dans la tds locale, 
            il n'a donc pas été déclaré dans le bloc courant *)
            (* Vérification de la bonne utilisation des identifiants dans l'expression *)
            (* et obtention de l'expression transformée *) 
            let ne = analyse_tds_expression tds e in
            (* Création de l'information associée à l'identfiant *)
            let info = InfoVar (n,Undefined, 0, "") in
            (* Création du pointeur sur l'information *)
            let ia = info_to_info_ast info in
            (* Ajout de l'information (pointeur) dans la tds *)
            ajouter tds n ia;
            (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information 
            et l'expression remplacée par l'expression issue de l'analyse *)
            Declaration (t, ne, ia) 
        | Some _ ->
            (* L'identifiant est trouvé dans la tds locale, 
            il a donc déjà été déclaré dans le bloc courant *) 
            raise (DoubleDeclaration n)
      end
  | AstSyntax.Affectation (n,e) ->
      begin
        Affectation (analyse_tds_expression tds e, analyse_tds_affectable tds n true)
      end
  | AstSyntax.Constante (n,v) -> 
      begin
        match chercherLocalement tds n with
        | None -> 
        (* L'identifiant n'est pas trouvé dans la tds locale, 
        il n'a donc pas été déclaré dans le bloc courant *)
        (* Ajout dans la tds de la constante *)
        ajouter tds n (info_to_info_ast (InfoConst (n,v))); 
        (* Suppression du noeud de déclaration des constantes devenu inutile *)
        Empty
        | Some _ ->
          (* L'identifiant est trouvé dans la tds locale, 
          il a donc déjà été déclaré dans le bloc courant *) 
          raise (DoubleDeclaration n)
      end
  | AstSyntax.Affichage e -> 
      (* Vérification de la bonne utilisation des identifiants dans l'expression *)
      (* et obtention de l'expression transformée *)
      let ne = analyse_tds_expression tds e in
      (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
      Affichage (ne)
  | AstSyntax.Conditionnelle (c,t,e) -> 
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc then *)
      let tast = analyse_tds_bloc tds t in
      (* Analyse du bloc else *)
      let east = analyse_tds_bloc tds e in
      (* Renvoie la nouvelle structure de la conditionnelle *)
      Conditionnelle (nc, tast, east)
  | AstSyntax.TantQue (c,b) -> 
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc *)
      let bast = analyse_tds_bloc tds b in
      (* Renvoie la nouvelle structure de la boucle *)
      TantQue (nc, bast)

      
(* analyse_tds_bloc : AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds li =
  (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale 
  pointant sur la table du bloc parent *)
  let tdsbloc = creerTDSFille tds in
  (* Analyse des instructions du bloc avec la tds du nouveau bloc 
  Cette tds est modifiée par effet de bord *)
   let nli = List.map (analyse_tds_instruction tdsbloc) li in
   (* afficher_locale tdsbloc ; *) (* décommenter pour afficher la table locale *)
   nli


   let ajouterIdTDS tds n = 
    match chercherLocalement tds n with
        | None ->
          begin
            (* L'identifiant n'est pas trouvé dans la tds locale, 
            il n'a donc pas été déclaré dans le bloc courant *)
            (* Création de l'information associée à l'identfiant *)
            let info = InfoVar (n,Undefined, 0, "") in
            (* Création du pointeur sur l'information *)
            let ia = info_to_info_ast info in
            (* Ajout de l'information (pointeur) dans la tds *)
            ajouter tds n ia;
            (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information 
            et l'expression remplacée par l'expression issue de l'analyse *)
            ia
          end
        | Some _ ->
            (* L'identifiant est trouvé dans la tds locale, 
            il a donc déjà été déclaré dans le bloc courant *) 
            raise (DoubleDeclaration n)




(* analyse_tds_fonction : AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
(*FROM type fonction = Fonction of typ * string * (typ * string) list * instruction list * expression*)
(*TO   type fonction = Fonction of typ * Tds.info_ast * (typ * Tds.info_ast ) list * instruction list * expression *)



let analyse_tds_fonction maintds (AstSyntax.Fonction(t,n,lp,li,e)) =
    match chercherGlobalement maintds n with
        | None ->
          begin
            let listType = List.map (fst) lp
            in let info = InfoFun(n, t, listType)
			      in let infosur = InfoFunSurcharges ([info])
            in let ia = info_to_info_ast infosur
			      in let iaSeule = info_to_info_ast info
            in ajouter maintds n ia;
            let tdsParam = creerTDSFille maintds
            in let lptraite = (List.map (fun (typ,nom) -> (typ, ajouterIdTDS tdsParam nom)) lp)
            in let tdsBloc = creerTDSFille tdsParam
            in let litraite = (List.map (analyse_tds_instruction tdsBloc) li)
            in let etraite = analyse_tds_expression tdsBloc e
            in Fonction(t,ia,iaSeule,lptraite,litraite,etraite)
          end
        | Some info ->
			    begin
				    match info_ast_to_info info with
					  | InfoFunSurcharges lf ->
						(*Le nom existe dans la tds*)
						  begin
                let listType = List.map (fst) lp
                in if List.exists (fun i -> 
                  begin
                    match i with
                    | InfoFun (_,_,listTypei) -> est_compatible_list listTypei listType
                    | _ -> failwith "Erreur interne"
                  end
                ) lf then
                  (*La signature est deja presente*)
                  raise (DoubleDeclaration n)
                else
                  let info_f = InfoFun(n, t, listType) in
                  let iaSeule = info_to_info_ast info_f in
                  ajouter_signature_info info_f info; 
                  let tdsParam = creerTDSFille maintds in 
                  let lptraite = (List.map (fun (typ,nom) -> (typ, ajouterIdTDS tdsParam nom)) lp) in
                  let tdsBloc = creerTDSFille tdsParam in
                  let litraite = (List.map (analyse_tds_instruction tdsBloc) li) in
                  let etraite = analyse_tds_expression tdsBloc e in
                  Fonction(t,info,iaSeule,lptraite,litraite,etraite)
						  end
					  | _ -> raise (MauvaiseUtilisationIdentifiant n)
				
			end


(* analyser : AstSyntax.ast -> AstTds.ast *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (typenums,fonctions,prog)) =
  let tds = creerTDSMere () in
  let nf = List.map (analyse_tds_fonction tds) fonctions in
  let nb = analyse_tds_bloc tds prog in
  Programme (nf,nb)

end
