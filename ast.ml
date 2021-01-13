open Type

(* Interface des arbres abstraits *)
module type Ast =
sig
   type expression
   type instruction
   type fonction
   type programme
end

(* Interface d'affichage des arbres abstraits *)
module type PrinterAst =
sig
  module A:Ast

  (* string_of_expression :  expression -> string *)
  (* transforme une expression en chaîne de caractère *)
  val string_of_expression : A.expression -> string

  (* string_of_instruction :  instruction -> string *)
  (* transforme une instruction en chaîne de caractère *)
  val string_of_instruction : A.instruction -> string

  (* string_of_fonction :  fonction -> string *)
  (* transforme une fonction en chaîne de caractère *)
  val string_of_fonction : A.fonction -> string

  (* string_of_ast :  ast -> string *)
  (* transforme un ast en chaîne de caractère *)
  val string_of_programme : A.programme -> string

  (* print_ast :  ast -> unit *)
  (* affiche un ast *)
  val print_programme : A.programme -> unit

end


(* *************************************** *)
(* AST après la phase d'analyse syntaxique *)
(* *************************************** *)
module AstSyntax =
struct

  (* Opérateurs binaires de Rat *)
  type binaire = Plus | Mult | Equ | Inf

  type affectable = Ident of string | Valeur of affectable

  type break = Break | Lambda
  	
  (* Expressions de Rat *)
  type expression =
    (* Appel de fonction représenté par le nom de la fonction et la liste des paramètres réels *)
    | AppelFonction of string * expression list 
    (* Rationnel représenté par le numérateur et le dénominateur *)
    | Rationnel of expression * expression 
    (* Accès au numérateur d'un rationnel *)
    | Numerateur of expression
    (* Accès au dénominateur d'un rationnel *)
    | Denominateur of expression
    (* Accès à un identifiant représenté par son nom *)
    | Ident of string
    (* Booléen vrai *)
    | True
    (* Booléen faux *)
    | False
    (* Entier *)
    | Entier of int
    (* Opération binaire représentée par l'opérateur, l'opérande gauche et l'opérande droite *)
    | Binaire of binaire * expression * expression
    (* Affectable *)
    | Affectable of affectable
    (* Null *)
    | Null
    (* New *)
    | New of typ
    (* & *)
    | Adresse of string
	| ExpressionEnum of string

  (* Instructions de Rat *)
  type bloc = instruction list
  and instruction =
    (* Déclaration de variable représentée par son type, son nom et l'expression d'initialisation *)
    | Declaration of typ * string * expression
    (* Affectation d'une variable représentée par son nom et la nouvelle valeur affectée *)
    | Affectation of affectable * expression
    (* Déclaration d'une constante représentée par son nom et sa valeur (entier) *)
    | Constante of string * int
    (* Affichage d'une expression *)
    | Affichage of expression
    (* Conditionnelle représentée par la condition, le bloc then et le bloc else *)
    | Conditionnelle of expression * bloc * bloc
    (*Boucle TantQue représentée par la conditin d'arrêt de la boucle et le bloc d'instructions *)
    | TantQue of expression * bloc
	  | Switch of expression * (case list)

  and case = CaseTid of string * instruction list * break | CaseEntier of int * instruction list * break | CaseTrue of instruction list * break | CaseFalse of instruction list * break | CaseDefault of instruction list * break


  (* Structure des fonctions de Rat *)
  (* type de retour - nom - liste des paramètres (association type et nom) - corps de la fonction - expression de retour *)
  type fonction = Fonction of typ * string * (typ * string) list * instruction list * expression

  (* Structure d'un programme Rat *)
  (* liste de fonction - programme principal *)
  type programme = Programme of typ list *  fonction list * bloc
  
end


(*Module d'affiche des AST issus de la phase d'analyse syntaxique *)
module PrinterAstSyntax : PrinterAst with module A = AstSyntax =
struct

  module A = AstSyntax
  open A

  (* Conversion des opérateurs binaires *)
  let string_of_binaire b =
    match b with
    | Plus -> "+ "
    | Mult -> "* "
    | Equ -> "= "
    | Inf -> "< "

  let rec string_of_affectable a =
    match a with
    | Valeur af -> "Affectable valeur " ^ (string_of_affectable af)
    | Ident s1 ->  "Affectable ident " ^ s1

  (* Conversion des expressions *)
  let rec string_of_expression e =
    match e with
    | AppelFonction (n,le) -> "call "^n^"("^((List.fold_right (fun i tq -> (string_of_expression i)^tq) le ""))^") "
    | Rationnel (e1,e2) -> "["^(string_of_expression e1)^"/"^(string_of_expression e2)^"] "
    | Numerateur e1 -> "num "^(string_of_expression e1)^" "
    | Denominateur e1 ->  "denom "^(string_of_expression e1)^" "
    | Ident n -> n^" "
    | True -> "true "
    | False -> "false "
    | Entier i -> (string_of_int i)^" "
    | Binaire (b,e1,e2) -> (string_of_expression e1)^(string_of_binaire b)^(string_of_expression e2)^" "
    | Null -> "null"
    | Affectable a1 -> string_of_affectable a1 
    | New typ -> "(new " ^ (string_of_type typ) ^")"
    | Adresse id -> "& " ^ id
    | ExpressionEnum n -> "enum " ^ n

  (* Conversion des instructions *)
  let rec string_of_instruction i =
    match i with
    | Declaration (t, n, e) -> "Declaration  : "^(string_of_type t)^" "^n^" = "^(string_of_expression e) ^ "\n"
    | Affectation (n,e) ->  "Affectation  : "^(string_of_affectable n)^" = "^(string_of_expression e) ^ "\n"
    | Constante (n,i) ->  "Constante  : "^n^" = "^(string_of_int i)^"\n"
    | Affichage e ->  "Affichage  : "^(string_of_expression e)^"\n"
    | Conditionnelle (c,t,e) ->  "Conditionnelle  : IF "^(string_of_expression c) ^ "\n" ^
                                  "THEN \n"^((List.fold_right (fun i tq -> (string_of_instruction i) ^ tq) t "")) ^
                                  "ELSE \n"^((List.fold_right (fun i tq -> (string_of_instruction i) ^ tq) e "")) ^ "\n"
    | TantQue (c,b) -> "TantQue  : TQ "^(string_of_expression c)^"\n"^
                                  "FAIRE \n"^((List.fold_right (fun i tq -> (string_of_instruction i)^tq) b "")) ^ "\n"
    | Switch (e,_) -> "Switch : " ^ (string_of_expression e)

  (* Conversion des fonctions *)
  let string_of_fonction (Fonction(t,n,lp,li,e)) = (string_of_type t)^" "^n^" ("^((List.fold_right (fun (t,n) tq -> (string_of_type t)^" "^n^" "^tq) lp ""))^") = \n"^
                                        ((List.fold_right (fun i tq -> (string_of_instruction i)^tq) li ""))^
                                        "Return "^(string_of_expression e)^"\n"

  (* Conversion d'un programme Rat *)
  let string_of_programme (Programme (enums, fonctions, instruction)) =
    (List.fold_right (fun f tq -> (string_of_type f)^tq) enums "") ^
    (List.fold_right (fun f tq -> (string_of_fonction f)^tq) fonctions "") ^
    (List.fold_right (fun i tq -> (string_of_instruction i)^tq) instruction "")

  (* Affichage d'un programme Rat *)
  let print_programme programme =
    print_string "AST : \n";
    print_string (string_of_programme programme);
    flush_all ()

end

(* ********************************************* *)
(* AST après la phase d'analyse des identifiants *)
(* ********************************************* *)
module AstTds =
struct

  type affectable = Ident of Tds.info_ast | Valeur of affectable
  
  type break = Break | Lambda

  (* Expressions existantes dans notre langage *)
  (* ~ expression de l'AST syntaxique où les noms des identifiants ont été 
  remplacés par les informations associées aux identificateurs *)
  type expression =
    | AppelFonction of Tds.info_ast * expression list
    | Rationnel of expression * expression
    | Numerateur of expression
    | Denominateur of expression
    | Ident of Tds.info_ast (* le nom de l'identifiant est remplacé par ses informations *)
    | True
    | False
    | Entier of int
    | Binaire of AstSyntax.binaire * expression * expression
    | Null
    | Affectable of affectable
    | New of typ
    | Adresse of Tds.info_ast
	| ExpressionEnum of string

  (* instructions existantes dans notre langage *)
  (* ~ instruction de l'AST syntaxique où les noms des identifiants ont été 
  remplacés par les informations associées aux identificateurs 
  + suppression de nœuds (const) *)
  type bloc = instruction list
  and instruction =
    | Declaration of typ * expression * Tds.info_ast (* le nom de l'identifiant est remplacé par ses informations *)
    | Affectation of expression * affectable (* le nom de l'identifiant est remplacé par ses informations *)
    | Affichage of expression
    | Conditionnelle of expression * bloc * bloc
    | TantQue of expression * bloc
    | Empty (* les nœuds ayant disparus: Const *)
    | Switch of expression * (case list)
  
  and case = CaseTid of string * instruction list * break | CaseEntier of int * instruction list * break | CaseTrue of instruction list * break | CaseFalse of instruction list * break | CaseDefault of instruction list * break

  (* Structure des fonctions dans notre langage *)
  (* type de retour - informations associées à l'identificateur (dont son nom) - liste des paramètres (association type et information sur les paramètres) - corps de la fonction - expression de retour *)
  type fonction = Fonction of typ * Tds.info_ast* Tds.info_ast* (typ * Tds.info_ast ) list * instruction list * expression 

  (* Structure d'un programme dans notre langage *)
  type programme = Programme of typ list * fonction list * bloc

end
    

(* ******************************* *)
(* AST après la phase de typage *)
(* ******************************* *)
module AstType =
struct

  type affectable = Ident of Tds.info_ast | Valeur of affectable

  (* Opérateurs binaires existants dans Rat - résolution de la surcharge *)
  type binaire = PlusInt | PlusRat | MultInt | MultRat | EquInt | EquBool | Inf | EquEnum

  type break = Break | Lambda

  (* Expressions existantes dans Rat *)
  (* = expression de AstTds *)
  type expression =
    | AppelFonction of Tds.info_ast * expression list
    | Rationnel of expression * expression
    | Numerateur of expression
    | Denominateur of expression
    | Ident of Tds.info_ast
    | True
    | False
    | Entier of int
    | Binaire of binaire * expression * expression
    | Null
    | Affectable of affectable
    | New of typ
    | Adresse of Tds.info_ast
    | ExpressionEnum of int

  (* instructions existantes Rat *)
  (* = instruction de AstTds + informations associées aux identificateurs, mises à jour *)
  (* + résolution de la surcharge de l'affichage *)
  type bloc = instruction list
  and instruction =
    | Declaration of expression * Tds.info_ast
    | Affectation of expression * affectable
    | AffichageInt of expression
    | AffichageRat of expression
    | AffichageBool of expression
    | Conditionnelle of expression * bloc * bloc
    | TantQue of expression * bloc
    | Empty (* les nœuds ayant disparus: Const *)
    | Switch of expression * (case list)

  and case = CaseTid of expression * instruction list * break | CaseEntier of int * instruction list * break | CaseTrue of instruction list * break | CaseFalse of instruction list * break | CaseDefault of instruction list * break


  (* informations associées à l'identificateur (dont son nom), liste des paramètres, corps, expression de retour *)
  type fonction = Fonction of Tds.info_ast * Tds.info_ast list * instruction list * expression 

  (* Structure d'un programme dans notre langage *)
  type programme = Programme of fonction list * bloc

  let taille_variables_declarees i = 
    match i with
    | Declaration (_,info) -> 
      begin
      match Tds.info_ast_to_info info with
      | InfoVar (_,t,_,_) -> getTaille t
      | _ -> failwith "internal error"
      end
    | _ -> 0 ;;

end

(* ******************************* *)
(* AST après la phase de placement *)
(* ******************************* *)
module AstPlacement =
struct

  (* Expressions existantes dans notre langage *)
  (* = expression de AstType  *)
  type expression = AstType.expression

  (* instructions existantes dans notre langage *)
  (* = instructions de AstType  *)
  type bloc = instruction list
  and instruction = AstType.instruction

  (* informations associées à l'identificateur (dont son nom), liste de paramètres, corps, expression de retour *)
  (* Plus besoin de la liste des paramètres mais on la garde pour les tests du placements mémoire *)
  type fonction = Fonction of Tds.info_ast * Tds.info_ast list * instruction list * expression

  (* Structure d'un programme dans notre langage *)
  type programme = Programme of fonction list * bloc

end


