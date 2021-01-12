(* Types manipulés dans Rat *)
type typ = Bool | Int | Rat | Undefined | Pointeur of typ | TypeEnum of string * (string list)

(* string_of_type :  typ -> string *)
(* transforme un typ en chaîne de caractère *)
val string_of_type : typ -> string  

(* est_compatible : typ -> typ -> bool *)
(* vérifie que le second type est compatible avec le premier *)
(* c'est à dire qu'un élèment du second type peut être affecté *)
(* à un élément du premier type *)
val est_compatible : typ -> typ -> bool

(* nom_complet_fonction :  string -> (typ * 'a) list -> string *)
(* génère un nom complet pour une fonction incluant les types de ses arguments *)
val nom_complet_fonction : string -> typ list -> string

(* est_compatible_list : typ list -> typ list -> bool *)
(* vérifie si les types sont compatibles deux à deux *)
val est_compatible_list : typ list -> typ list -> bool

(* getTaille : typ -> int *)
(* Renvoie la taille en mémoire qui doit prendre une variable en fonction de son type *)
val getTaille : typ -> int 

