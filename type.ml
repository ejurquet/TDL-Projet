type typ = Bool | Int | Rat | Undefined | Pointeur of typ | TypeEnum of string * (string list)

let rec string_of_type t = 
  match t with
  | Bool ->  "Bool"
  | Int  ->  "Int"
  | Rat  ->  "Rat"
  | Pointeur (tp) -> "Pointeur (" ^ string_of_type tp ^ ")"
  | Undefined -> "Undefined"
  | TypeEnum (str,le) -> "Enum " ^ str ^ " : " ^ List.fold_right (fun t qt -> t ^ " " ^ qt) le ""

let rec est_compatible t1 t2 =
  match t1, t2 with
  | Bool, Bool -> true
  | Int, Int -> true
  | Rat, Rat -> true
  | Pointeur a, Pointeur b -> est_compatible a b
  |	TypeEnum (str1,_), TypeEnum (str2,_) -> str1 = str2
  | _ -> false 

let nom_complet_fonction n lp =
		let f_fold = (fun q t -> q ^ "$" ^(string_of_type t))
		in List.fold_left f_fold n lp

let est_compatible_list lt1 lt2 =
  try
    List.for_all2 est_compatible lt1 lt2
  with Invalid_argument _ -> false

let getTaille t =
  match t with
  | Int -> 1
  | Bool -> 1
  | Rat -> 2
  | Pointeur _ -> 1
  | TypeEnum _ -> 1
  | Undefined -> 0
  
