open Compilateur

(* Changer le chemin d'accès du jar. *)
let runtamcmde = "java -jar ../../runtam.jar"
(* let runtamcmde = "java -jar /mnt/n7fs/.../tools/runtam/runtam.jar" *)

(* Execute the TAM code obtained from the rat file and return the ouptut of this code *)
let runtamcode cmde ratfile =
  let tamcode = compiler ratfile in
  let (tamfile, chan) = Filename.open_temp_file "test" ".tam" in
  output_string chan tamcode;
  close_out chan;
  let ic = Unix.open_process_in (cmde ^ " " ^ tamfile) in
  let printed = input_line ic in
  close_in ic;
  Sys.remove tamfile;    (* à commenter si on veut étudier le code TAM. *)
  String.trim printed

(* Compile and run ratfile, then print its output *)
let runtam ratfile =
  print_string (runtamcode runtamcmde ratfile)

(* requires ppx_expect in jbuild, and `opam install ppx_expect` *)
let%expect_test "testprintint" =
  runtam "../../fichiersRat/src-rat-tam-test/testprintint.rat";
  [%expect{| 42 |}]

let%expect_test "testprintbool" =
  runtam "../../fichiersRat/src-rat-tam-test/testprintbool.rat";
  [%expect{| true |}]

let%expect_test "testprintrat" =
   runtam "../../fichiersRat/src-rat-tam-test/testprintrat.rat";
   [%expect{| [4/5] |}]

let%expect_test "testaddint" =
  runtam "../../fichiersRat/src-rat-tam-test/testaddint.rat";
  [%expect{| 42 |}]

let%expect_test "testaddrat" =
  runtam "../../fichiersRat/src-rat-tam-test/testaddrat.rat";
  [%expect{| [7/6] |}]

let%expect_test "testmultint" =
  runtam "../../fichiersRat/src-rat-tam-test/testmultint.rat";
  [%expect{| 440 |}]

let%expect_test "testmultrat" =
  runtam "../../fichiersRat/src-rat-tam-test/testmultrat.rat";
  [%expect{| [14/3] |}]

let%expect_test "testnum" =
  runtam "../../fichiersRat/src-rat-tam-test/testnum.rat";
  [%expect{| 4 |}]

let%expect_test "testdenom" =
  runtam "../../fichiersRat/src-rat-tam-test/testdenom.rat";
  [%expect{| 7 |}]

let%expect_test "testwhile1" =
  runtam "../../fichiersRat/src-rat-tam-test/testwhile1.rat";
  [%expect{| 19 |}]

let%expect_test "testif1" =
  runtam "../../fichiersRat/src-rat-tam-test/testif1.rat";
  [%expect{| 18 |}]

let%expect_test "testif2" =
  runtam "../../fichiersRat/src-rat-tam-test/testif2.rat";
  [%expect{| 21 |}]

let%expect_test "factiter" =
  runtam "../../fichiersRat/src-rat-tam-test/factiter.rat";
  [%expect{| 120 |}]

let%expect_test "complique" =
  runtam "../../fichiersRat/src-rat-tam-test/complique.rat";
  [%expect{| [9/4][27/14][27/16][3/2] |}]

let%expect_test "factfun1" =
  runtam "../../fichiersRat/src-rat-tam-test/testfun1.rat";
  [%expect{| 1 |}]

let%expect_test "factfun2" =
  runtam "../../fichiersRat/src-rat-tam-test/testfun2.rat";
  [%expect{| 7 |}]

let%expect_test "factfun3" =
  runtam "../../fichiersRat/src-rat-tam-test/testfun3.rat";
  [%expect{| 10 |}]

let%expect_test "factfun4" =
  runtam "../../fichiersRat/src-rat-tam-test/testfun4.rat";
  [%expect{| 10 |}]

let%expect_test "factfuns" =
  runtam "../../fichiersRat/src-rat-tam-test/testfuns.rat";
  [%expect{| 28 |}]

let%expect_test "factrec" =
  runtam "../../fichiersRat/src-rat-tam-test/factrec.rat";
  [%expect{| 120 |}]

let%expect_test "pointeur_0" =
  runtam "../../fichiersRat/src-rat-pointeur-test/test_pointeur_0.rat";
  [%expect{| 3 |}]

let%expect_test "pointeur_2" =
  runtam "../../fichiersRat/src-rat-pointeur-test/test_pointeur_2.rat";
  [%expect{| 183 |}]

let%expect_test "pointeur_adresse_rat" =
  runtam "../../fichiersRat/src-rat-pointeur-test/test_pointeur_adresse_rat.rat";
  [%expect{| [3/4] |}]

let%expect_test "pointeur_fonction" =
  runtam "../../fichiersRat/src-rat-pointeur-test/test_pointeur_fonction.rat";
  [%expect{| 650 |}]

let%expect_test "pointeur_pointeur_rat" =
  runtam "../../fichiersRat/src-rat-pointeur-test/test_pointeur_pointeur_rat.rat";
  [%expect{| [3/4] |}]

let%expect_test "pointeur_rat" =
  runtam "../../fichiersRat/src-rat-pointeur-test/test_pointeur_rat.rat";
  [%expect{| [3/4] |}]

let%expect_test "pointeur_beaucoup" =
  runtam "../../fichiersRat/src-rat-pointeur-test/test_pointeur_beaucoup.rat";
  [%expect{| 33333 |}]

let%expect_test "surcharge_0" =
  runtam "../../fichiersRat/src-rat-surcharge-test/test_surcharge_0.rat";
  [%expect{| 12 |}]

let%expect_test "surcharge_rec" =
  runtam "../../fichiersRat/src-rat-surcharge-test/test_surcharge_rec.rat";
  [%expect{| 1202 |}]

let%expect_test "surcharge_vide" =
  runtam "../../fichiersRat/src-rat-surcharge-test/test_surcharge_vide.rat";
  [%expect{| 13 |}]

let%expect_test "surcharge_beaucoup" =
  runtam "../../fichiersRat/src-rat-surcharge-test/test_surcharge_beaucoup.rat";
  [%expect{| 1234567 |}]

let%expect_test "enum_0" =
  runtam "../../fichiersRat/src-rat-enum-test/test_enum_0.rat";
  [%expect{| falsetrue |}]

let%expect_test "enum_pointeur" =
  runtam "../../fichiersRat/src-rat-enum-test/test_enum_pointeur.rat";
  [%expect{| truetrue |}]

let%expect_test "switch_enum" =
  runtam "../../fichiersRat/src-rat-switch-test/test_switch_enum.rat";
  [%expect{| 19 |}]

let%expect_test "switch_exemple1" =
  runtam "../../fichiersRat/src-rat-switch-test/test_switch_exemple1.rat";
  [%expect{| 0434 |}]

let%expect_test "switch_exemple2" =
  runtam "../../fichiersRat/src-rat-switch-test/test_switch_exemple2.rat";
  [%expect{| 427878372096 |}]

let%expect_test "switch_exemple3" =
  runtam "../../fichiersRat/src-rat-switch-test/test_switch_exemple3.rat";
  [%expect{| 049988434234 |}]

let%expect_test "switch_exemple4" =
  runtam "../../fichiersRat/src-rat-switch-test/test_switch_exemple4.rat";
  [%expect{| 4278783209653 |}]

let%expect_test "switch_expression-complexe" =
  runtam "../../fichiersRat/src-rat-switch-test/test_switch_expression-complexe.rat";
  [%expect{| 427878372096 |}]

let%expect_test "combi_sujet" =
  runtam "../../fichiersRat/src-rat-combinaison-test/test_combi_sujet.rat";
  [%expect{| [15/1][8/12][8/1][15/1][8/1][15/2] |}]
  