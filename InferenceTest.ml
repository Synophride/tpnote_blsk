open Other
open SimpleTypes


module Test_exo1 = struct
  open Exo1.BaseTypeChecker
  open BaseAST
     
  let f_test () =        
    let evt = Env.empty in 
    let e1 = Int(623) in
    (* (x -> x)(3) *) 
    let e2 = App(Fun("x", TInt, Var("x")), Int(3)) in
    let e3 = Pair(
                 App(
                     Fun("x",
                         TBool,
                         Let("y",
                             Var("x"),
                             Var("y"))),
                     Bool(true)),
                 Int(123)) in  
    let f_e1 = App(
                   Fun("x",
                       TBool,
                       App(Var("x"),
                           Var("x"))),
                   Int(3)) in
    let liste_exp_correctes = [e1; e2; e3] in
    let liste_types = List.map (fun exp -> type_expression evt exp) liste_exp_correctes in
    List.iter2 (fun exp t ->
        let str_rendue = (str_expression exp) ^ "\n\n" ^ (str_of_type t) ^ "\n~~~~~~\n\n" in
        print_string str_rendue;)
      liste_exp_correctes
      liste_types;
    
    try
      let t_er = type_expression evt f_e1 in 
      assert(false)
    with Bad_type(s) -> print_string s
                      
end;;

module Test_exo2 = struct 
  open BaseTypeReconstruction
  open RawAST
     
  let rec (str_expression : expression -> string) =
    function
    | Int(i) -> string_of_int i
    | Bool(b) -> string_of_bool b
    | Unit -> "()"
    | Var(str) -> str
    | App(e1, e2) -> "( " ^ str_expression e1 ^ " ) ( " ^ str_expression e2 ^ " )"
    | Fun(str, e) -> "fun (" ^ str ^ ") -> " ^ str_expression e
    | Let(str, e1, e2) -> "let " ^ str ^ " = " ^ str_expression e1 ^ " in \n" ^ str_expression e2
    | Op(str) -> str
    | Pair(e1, e2) -> "(" ^ str_expression e1 ^ ", " ^ str_expression e2 ^ " )"
    | Newref(exp) -> str_expression exp ^ " ref"
    | Sequence(e1, e2) -> str_expression e1 ^ ";\n" ^ str_expression e2
    | If(eb, e1, e2) -> "if( " ^ str_expression eb
                        ^ " )\nthen " ^ str_expression e1
                        ^ "\nelse " ^ str_expression e2
    | While(eb, e)
      -> "While ( " ^ str_expression eb ^ " ) do \n " ^ str_expression e ^ " \n end \n"
  ;;
  let f_test ()= 
    let environnement = Env.empty in              
    let i = Int(214) in
    let j = Int(1) in 
    let id = Fun("x", Var("x")) in
    let apply_id = App(id, i) in
    let b = Bool(true) in
    let cond = If(b, i, j) in
    let pair = Pair(j, b) in
    let pair2 = Pair(id, App(id, j)) in
    let doubleapply = Let("f",
                 id,
                 Pair(
                     App(Var("f"), i),
                     App(Var("f"), j)))
    in
    
    let l = [i;j;id;apply_id; b; cond; pair; pair2; doubleapply] in 
    let l_types = List.map (fun exp -> type_expression environnement exp) l in
    let _ = List.iter2
              (fun expression type_
               -> let str_exp = str_expression expression in
                  let str_t = str_of_type type_ in
                  let str_rendue = ("\n" ^ str_exp ^ "\n____\n" ^ str_t ^ "\n~~~~~\n\n") in
                  print_string str_rendue)
              l
              l_types
    in
    let _ = print_string "\n Fin des tests des types qui fonctionnent\n" in
    let e1 = App(i, j) in
    let e2 = Fun("x", App(Var("x"), Var("x"))) in
    let e3 = Let("f", id, Pair(App(Var("f"), b), App(Var("f"), j))) in
    let lm = [e1; e2; e3] in
    let _ = List.iter
      (fun e ->
        let _ = print_string ((str_expression e) ^
                                "\n______\n" )  in 
        let _ = try
            let _ = type_expression environnement e in
            assert(false) 
          with Bad_type(str) -> print_string (str ^ "\n")
        in
        print_string ("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n")
      )
      lm
          
    in ()
end ;;






module Test_exo2bonus = struct 
  open Exo2.PTypeChecker
  open RawAST
  
  let f_test ()= 
    let environnement = Env.empty in
    
    let i = Int(214) in
    let j = Int(1) in 
    let id = Fun("x", Var("x")) in
    let apply_id = App(id, i) in
    let b = Bool(true) in
    let cond = If(b, i, j) in
    let pair = Pair(j, b) in
    let pair2 = Pair(id, App(id, j)) in
    let doubleapply = Let("f",
                 id,
                 Pair(
                     App(Var("f"), i),
                     App(Var("f"), j))) in 
    let e3 = Let("f", id, Pair(App(Var("f"), b), App(Var("f"), j))) in
    let l = [i;j;id;apply_id; b; cond; pair; pair2; doubleapply; e3]  in  
    let l_types = List.map (fun exp -> type_expression environnement exp) l in
    let pouet = List.iter2
              (fun expression type_
               -> let str_exp = str_expression expression in
                  let str_t = str_of_type type_ in
                  let str_rendue = ("\n" ^ str_exp ^ "\n____\n" ^ str_t ^ "\n~~~~~\n\n") in
                  print_string str_rendue)
              l
              l_types
                 
    in

    
    let _ = print_string "\n Fin des tests des types qui fonctionnent\n" in
    let e1 = App(i, j) in
    let e2 = Fun("x", App(Var("x"), Var("x"))) in

    let lm = [e1; e2] in
    let _ = List.iter
      (fun e ->
        let _ = print_string ((str_expression e) ^
                                "\n______\n" )  in 
        let _ = try
            let _ = type_expression environnement e in
            assert(false) 
          with Bad_type(str) -> print_string (str ^ "\n")
        in
        print_string ("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n")
      )
      lm
          
    in ()
end ;;



print_string "\n ~~~~~~~~~~~~~~~~~~~~~~~~~~ \n ~~~~~~~~ EXO 1 ~~~~~~~~ " ^
  "\n ~~~~~~~~~~~~~~~~~~~~~~~~~ \n\n";
Test_exo1.f_test ();


print_string "\n ~~~~~~~~~~~~~~~~~~~~~~~~~~ \n ~~~~~~~~ EXO 2 ~~~~~~~~ " ^
  "\n ~~~~~~~~~~~~~~~~~~~~~~~~~ \n\n";
Test_exo2.f_test ();


print_string "\n ~~~~~~~~~~~~~~~~~~~~~~~~~~ \n ~~~~~~~~EXO 2.5~~~~~~~~ " ^
  "\n ~~~~~~~~~~~~~~~~~~~~~~~~~ \n\n";
Test_exo2bonus.f_test ();

