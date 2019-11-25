open Inference

module Exercice1 = struct
  open BaseAST
  open SimpleTypes
  open BaseTypeChecker

  let evt = Env.empty 
  let f_test () =
    let i, j = Int(3), Int(12) in
    let bt, bf = Bool(true), Bool(false) in
    let f_int, f_bool = Fun("x", TInt, Var("x")), Fun("x", TBool, Var("x")) in

    (* Tests légitimes *) 
    let r_int = NewRef(i) in
    let r_bool = NewRef(bt) in
    let pair = Pair(i, j) in 
    let plet = Let("x", i, App(f_int, Var("x"))) in
    let op_add = App( App( Op("+"), i), j) in
    let op_b =   App( App( Op("&&"), bt), bf) in
    let op_eq =  App( App( Op("="), i), j) in
    let op_eqbool = App( App(Op("="), bt), bt) in
    let condit = If(op_b, i, op_add) in
    let unit_exp = App( App(Op(":="), r_int ), j)  in
    let seq = Sequence(unit_exp, pair) in
    let w = While(op_eq, unit_exp) in
    let let_deref = Let("x", r_int, App(Op("!"), Var("x"))) in
    let deref'  = App(Op("!"), r_int) in    
    let tab_exps =
      [r_int; r_bool; pair; plet; op_add; op_b; op_eq;
         op_eqbool; condit; unit_exp; seq; w; let_deref; deref'] in
    let _  = List.iter
               (fun exp
                ->
                 let s_exp  = str_expression exp in 
                 try
                   let t = type_expression evt exp in
                   let s_type = str_of_type t in
                   let str = "------\n" ^ s_exp ^ "\n__\n" ^ s_type ^ "\n" in
                   print_string str
               with Bad_type(s) -> print_string ("ERREUR POUR L'EXPRESSION " ^ (s_exp) ^ "\n\n"))
               tab_exps
    in
    (* expressions mal typées *)
    let _ = print_string ("Fin des expressions qui fonctionnent\n") in 
    let fe1 = App(r_int, r_int) in
    let fe2 = App(App(Op("="), i), bt) in
    let fseq = Sequence(i, j) in

    let fw = While(unit_exp, unit_exp ) in
    let lst_mauvaises_exp = [fe1; fe2; fseq; fw] in
    let _ = List.iter
              (fun exp ->
                let s_exp = (str_expression exp) in

                let _ = print_string ("\n\n->" ^ s_exp ^ "\n") in 
                let _ = 
                  try
                    let t = type_expression evt exp in

                    print_string ("ERREUR : " ^ (str_of_type t) ^ "\n~~~~~\n");
                    print_newline() 
                  with Bad_type _ ->
                    print_string ("exn\n~~~~~~~\n");
                in () 
              )
          lst_mauvaises_exp
    in ()
(* faire des exemples qui fonctionnent pas. 
   Implique l'existence d'une unique exception à lancer *)    
end;;

module Test_exo2 = struct 
  open BaseTypeReconstruction
  open RawAST
  open SimpleTypes
  let write_exp e =
    let s_exp = str_expression e in 
    let s_ret = ("Expression : \n " ^ s_exp
                ^ "\n Type :\n " ^
                  (try
                     let t = type_expression (Env.empty) e in
                     str_of_type t
                   with Bad_type _ -> "exn"
                  ) ^ "\n ____ \n")
    in
    print_string s_ret

  let evt = Env.empty 
  let f_test () =
    let i, j = Int(3), Int(12) in
    let bt, bf = Bool(true), Bool(false) in
    let f = Fun("x", Var("x")) in

    (* Tests légitimes *) 
    let r_int = Newref(i) in
    let r_bool = Newref(bt) in
    let pair = Pair(i, j) in 
    let plet = Let("x", i, App(f, Var("x"))) in
    let op_add = App(App(Op("+"), i), j) in
    let op_b =  App(App(Op("&&"), bt), bf) in
    let op_eq = App( App(Op("="), i), j) in
    let op_eqbool = App( App(Op("="), bt), bt) in
    let condit = If(op_b, i, op_add) in
    let deref = App(Op("!"), r_int) in
    let unit_exp = App(App(Op(":="), r_int), j) in 
    let seq = Sequence(unit_exp, pair) in
    let w = While(op_eq, unit_exp) in
    let nicolas = Let("x", f, App(Var "x", Var "x")) in 
    let tab_exps = [r_int; r_bool; pair; plet; op_add; op_b; op_eq;
                    op_eqbool; condit; deref; unit_exp; seq; w; nicolas] in

    let _  = List.iter
               write_exp
               tab_exps 

    in ()
end ;;



module Test_exo2bonus = struct 
  open BaseTypeReconstructionBonus
  open RawAST
  open SimpleTypes

  let write_exp e =
    let s_exp = str_expression e in 
    let s_ret = ("Expression : \n " ^ s_exp
                ^ "\n Type :\n " ^
                  (try
                     let t = type_expression (Env.empty) e in
                     str_of_type t
                   with Bad_type _ -> "exn"
                  ) ^ "\n ____ \n")
    in
    print_string s_ret

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
              write_exp 
              lm          
    in ()
end ;;


module Exo3 = struct
  open OptionTypes
  open SubAST
  open SubTypeChecker
  let write_exp e =
    let s_exp = str_expression e in 
    let s_ret = ("Expression : \n " ^ s_exp
                ^ "\n Type :\n " ^
                  (try
                     let t = type_expression (Env.empty) e in
                     str_of_type t
                   with Bad_type (s) -> ("exn : " ^ s) 
                  ) ^ "\n ____ \n")
    in
    print_string s_ret
                     
    
  let env=Env.empty
        
  let f_test () =
    let i = Int(3) in
    let ref_int = NewRef(TInt) in
    let tmaybe = App(Op("!"), ref_int) in
    let f_int = Fun("x", TInt, Var("x")) in
    let f_opt = Fun("x", TMaybe(TInt),
                    If(App(Op("IsNull"), Var("x")),
                       Int(3),
                       App(Op("valueOf"), Var("x")))) in
    let apply_fopt_tmaybe = Let("y", i, App(f_opt, Var"y")) in
    let test_list = [i; ref_int; tmaybe; f_int; f_opt; apply_fopt_tmaybe] in
    let _ = List.iter write_exp test_list in
    ()

                
                  
     
end ;; 



print_string ("\n ~~~~~~~~~~~~~~~~~~~~~~~~~~ \n ~~~~~~~~ EXO 1 ~~~~~~~~ " ^
  "\n ~~~~~~~~~~~~~~~~~~~~~~~~~ \n\n");
Exercice1.f_test ();
print_newline();
print_string("Fin de l'exo1");
let _ = read_line() in () ;

print_string ("\n ~~~~~~~~~~~~~~~~~~~~~~~~~~ \n ~~~~~~~~ EXO 2 ~~~~~~~~ " ^
  "\n ~~~~~~~~~~~~~~~~~~~~~~~~~ \n\n");
Test_exo2.f_test ();
let _ = read_line() in ();
          
print_string ("\n ~~~~~~~~~~~~~~~~~~~~~~~~~~ \n ~~~~~~~~EXO 2.5~~~~~~~~ " ^
  "\n ~~~~~~~~~~~~~~~~~~~~~~~~~ \n\n");
Test_exo2bonus.f_test ();
let _ = read_line() in () ;

print_string ("\n ~~~~~~~~~~~~~~~~~~~~~~~~~~ \n ~~~~~~~~EXO 3~~~~~~~~ " ^
                "\n ~~~~~~~~~~~~~~~~~~~~~~~~~ \n\n");
Exo3.f_test();

let _ = read_line in ();
