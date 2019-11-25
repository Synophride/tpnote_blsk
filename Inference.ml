exception Bad_type 

module SimpleTypes = struct    
  type typ =
    | TVar of string      (** Variables de type ['a] *)
    | TInt                (** Entiers [int]          *)
    | TBool               (** Booléens [bool]        *)
    | TUnit               (** Unité [unit]           *)
    | TFun  of typ * typ  (** Fonctions [T₁ ⟶ T₂]  *)
    | TPair of typ * typ  (** Paires [T₁ * T₂]       *)
    | TRef  of typ        (** Références [ref T]     *)

  let rec (str_of_type : typ -> string) = 
    function
    | TInt -> "int"
    | TBool -> "bool"
    | TUnit -> "unit"
    | TVar(str) -> str ^ "'"
    | TFun(t1, t2)  -> "( " ^ str_of_type t1 ^ " -> " ^ str_of_type t2 ^ " )"
    | TPair(t1, t2) -> "( " ^ str_of_type t1 ^ " * " ^ str_of_type t2 ^ " )"
    | TRef(t) -> str_of_type t ^ " ref"  
end

                   
(** Expressions avec annotations de types *)
module BaseAST = struct
  open SimpleTypes
  type expression =
    | Int    of int    (** Entier [n]    *)
    | Bool   of bool   (** Booléen [b]   *)
    | Unit             (** Unité [()]    *)
    | Var    of string (** Variable  [x] *)
    | App    of expression * expression
    (** Application [e₁ e₂] *)
              
    | Fun    of string * SimpleTypes.typ * expression
    (** Fonction [fun x:T -> e] *)
    | Let    of string * expression * expression
    (** Liaison [let x=e₁ in e₂] *)
    | Op     of string (** Opérateur *)
    | Pair   of expression * expression
    (** Paire [(e₁, e₂)] *)
    | NewRef of expression
    (** Création d'une référence initialisée [ref e] *)
    | Sequence of expression * expression
    (** Séquence d'expressions [e₁; e₂] *)
    | If     of expression * expression * expression
    (** Conditionnelle [if c then e₁ else e₂] *)
    | While  of expression * expression
  (** Boucle [while c do e done] *)


  let rec (str_expression : expression -> string) =
    function
    | Int(i) -> string_of_int i
    | Bool(b) -> string_of_bool b
    | Unit -> "()"
    | Var(str) -> str
    | App(e1, e2) -> "( " ^ str_expression e1 ^ " ) ( " ^ str_expression e2 ^ " )"
    | Fun(str, t, e) -> "fun (" ^ str ^ " : " ^ str_of_type t ^ ") -> " ^ str_expression e
    | Let(str, e1, e2) -> "let " ^ str ^ " = " ^ str_expression e1 ^ " in \n" ^ str_expression e2
    | Op(str) -> str
    | Pair(e1, e2) -> "(" ^ str_expression e1 ^ ", " ^ str_expression e2 ^ " )"
    | NewRef(exp) -> str_expression exp ^ " ref"
    | Sequence(e1, e2) -> str_expression e1 ^ ";\n" ^ str_expression e2
    | If(eb, e1, e2) -> "if( " ^ str_expression eb
                        ^ " )\nthen " ^ str_expression e1
                        ^ "\nelse " ^ str_expression e2
    | While(eb, e) -> "While ( " ^ str_expression eb ^ " ) do \n " ^ str_expression e ^ " \n end \n"
end


(*******
 * Vérificateur de types.
 *******)
module BaseTypeChecker = struct
  open SimpleTypes
  open BaseAST
  module Env = Map.Make(String)
  type type_env = SimpleTypes.typ Env.t

  let rec type_expression (env: type_env) (e: expression) : typ =
    match e with
    | Int(_) -> TInt
    | Bool(_) -> TBool
    | Unit -> TUnit
    | Var(str) -> Env.find str env
    | App(e1, e2)
      ->  let t2 = type_expression env e2 in 
	  let t1 = 
	    (match e1 with 
	     | Op(s) (* étant donné qu'on a besoin du type du premier paramètre pour déterminer 
                        le type de l'expression, traitement du cas op dans l'application *) 
	       ->(	match s with 
			| "+" 
			  -> 	TFun(TInt, TFun(TInt, TInt))
			| "&&" | "||" 
			  ->	TFun(TBool, TFun(TBool, TBool))
			      
			|"=" | "<" | ">" 
			 ->	TFun(t2, TFun(t2, TBool))
			| "!" | "deref"(* dé-référençage *)  
			  ->(	match t2 with 
				|TRef(t) -> TFun(TRef(t), t)
				| _ -> raise Bad_type)
                        | ":=" | "setref" 
                          ->(   match t2 with
                                | TRef(t) -> TFun(t2, TFun(t, TUnit))
                                | _ -> raise (Bad_type)
		            )
                        | "fst"
                          -> (match t2 with | TPair(t, _) -> t
                                            | _ -> raise Bad_type
                             )
                        | "snd" -> (match t2 with | TPair(_,t) -> t | _ -> raise Bad_type) 
                        | _ -> raise (Bad_type)
                 )
	     | _ -> type_expression env e1 
	    )
	  in (match t1 with 
	      | TFun(tparam, tret)
		->   if tparam = t2 
		     then tret 
		     else raise (Bad_type)
              | _ -> raise (Bad_type)
             )
           
    | Fun(nom_var, type_var, term)
      ->  let nouvel_evt = Env.add (nom_var) (type_var) (env) in
          let nouveau_type = type_expression nouvel_evt term in
          TFun(type_var, nouveau_type)
    | Let(nom_var, e1, e2)
      ->  let type_var = type_expression env e1 in
          type_expression (Env.add nom_var type_var env) e2
    | Op(op) -> failwith ""
    | Pair(e1, e2) -> TPair(type_expression env e1, type_expression env e2)
    | NewRef(e) -> TRef(type_expression env e)
    | Sequence(e1, e2) -> let type_e1 = type_expression env e1 in
                          if type_e1 = TUnit
                          then type_expression env e2
                          else raise (Bad_type)
    | If(cond, e1, e2) -> let f = type_expression env in
                          if f cond <> TBool
                          then raise (Bad_type)
                          else let t1, t2 = f e1, f e2 in
                               if t1 = t2
                               then t1
                               else raise (Bad_type)
    | While(c, e) -> let type_c = type_expression env c in
                     if type_c = TBool
                     then let te = type_expression env e in
                          if te = TUnit then TUnit
                          else raise (Bad_type)
                     else raise (Bad_type)
end


(** 
    Exercice 2 : inférence des types simples.

    Ci-dessous, une syntaxe quasi-identique à [BaseAST].
    A disparu : l'annotation du paramètre formel d'une fonction par son type.

    Objectif : inférence de types.
 *)
module RawAST = struct
  open SimpleTypes
  (** Expressions *)
  type expression =
    | Int    of int    (** Entier [n]    *)
    | Bool   of bool   (** Booléen [b]   *)
    | Unit             (** Unité [()]    *)
    | Var    of string (** Variable  [x] *)
    | App    of expression * expression
    (** Application [e₁ e₂] *)
    | Fun    of string * expression
    (** Fonction [fun x -> e] *)
    | Let    of string * expression * expression
    (** Liaison [let x=e₁ in e₂] *)
    | Op     of string (** Opérateur *)
    | Pair   of expression * expression
    (** Paire [(e₁, e₂)] *)
    | Newref of expression
    (** Création d'une référence initialisée [ref e] *)
    | Sequence of expression * expression
    (** Séquence d'expressions [e₁; e₂] *)
    | If     of expression * expression * expression
    (** Conditionnelle [if c then e₁ else e₂] *)
    | While  of expression * expression
  (** Boucle [while c do e done] *)
	      
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

end
              
module BaseTypeReconstruction = struct
  
  open SimpleTypes
  open RawAST
  module Env = Map.Make(String)
  type type_env = SimpleTypes.typ Env.t 
  type t_contrainte = SimpleTypes.typ * SimpleTypes.typ (* None = Tout type *) 
  module CSet = Set.Make(struct type t = t_contrainte let compare = compare end)


  (* fonction de création d'un compteur *) 
  let mk_cpt_vt () =
    let x = ref 0 in
    (fun ()
     -> let s = string_of_int !x in
        x := (!x)+1;
        s)
    

  let str_contrainte (t1, t2) =
    "(" ^ (str_of_type t1) ^ ") ?= (" ^ (str_of_type t2) ^ ")"
    
  let type_operateur fun_cpt op =
    match op with 
    | "+" -> TFun(TInt, TFun(TInt, TInt)) 
    | "&&" | "||" -> TFun(TBool, TFun(TBool, TBool))
    | "<" | "=" 
      -> 	let vt = TVar(fun_cpt()) in 
		TFun(vt, TFun(vt, TBool))
    | "!" | "deref" -> let vt = TVar(fun_cpt()) in TFun(TRef(vt), vt)  
    | "ref" -> let vt = TVar(fun_cpt ()) in TFun(vt, TRef(vt))
    | ":=" | "setref" -> let vt = TVar(fun_cpt()) in TFun(TRef(vt),  TFun(vt, TUnit))
    | "fst" -> let vt = TVar(fun_cpt()) in TFun(TPair(vt, TVar(fun_cpt())), vt)
    | "snd" -> let vt = TVar(fun_cpt()) in TFun(TPair(TVar(fun_cpt()), vt), vt)
    | _ -> failwith "opérateur pas implémenté"
  let print_ensemble_contraintes =
    CSet.iter (fun c -> print_string ("\n" ^ (str_contrainte c) ^ "\n~~~"))
    
  (** 
      Objectif : compléter la fonction suivante de typage d'une expression.
      Un appel [type_expression e] doit :
      - renvoyer le type de [e] dans l'environnement [env] si [e] est bien typée
      - déclencher une exception sinon
      
      Procéder en deux étapes : génération de contraintes sur les types,
      puis résolution par unification.
   **)
  let type_expression (env: type_env) (e: expression) : SimpleTypes.typ =
    (** I. Génération des contraintes sur l'expression **)
    let generation_contraintes (env:type_env) (e:expression) : (CSet.t * SimpleTypes.typ) =
      (* génération de variables de types uniques *)
      let get_new_vartyp = mk_cpt_vt () in
      (* ensemble des contraintes *) 
      let constraints = ref CSet.empty in
      (* ajoute une contrainte à l'ensemble *) 
      let add_cst c = constraints := CSet.add c (!constraints) in
      let rec build_cst (evt : type_env) (exp : expression) : SimpleTypes.typ =
        match exp with 
        | Int(i) -> TInt
        | Int(_) -> TInt
        | Bool(_)-> TBool
        | Unit   -> TUnit
        | Var(nom_var) ->  (Env.find nom_var evt)
        | App(f_exp, param_exp)
          -> let type_f = build_cst evt f_exp in
             let type_param = build_cst evt param_exp in
             (* ajout d'une variable de type représentant le type de retour *) 
             let type_retour= TVar(get_new_vartyp()) in
             begin
               (* ajout de la contrainte liant le type de l'expression fonctionnelle, celui 
                  du paramètre ainsi que le retour *)
               add_cst (type_f, TFun(type_param, type_retour));
               (* une fois la fonction appliquée, le type de l'expression est celle du type de retour
                  de la fonction *)
               type_retour
             end
        | Fun(nom_var, expr)
(* On définit le type du paramètre *)
          -> let type_param = TVar(get_new_vartyp()) in
             (* environnement visible depuis l'intérieur de la fonction : 
                ajout de la variable de type du paramètre *)
             let env' = Env.add nom_var type_param evt in
             let type_retour = build_cst env' expr in
             TFun(type_param, type_retour)
        | Let(s, e1, e2)
          -> let type_s = build_cst env e1 in
             let evt' = Env.add (s) (type_s) evt in
             build_cst evt' e2

        | Op(op)
          -> type_operateur get_new_vartyp op
        | Pair(e1, e2) -> TPair(build_cst evt e1, build_cst evt e2)
        | Newref(e) -> TRef(build_cst evt e)
        | Sequence(e1, e2)
          -> let t1, t2 = build_cst evt e1, build_cst evt e2 in
             begin
               (* On part du principe que e1 doit être un effet de bord *)
               add_cst (t1, TUnit);
               t2
             end
        | If(condition, e1, e2)
          -> let tb = build_cst evt condition in
             let t1 = build_cst evt e1 in
             let t2 = build_cst evt e2 in
             begin
               add_cst (tb, TBool);
               add_cst (t1, t2);
               t1
             end
        | While(condition, e)
          -> let tb = build_cst evt condition in
             let texp = build_cst evt e in
             begin
               add_cst (tb, TBool);
               (* on part du principe que e est un effet
                  de bord et ne doit pas renvoyer de valeur *)
               add_cst (texp, TUnit);
               TUnit
             end
      in
      let t = build_cst env e in
      (!constraints, t)
    in
    
    (** II. Résolution des contraintes *) 

    let resolution_contraintes cset t_exp =
      (* type de retour *) 
      let t_retour_gen = ref t_exp in 
      (* liste des contraintes à éliminer *) 
      let constraints = ref cset in
      
      let cset_map f cset = CSet.fold (fun c cset -> CSet.add (f c) cset) cset CSet.empty in
      let constraints_map f = (constraints := cset_map f (!constraints)) in 
      (** suppression et ajout de contraintes dans l'ensemble des contraintes **)
      let rm ct = constraints := CSet.remove ct (!constraints) in
      let add ct = constraints := CSet.add ct (!constraints) in

      (** fonction déterminant si une variable de type est contenue dans le type t **)
      let rec contains str_var t =
        match t with
        | TVar(str) -> str = str_var
        | TInt | TBool | TUnit -> false
                                
        | TFun(t1, t2) | TPair(t1, t2) -> (contains str_var t1 || contains str_var t2) 
        | TRef(t) -> contains str_var t
      in
      (* t[TypVar(str_var) <- t_remp]. str_var pas contenu dans t_remp *)
      let substitution str_var t_remp t =
        let rec subst t = 
          match t with
          | TBool | TInt | TUnit -> t
          | TVar(s) -> if(s = str_var) then t_remp else t
          | TFun(t1, t2) -> TFun(subst t1, subst t2)
          | TPair(t1, t2) -> TPair(subst t1, subst t2)
          | TRef(t') -> TRef(subst t')
        in
        subst t
      in

      
      (** Fonction de résolution des contraintes **)
      let rec res () =
        match CSet.min_elt_opt (!constraints) with
        | None -> ()
        | Some(cst)
          -> let _ = rm cst in (*effacement de la contrainte*)
             let a, b = cst in
             let _ =
               if a = b
               then () 
               else
                 match cst with
                 | TVar(s), other
                   | other, TVar(s) 
                   -> if other = TVar(s) (* tautologie, rien à faire *)
                      then ()
                             (* Cas où un type est contenu dans lui même : insulter l'utilisateur *)
                      else if contains s other 
                      then
                        raise (Bad_type)
                      else (* On peut faire la substitution dans ce cas *)
                        let _ = constraints_map
                                  (fun (a,b) -> (substitution s other a,
                                                 substitution s other b)) in
                        let _ =  t_retour_gen := substitution s other (!t_retour_gen)
                        in ()

                 | TPair(t1a, t1b), TPair(t2a, t2b) | TFun(t1a, t1b), TFun(t2a, t2b) 
                   -> let _ = add (t1a, t2a) in 
                      let _ = add (t1b, t2b) in ()
                 | TRef(t1), TRef(t2)
                   -> let _ = add (t1,t2) in ()

                 | _ -> raise (Bad_type)
             in res ()
      in
      let _ = res () in
      (!t_retour_gen)
    in
    let (contraintes, t) = generation_contraintes env e in
    (*    let _ = print_string "CONTRAINTES:\n\n\n" in
    let _ = print_ensemble_contraintes contraintes in
    let _ = print_string "FIN DES CONTRAINTES\n" in *) 
    let  type_retour = resolution_contraintes contraintes t in
    type_retour

end


(* exactement la même chose que l'exo 2, mis à part le traitement du let ... lors 
de la génération de contraintes *) 
module BaseTypeReconstructionBonus = struct
  
  open SimpleTypes
  open RawAST
  module Env = Map.Make(String)
  type type_env = SimpleTypes.typ Env.t 
  type t_contrainte = SimpleTypes.typ * SimpleTypes.typ 

  module CSet = Set.Make(struct type t = t_contrainte let compare = compare end)

  (* fonction de création d'un compteur *) 
  let mk_cpt_vt () =
    let x = ref 0 in
    (fun ()
     -> let s = string_of_int !x in
        x := (!x)+1;
        s)

  (* substitue toutes les ocurrences de e1 par e2 dans l'expression e *)
  let subst_e stvar e2 e =
    let rec s e =
      match e with
      | Var(s) -> if s = stvar then e2 else e
      | Int _ | Bool _ | Unit | Op _ -> e
      | Pair(e_fst, e_snd) -> Pair(s e_fst, s e_snd)
      | Fun(p, er) -> Fun(p, s er)
      | App(ef, er) -> App(s ef, s er)
      | Let(str, ea, eb) -> Let(str, s ea, s eb)
      | Newref(e) -> Newref(s e)
      | Sequence(e, e') -> Sequence(s e, s e')
      | If(c, e, e') -> If(s c, s e, s e')
      | While(c, e) -> While(s c, s e)  
    in s e                        

  let str_contrainte (t1, t2) =
    "(" ^ (str_of_type t1) ^ ") ?= (" ^ (str_of_type t2) ^ ")"
  let type_operateur fun_cpt op =
    match op with 
    | "+" -> TFun(TInt, TFun(TInt, TInt)) 
    | "&&" | "||" -> TFun(TBool, TFun(TBool, TBool))
    | "<" | "=" 
      -> 	let vt = TVar(fun_cpt()) in 
		TFun(vt, TFun(vt, TBool))
    | "!" | "deref" -> let vt = TVar(fun_cpt()) in TFun(TRef(vt), vt)  
    | "ref" -> let vt = TVar(fun_cpt ()) in TFun(vt, TRef(vt))
    | ":=" | "setref" -> let vt = TVar(fun_cpt()) in TFun(TRef(vt),  TFun(vt, TUnit))
    | "fst" -> let vt = TVar(fun_cpt()) in TFun(TPair(vt, TVar(fun_cpt())), vt)
    | "snd" -> let vt = TVar(fun_cpt()) in TFun(TPair(TVar(fun_cpt()), vt), vt)
    | _ -> failwith "opérateur pas implémenté"
         
  let print_ensemble_contraintes =
    CSet.iter (fun c -> print_string ("\n" ^ (str_contrainte c) ^ "\n~~~"))
    
  (** 
      Objectif : compléter la fonction suivante de typage d'une expression.
      Un appel [type_expression e] doit :
      - renvoyer le type de [e] dans l'environnement [env] si [e] est bien typée
      - déclencher une exception sinon
      
      Procéder en deux étapes : génération de contraintes sur les types,
      puis résolution par unification.
   **)

  let type_expression (env: type_env) (e: expression) : SimpleTypes.typ =
    (** I. Génération des contraintes sur l'expression **)
    let generation_contraintes (env:type_env) (e:expression) : (CSet.t * SimpleTypes.typ) =
      (* génération de variables de types uniques *)
      let get_new_vartyp = mk_cpt_vt () in
      (* ensemble des contraintes *) 
      let constraints = ref CSet.empty in
      (* ajoute une contrainte à l'ensemble *) 
      let add_cst c = constraints := CSet.add c (!constraints) in
      let rec build_cst (evt : type_env) (exp : expression) : SimpleTypes.typ =
        match exp with 
        | Int(i) -> TInt
        | Int(_) -> TInt
        | Bool(_)-> TBool
        | Unit   -> TUnit
        | Var(nom_var) ->  (Env.find nom_var evt)

        | App(f_exp, param_exp)
          -> let type_f = build_cst evt f_exp in
             let type_param = build_cst evt param_exp in
             (* ajout d'une variable de type représentant le type de retour *) 
             let type_retour= TVar(get_new_vartyp()) in
             begin
               (* ajout de la contrainte liant le type de l'expression fonctionnelle, celui 
                  du paramètre ainsi que le retour *)
               add_cst (type_f, TFun(type_param, type_retour));
               (* une fois la fonction appliquée, le type de l'expression est celle du type de retour
                  de la fonction *)
               type_retour
             end
        | Fun(nom_var, expr)
(* On définit le type du paramètre *)
          -> 	let type_param = TVar(get_new_vartyp()) in
                (* environnement visible depuis l'intérieur de la fonction : 
                ajout de la variable de type du paramètre *)
                let env' = Env.add nom_var type_param evt in
                let type_retour = build_cst env' expr in
                TFun(type_param, type_retour)
        | Let(s, e1, e2)
          -> let e2' = subst_e s e1 e2 in
             build_cst env e2'
        | Op(op)
          -> type_operateur get_new_vartyp op
        | Pair(e1, e2) -> TPair(build_cst evt e1, build_cst evt e2)
        | Newref(e) -> TRef(build_cst evt e)
        | Sequence(e1, e2)
          -> let t1, t2 = build_cst evt e1, build_cst evt e2 in
             begin
               (* On part du principe que e1 doit être un effet de bord *)
               add_cst (t1, TUnit);
               t2
             end
        | If(condition, e1, e2)
          -> let tb = build_cst evt condition in
             let t1 = build_cst evt e1 in
             let t2 = build_cst evt e2 in
             begin
               add_cst (tb, TBool);
               add_cst (t1, t2);
               t1
             end
        | While(condition, e)
          -> let tb = build_cst evt condition in
             let texp = build_cst evt e in
             begin
               add_cst (tb, TBool);
               (* on part du principe que e est un effet de bord et ne doit pas renvoyer de valeur *)
               add_cst (texp, TUnit);
               TUnit
             end
        | _ -> failwith "" 
      in
      let t = build_cst env e in
      (!constraints, t)
    in
    
    (** II. Résolution des contraintes *) 

    let resolution_contraintes cset t_exp =
      (* type de retour *) 
      let t_retour_gen = ref t_exp in 
      (* liste des contraintes à éliminer *) 
      let constraints = ref cset in

      let cset_map f cset = CSet.fold (fun c cset -> CSet.add (f c) cset) cset CSet.empty in
      let constraints_map f = (constraints := cset_map f (!constraints)) in 
      (** suppression et ajout de contraintes dans l'ensemble des contraintes **)
      let rm ct = constraints := CSet.remove ct (!constraints) in
      let add ct = constraints := CSet.add ct (!constraints) in

      (** fonction déterminant si une variable de type est contenue dans le type t **)
      let rec contains str_var t =
        match t with
        | TVar(str) -> str = str_var
        | TInt | TBool | TUnit -> false
                                
        | TFun(t1, t2) | TPair(t1, t2) -> (contains str_var t1 || contains str_var t2) 
        | TRef(t) -> contains str_var t
      in
      (* t[TypVar(str_var) <- t_remp]. str_var pas contenu dans t_remp *)
      let substitution str_var t_remp t =
        let rec subst t = 
          match t with
          | TBool | TInt | TUnit -> t
          | TVar(s) -> if(s = str_var) then t_remp else t
          | TFun(t1, t2) -> TFun(subst t1, subst t2)
          | TPair(t1, t2) -> TPair(subst t1, subst t2)
          | TRef(t') -> TRef(subst t')
        in
        subst t
      in

      
      (** Fonction de résolution des contraintes **)
      let rec res () =
        match CSet.min_elt_opt (!constraints) with
        | None -> ()
        | Some(cst)
          -> let _ = rm cst in
             let a, b = cst in
             let _ = if a = b
                     then ()
                     else
                       match cst with
                       | TVar(s), other 
                         -> if other = TVar(s) (* tautologie, rien à faire *)
                            then ()
                                   (* Cas où un type est contenu dans lui même : insulter l'utilisateur *)
                            else if contains s other 
                            then
                              raise (Bad_type)
                            else (* On peut faire la substitution dans ce cas *)
                              let _ = constraints_map
                                        (fun (a,b) -> (substitution s other a,
                                                       substitution s other b)) in
                              (*     let _ = print_string "substitution de type \n" in
                                let _ = print_string ((str_of_type (!t_retour_gen))^"\n") in
                                let _ = print_string ("remplacement de " ^ s ^ " par " ^
                                                        (str_of_type other) ^ " dans " ^
                                                          (str_of_type (!t_retour_gen))  ^
                                                            "\n") in *)
                              let _ =  t_retour_gen := substitution s other (!t_retour_gen)
                              in ()

                       | TPair(t1a, t1b), TPair(t2a, t2b) | TFun(t1a, t1b), TFun(t2a, t2b) 
                         -> let _ = add (t1a, t2a) in 
                            let _ = add (t1b, t2b) in ()
                       | TRef(t1), TRef(t2)
                         -> let _ = add (t1,t2) in ()
                       | other, TVar(s) -> let _ = add (TVar(s), other) in ()
                       | _ -> raise (Bad_type)
             in res ()
      in
      let _ = res () in
      (!t_retour_gen)
    in
    let (contraintes, t) = generation_contraintes env e in
    (*let _ = print_string "CONTRAINTES:\n\n\n" in
    let _ = print_ensemble_contraintes contraintes in
    let _ = print_string "FIN DES CONTRAINTES\n" in*)
    let  type_retour = resolution_contraintes contraintes t in
    type_retour

end



(**
   Exercice 3 : sous-typage.

   On ajoute un type optionnel [T?] désignant des valeurs de type [T]
   éventuellement non définies (contrairement au type [T] lui-même pour
   lequel la valeur est à coup sûr définie.

   On a donc la relation de sous-typage [T <: T?], de laquelle on déduit
   une relation plus générale avec les règles habituelles.
	T sous-type de T-Question
 *)
module OptionTypes = struct

  (** Les types simples + un type optionnel *)
  type typ =
    | TVar of string      (** Variables de type ['a] *)
    | TInt                (** Entiers [int]          *)
    | TBool               (** Booléens [bool]        *)
    | TUnit               (** Unité [unit]           *)
    | TFun  of typ * typ  (** Fonctions [T₁ ⟶ T₂]  *)
    | TPair of typ * typ  (** Paires [T₁ * T₂]       *)
    | TRef  of typ        (** Références [ref T]     *)

    | TMaybe of typ       (** Type option [T?]       *)

  let rec (str_of_type : typ -> string) = 
    function
    | TInt -> "int"
    | TBool -> "bool"
    | TUnit -> "unit"
    | TVar(str) -> str ^ "'"
    | TFun(t1, t2)  -> "( " ^ str_of_type t1 ^ " -> " ^ str_of_type t2 ^ " )"
    | TPair(t1, t2) -> "( " ^ str_of_type t1 ^ " * " ^ str_of_type t2 ^ " )"
    | TRef(t) -> str_of_type t ^ " ref"
    | TMaybe(t) -> "[" ^ str_of_type t ^ "?]" 
end
                   
                   

(**
   Parallèlement à l'introduction du type optionnel, on modifie l'opérateur
   de création de référence, qui crée une référence non initialisée sur un
   type [T] donné en paramètre.
   L'expression [newref T] aura donc le type [ref T?].

   On crée également un opérateur ["isNull"] testant si une valeur donnée
   est indéfinie.
 *)
module SubAST = struct
  open OptionTypes
  type expression =
    | Int    of int    (** Entier [n]    *)
    | Bool   of bool   (** Booléen [b]   *)
    | Unit             (** Unité [()]    *)
    | Var of string 
    | App    of expression * expression
    (** Application [e₁ e₂] *)
    | Fun    of string * OptionTypes.typ * expression
    (** Fonction [fun x:T -> e] *)
    | Let    of string * expression * expression
    (** Liaison [let x=e₁ in e₂] *)
    | Op     of string (** Opérateur *)
    | Pair   of expression * expression
    (** Paire [(e₁, e₂)] *)
    | NewRef of OptionTypes.typ
    (** Création d'une référence non initialisée [newref T] *)
    | Sequence of expression * expression
    (** Séquence d'expressions [e₁; e₂] *)
    | If     of expression * expression * expression
    (** Conditionnelle [if c then e₁ else e₂] *)
    | While  of expression * expression
  (** Boucle [while c do e done] *)

  let rec (str_expression : expression -> string) =
    function
    | Int(i) -> string_of_int i
    | Bool(b) -> string_of_bool b
    | Unit -> "()"
    | Var(str) -> str
    | App(e1, e2) -> "( " ^ str_expression e1 ^ " ) ( " ^ str_expression e2 ^ " )"
    | Fun(str,t, e) -> "fun (" ^ str ^ ": "^ (str_of_type t) ^ ") -> " ^ str_expression e
    | Let(str, e1, e2) -> "let " ^ str ^ " = " ^ str_expression e1 ^ " in \n" ^ str_expression e2
    | Op(str) -> str
    | Pair(e1, e2) -> "(" ^ str_expression e1 ^ ", " ^ str_expression e2 ^ " )"
    | NewRef(t) -> str_of_type t ^ " ref"
    | Sequence(e1, e2) -> str_expression e1 ^ ";\n" ^ str_expression e2
    | If(eb, e1, e2) -> "if( " ^ str_expression eb
                        ^ " )\nthen " ^ str_expression e1
                        ^ "\nelse " ^ str_expression e2
    | While(eb, e)
      -> "While ( " ^ str_expression eb ^ " ) do \n " ^ str_expression e ^ " \n end \n"
end

(**
   Vérification de types avec sous-typage.

   Ajouter du sous-typage au vérificateur de types simples, avec la règle
   algorithmique standard : le paramètre effectif d'un appel de fonction peut
   être un sous-type du type du paramètre formel.

   On ajoutera les particularités suivantes :
   - Tout opérateur travaillant sur des valeurs concrètes nécessitera des
	opérandes dont le type *n'est pas* un type optionnel.
   - Dans une expression de la forme [if isNull(a) then e1 else e2] avec [a] de
    type [T?], on pourra donner à [a] le type [T] dans la branche [e2].
 **)
module SubTypeChecker = struct
  open OptionTypes
  open SubAST
     
  module Env = Map.Make(String)
  module S = Set.Make(String)
  type type_env = typ Env.t
  let x = ref 0
        
  let mk_new_vartype () =
    let y = !x in
    x := (!x) + 1;
    string_of_int y

  let rec suppr_maybe t =
    match t with
    | TMaybe t' -> suppr_maybe t'
    | _ -> t
         
  let rec varset =    
    function
    | Var(s) -> S.singleton s
    | Int _ | Bool _ | Op(_) | Unit | NewRef(_) -> S.empty
    | Fun(s, _, exp)
      -> let varset_exp = varset exp in
         S.add s varset_exp (* au cas où le param est pas utilisé *)
    | Let(s, e1, e2)
      -> S.union (varset e1) (S.add s (varset e2))
       
    | App(e1, e2) | Pair(e1, e2) | While(e1, e2) | Sequence(e1, e2)
      -> S.union (varset e1) (varset e2)
    | If(c, e1, e2)
      -> S.union (S.union (varset c) (varset e1)) (varset e2)

  let rec vl =
    function
    | Var(s) -> S.singleton s
    | Int _ | Bool _ | Op(_) | Unit | NewRef(_) -> S.empty
    | Fun(s, _, exp)
      -> let vl_exp = vl exp in
         S.remove s vl_exp
    | Let(s, e1, e2)
      -> S.union (vl e1) (S.remove s (vl e2))
       
    | App(e1, e2) | Pair(e1, e2) | While(e1, e2) | Sequence(e1, e2)
      -> S.union (vl e1) (vl e2)
    | If(c, e1, e2)
      -> S.union (S.union (vl c) (vl e1)) (vl e2)
       
       
  (* Supprime les couches inutiles
     de TMaybe/"minimise" un type *)
  let rec minim t = 
    match t with 
    | TMaybe(t')
      -> (match t' with | TMaybe(t'') -> minim t' | _ -> t' )   
    | _ -> t
           
  (* renvoie true si t1 <= t2 *)
  (* probablement de la merde *)
  let rec is_subtype t1 t2 = 
    if t1 = t2 
    then true 
    else match t2 with
	 | TMaybe(t) -> is_subtype t1 t
	 | _ -> false

  let rec replace_var exp set_vars =
    match exp with
    | Let(s, e1, e2)
      -> if S.mem s set_vars
         then let vt = ref (mk_new_vartype()) in
              while S.mem (!vt) set_vars do
                vt := mk_new_vartype()
              done; 
         else 
           failwith ("to do")
    | _ -> failwith "to do"

  let rec generalisation t1 t2 =
    if t1 = t2 
    then minim t1
    else if is_subtype t1 t2 
    then minim t2
    else if is_subtype t2 t1 
    then minim t1
    else raise (Bad_type)
      
  let rec subst_var s eremp e =
    match e with
    | Var(s') -> if s = s' then eremp else e
    | NewRef _ | Int _ | Bool _ | Unit | Op _ -> e
    | Fun(s', t, e')
      -> if s = s'
         then e
         else Fun(s', t, subst_var s eremp e')
    | Let(s', t, e') 
       -> if s = s'
         then e
          else Let(s', t, subst_var s eremp e')
    | Pair(e1, e2) -> Pair(subst_var s eremp e1, subst_var s eremp e2)
    | Sequence(e1, e2) -> Sequence(subst_var s eremp e1, subst_var s eremp e2)
    | While(e1, e2)  -> While(subst_var s eremp e1, subst_var s eremp e2)
    | App(e1, e2)    -> App(subst_var s eremp e1, subst_var s eremp e2)
    | If(e1, e2, e3) -> If(subst_var s eremp e1, subst_var s eremp e2,subst_var s eremp e3)
                       


  let type_expression (env: type_env) (exp : expression) = 
    let rec t_exp (env:type_env) (exp: expression) : OptionTypes.typ = 
      match exp with 
      | Int(_) -> TInt
      | Bool(_) -> TBool
      | Unit -> TUnit 
      | Var(v) -> Env.find v env
      | App(e1, e2)
        -> gestion_app env e1 e2 
      | Fun(s, t, e)
        -> let t_e = t_exp (Env.add s t env) e in
           TFun(t, t_e) 
      | Let(s, e1, e2)
        -> let t1 = t_exp env e1 in
           t_exp (Env.add s t1 env) e2
      | Op(s) -> failwith "méchant user qui fait n'importe quoi"
      | Pair(e1, e2)-> TPair(t_exp env e1, t_exp env e2)
      | NewRef(t) -> TRef(minim (TMaybe(t)))
      | Sequence(a, b)
        ->  let t_a, t_b = t_exp env a , t_exp env b in
            if t_a = TUnit
            then t_b
            else raise (Bad_type)
      | If(c, e1, e2)
        -> gestion_if env c e1 e2 
      | While(c,  i)
        -> let tc, ti = t_exp env c, t_exp env i in
           if tc = TBool
           then if ti = TUnit
                then TUnit
                else raise (Bad_type)
           else raise (Bad_type)

    (* gestion du cas de la conditionnelle *) 
    and gestion_if (env:type_env) (c:expression) (e1:expression) (e2:expression) : OptionTypes.typ = 
      let ct = t_exp env c in
      if ct = TBool
      then
        match c with
        (* TODO Généraliser au isnull avec des expressions si j'ai que ça à faire *) 
        | App(Op("IsNull"), Var(x))
          -> let t1 = t_exp env e1 in
             let t_x = suppr_maybe (Env.find x env)
             in
             let env2 = Env.add x t_x env in
             let t2 = t_exp env2 e2 in
             generalisation t1 t2
             
        | _ -> let t1 = t_exp env e1 in
               let t2 = t_exp env e2 in
               generalisation t1 t2
      else
        raise (Bad_type)

    (* Gestion de l'application d'une expression à une autre *) 
    and gestion_app env e1 e2 =
      let t2 = t_exp env e2 in
      let t1 =
        match e1 with
        | Op(op)
          ->( match op with
              | "+" -> TFun(TInt, TFun(TInt, TInt))
              | "=" | "<"
                -> TFun(t2, TFun(t2, TBool))
	      | "IsNull"
                ->( match t2 with
                    | TMaybe(t) -> TFun(minim t2, TBool)
   		    | _ -> TFun(t2, TBool)
		  )
	      | "!" -> (match t2 with TRef(t) -> TFun(t2, t) | _ -> raise (Bad_type))
                     
              | "*" (* Fonction censée donner la valeur 
                       d'une référence, et planter
                       si la référence est égale à null *) 
                ->
                 (match t2 with
                  | TRef(TMaybe(t)) -> t
                  | TRef(t) -> t
                  | _ -> raise (Bad_type)
                 )
              | "valueOf"
                -> TFun(t2, suppr_maybe t2)
	      | ":="
                -> (match t2 with
                      TRef(t) -> TFun(t2, TFun(t, TUnit))
                    | _ -> raise (Bad_type))
              | "&&" | "||" -> TFun(TBool, TFun(TBool, TBool))
	      | _ -> failwith "opérateur pas implémenté"
	    )
        | _ -> t_exp env e1
      in 
      let m = 
        match t1 with 
	(* type de param théorique, 
           peut être plus étendu 
           que le type réel *)
	| TFun(tparam, tret)
	  -> if t2 = tparam || is_subtype (minim t2) (minim tparam)
	     then tret
	     else raise (Bad_type)
        | _ -> raise (Bad_type)
      in 
      m
    in
    let (x : OptionTypes.typ) = t_exp env exp in
    x
      
end 


module SubAST4 = struct
  open OptionTypes
  type expression =
    | Int    of int    (** Entier [n]    *)
    | Bool   of bool   (** Booléen [b]   *)
    | Unit             (** Unité [()]    *)
    | Var of string 
    | App    of expression * expression
    (** Application [e₁ e₂] *)
    | Fun    of string * expression
    (** Fonction [fun x:T -> e] *)
    | Let    of string * expression * expression
    (** Liaison [let x=e₁ in e₂] *)
    | Op     of string (** Opérateur *)
    | Pair   of expression * expression
    (** Paire [(e₁, e₂)] *)
    | NewRef
    (** Création d'une référence non initialisée [newref T] *)
    | Sequence of expression * expression
    (** Séquence d'expressions [e₁; e₂] *)
    | If     of expression * expression * expression
    (** Conditionnelle [if c then e₁ else e₂] *)
    | While  of expression * expression
    (** Boucle [while c do e done] *)

  let rec (str_expression : expression -> string) =
    function
    | Int(i) -> string_of_int i
    | Bool(b) -> string_of_bool b
    | Unit -> "()"
    | Var(str) -> str
    | App(e1, e2) -> "( " ^ str_expression e1 ^ " ) ( " ^ str_expression e2 ^ " )"
    | Fun(str, e) -> ("fun(" ^ str ^ ") -> " ^ str_expression e) 
    | Let(str, e1, e2) -> "let " ^ str ^ " = " ^ str_expression e1 ^ " in \n" ^ str_expression e2
    | Op(str) -> str
    | Pair(e1, e2) -> "(" ^ str_expression e1 ^ ", " ^ str_expression e2 ^ " )"
    | NewRef -> " NewRef"
    | Sequence(e1, e2) -> str_expression e1 ^ ";\n" ^ str_expression e2
    | If(eb, e1, e2) -> "if( " ^ str_expression eb
                        ^ " )\nthen " ^ str_expression e1
                        ^ "\nelse " ^ str_expression e2
    | While(eb, e)
      -> "While ( " ^ str_expression eb ^ " ) do \n " ^ str_expression e ^ " \n end \n"
end
               
module Ex4 = struct
  open OptionTypes
  open SubAST4
  module Env = Map.Make(String)

  type type_env = typ Env.t
  type contrainte =
    | Eq of typ * typ
    | SubT of typ * typ
                      
  module CSet = Set.Make(struct type t = contrainte let compare = compare end)

  let type_operateur fun_cpt op =
    match op with

    | "+" -> TFun(TInt, TFun(TInt, TInt)) 
    | "&&" | "||" -> TFun(TBool, TFun(TBool, TBool))
    | "<" | "=" 
      ->  let vt = TVar(fun_cpt()) in 
	  TFun(vt, TFun(vt, TBool))
    | "deref" | "!" -> let vt = TVar(fun_cpt()) in TFun(TRef(vt), vt)
    | "IsNull" -> let vt = TVar(fun_cpt ()) in TFun(vt, TBool)
    (* todo : ajouter d'autres opérateurs *) 
    | _ -> failwith "opérateur pas implémenté" 

  (* fonction de création d'un compteur *) 
  let mk_cpt () =
    let x = ref 0 in
    (fun ()
     -> let s = string_of_int !x in
        x := (!x)+1;
        s)
  (* Supprime les couches inutiles
     de TMaybe/"minimise" un type *)
  let rec minim t = 
    match t with 
    | TMaybe(t')
      -> (match t' with | TMaybe(t'') -> minim t' | _ -> t' )   
    | _ -> t
         
  (* renvoie true si t1 <= t2 *)
  let rec is_subtype t1 t2 = 
    if t1 = t2 
    then true 
    else match t2 with
	 | TMaybe(t) -> is_subtype t1 t
	 | _ -> false

  let generation_contraintes (env : type_env) (exp:expression) : (CSet.t * typ) =
    let mk_vartyp = mk_cpt() in
    let contraintes = ref CSet.empty in
    let add c = contraintes := CSet.add c (!contraintes) in

    let rec mk_cst (evt:type_env) (exp : expression) : typ =
      match exp with
      | Int _ -> TInt
      | Bool _ -> TBool
      | Unit -> TUnit
      | Var(nom_var) -> Env.find nom_var evt
      | App(f, x)
        -> let type_f = mk_cst evt f in
           let type_x = mk_cst evt x in
           let type_retour = TVar(mk_vartyp()) in
           let c = SubT(TFun(type_x, type_retour), type_f) in
           let _ = add c in
           type_retour
      | Fun(nom_var, e)
        -> let type_param = TVar(mk_vartyp()) in
           let env' = Env.add nom_var type_param env in
           let type_ret = mk_cst env' e in
           TFun(type_param, type_ret)
           
      | Let(s, e1, e2)
        -> let t1 = mk_cst env e1 in
           let evt' = Env.add s t1 evt in
           mk_cst evt' e2
      | Op(s) -> type_operateur mk_vartyp s
      | Pair(e1, e2) -> TPair(mk_cst evt e1, mk_cst evt e2) 
      | Sequence(e1, e2)
        -> let t1 = mk_cst evt e1 in
           let c1 = Eq(t1, TUnit) in
           let _ = add c1 in
           mk_cst evt e2
      | If(c, e1, e2)
        -> let _ = add (Eq(mk_cst evt c, TBool)) in
           let t1 = mk_cst evt e1 in
           let t2 = mk_cst evt e2 in
           let _ = add (Eq(t1, t2)) in
           t1
      | While(c, e)
        ->  let _ = add (Eq(mk_cst evt c, TBool)) in
            let _ = add (Eq(mk_cst evt e, TUnit)) in
            TUnit
            
      | NewRef -> TMaybe(TVar(mk_vartyp()))
    in
    let t = mk_cst env exp in
    (!contraintes, t)

  let cset_map f cset = CSet.fold (fun c cset -> CSet.add (f c) cset) cset CSet.empty 

                
  let substitution typed type_remp t =
    let rec sub t =
      if t = typed
      then type_remp
      else
        match t with
        | TFun(t1, t2) -> TFun(sub t1, sub t2)
        | TPair(t1, t2) -> TPair(sub t1, sub t2)
        | TRef(t) -> TRef(sub t)
        | TMaybe(t) -> TMaybe(sub t)
        | _ -> t
    in sub t
  let c_substitution typed type_remp c =
    match c with
    | Eq(a, b) -> Eq(substitution typed type_remp a, substitution typed type_remp b)
    | SubT(a, b) -> SubT(substitution typed type_remp a, substitution typed type_remp b)
                  
  let rec generalisation t1 t2 =
    if t1 = t2 
    then minim t1
    else if is_subtype t1 t2 
    then minim t2
    else if is_subtype t2 t1 
    then minim t1
    else raise (Bad_type)

  let resolution_contraintes t contraintes =
    let typ = ref t in
    let contraintes = ref contraintes in
    let cset_replace t1 t2 =
      contraintes := cset_map (c_substitution t1 t2) (!contraintes) in
    let typ_replace t1 t2 = t := substitution t1 t2 (!t) in
    let rep t1 t2 = (cset_replace t1 t2; typ_replace t1 t2) in 

    let add c = contraintes := CSet.add c (!contraintes) in
    let del c = contraintes := CSet.remove c (!contraintes) in

    let rec red_cst c =
      let _ = del c in 
      match c with
      | Eq(t1, t2)
        ->
         let t1, t2 = minim t1, minim t2  in 
         if is_subtype t1 t2 
         then cset_replace t1 t2 
         else if is_subtype t2 t1
         then cset_replace t2 t1
         else (  match t1,t2 with
                 | TVar(n), o | o, TVar(n)
                   -> rep t1 o
                    
                 | TMaybe(t1), TMaybe(t2) 
                   | TRef(t1), TRef(t2) -> add (Eq(t1, t2))

                 | TPair(t1a, t1b), TPair(t2a, t2b)
                   | TFun(t1a, t1b), TFun(t2a, t2b)
                   -> let _ = add (Eq(t1a, t2a)) in
                      let _ = add (Eq(t1b, t2b)) in
                      ()
                 | _ -> raise (Bad_type)
              )
      (* t1 doit être un sous type de c2 *)
      | SubT(t1, t2)
        -> let t1, t2 = minim t1, minim t2 in
           if is_subtype t1 t2 then ()
           else
             match t1, t2 with
             | TVar(str_t1), other
               -> ()
            
   
                               


    in ()     
                            
           
    
end 
