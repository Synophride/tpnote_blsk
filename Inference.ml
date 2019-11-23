

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
  exception Bad_type of string 
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
					| Op(s) 
					->(	match s with 
						| "+" 
						-> 	TFun(TInt, TFun(TInt, TInt))
						| "&&" | "||" 
						->	TFun(TBool, TFun(TBool, TBool))
							
						|"=" | "<" | ">" 
						->	TFun(t2, TFun(t2, TBool))
						| "ref" -> Tfun(t2, TRef(t2))
						| "deref" 
						->(	match t2 with 
							|TRef(t) -> Tfun(TRef(t), t) 
							| _ -> failwith "")
						)
							
					_ -> type_expression env e1 
				)
			in (match t1 with 
				| TFun(tparam, tret)
				-> 	if tparam = t2 
					then tret 
					else failwith "meh")
			
	| Fun(nom_var, type_var, term) -> let nouvel_evt = Env.add (nom_var) (type_var) (env) in
                                      let nouveau_type = type_expression nouvel_evt term in
                                      TFun(type_var, nouveau_type)
    | Let(nom_var, e1, e2) -> let type_var = type_expression env e1 in
                              type_expression (Env.add nom_var type_var env) e2
    | Op(op) -> failwith "wtf" 
    | Pair(e1, e2) -> TPair(type_expression env e1, type_expression env e2)
    | NewRef(e) -> TRef(type_expression env e)
    | Sequence(e1, e2) -> let type_e1 = type_expression env e1 in (* type_e1 ?= () *) 
                          type_expression env e2
    | If(cond, e1, e2) -> let f = type_expression env in
                          if f cond <> TBool
                          then raise (Bad_type("condition non booléenne"))
                          else let t1, t2 = f e1, f e2 in
                               if t1 = t2
                               then t1
                               else raise (Bad_type("deux branches du if pas de meme type"))
    | While(c, e) -> let type_c = type_expression env c in
                     if type_c = TBool
                     then let _ = type_expression env e in
                          (* Type_e1 ?= () *)
                          TUnit
                     else raise (Bad_type("Condition non bool dans le while"))
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
  exception Bad_type of string
  module Env = Map.Make(String)
  type type_env = SimpleTypes.typ Env.t 
  type t_contrainte = SimpleTypes.typ * SimpleTypes.typ (* None = Tout type *) 

  module CSet = Set.Make(struct type t = t_contrainte let compare = compare end)

  let type_operateur mk_cpt op =
	match op with 
	| _ -> failwith "pas implémenté" 
  

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
		TFun(ct, TFun(vt, TBool)  	
	| "deref" -> let vt = TVar(fun_cpt()) in TFun(TRef(vt), vt)  
	| "ref" -> let vt = TVar(fun_cpt ()) in TFun(vt, TRef(vt))
	
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
      let get_new_vartyp = mk_cpt_vt () iny
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
                                raise (Bad_type("You have two parts of brain, 'left' and 'right'." ^
                                                  " In the left side, there's nothing right."^
                                                    " In the right side, there's nothing left."))
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
                         | _ -> raise (Bad_type("Your birth certificate is an"^
                                                  " apology letter from the condom factory."))
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


module PTypeChecker = struct
  open DifficultTypes
  open SimpleTypes
  open RawAST

  exception Bad_type of string
  module Env = Map.Make(String)
             
  type evt = DifficultTypes.dtyp Env.t
  type simple_evt = SimpleTypes.typ Env.t

  type contrainte = typ * typ
  module CSet = Set.Make(struct type t = contrainte let compare = compare end)

  let mk_cpt () =
    let x = ref 0 in
    (fun ()
		-> let s = string_of_int !x in
			x := (!x)+1;
			s)
	
  let rec print_contraintes cset =
    CSet.iter (fun (a,b) -> print_string ((str_of_type a) ^ " ?= " ^ (str_of_type b) ^ "\n____\n" )
 
  let type_operateur fun_cpt op =
	match op with 
	| "+" -> TFun(TInt, TFun(TInt, TInt)) 
	| "&&" | "||" -> TFun(TBool, TFun(TBool, TBool))
	| "<" | "=" 
	-> 	let vt = TVar(fun_cpt()) in 
		TFun(ct, TFun(vt, TBool)  	
	| "deref" -> let vt = TVar(fun_cpt()) in TFun(TRef(vt), vt)  
	| "ref" -> let vt = TVar(fun_cpt ()) in TFun(vt, TRef(vt))
	
  let type_expression (env: simple_evt) (e : expression) : typ =
    (* Transition d'un type simple à un type simple, mais de bon type  *)
    let mk_new_str_vartyp = mk_cpt() in
    let gen_st = (fun st -> T(st)) in
    let env' = Env.map (gen_st) (env) in

    let substitution (str_var_a_remplacer, type_remplacant) t =
      let rec sub t = 
        match t with
        | TVar(s) -> if str_var_a_remplacer = s
                     then type_remplacant
                     else t
        | TFun(t1, t2) -> TFun (sub t1, sub t2)
        | TPair(t1, t2)-> TPair(sub t1, sub t2)
        | TRef(t) -> TRef(sub t)
        | _ -> t 
      in
      sub t
    in
    
    let generalisation styp var =
      Forall(var, T(styp))  in
    let specialisation dtyp =      
      let rec spec (liste_substitutions : (string * typ) list) =
        function
        | Forall(str, t2) -> let v = mk_new_str_vartyp() in 
                             spec ((str, TVar(v))::liste_substitutions) t2
        | T(typ) -> List.fold_left
                      (fun t (subst_elt) -> substitution subst_elt t )
                      typ
                      liste_substitutions
      in
      spec [] dtyp 
    in

    
    (***************************************
     *** I . GenEraTiOn dEs CoNtRaiNTeS ****
     ***************************************)
    let generation_contraintes () : (CSet.t * SimpleTypes.typ) =

      let constraints = ref CSet.empty in
      
      let add c = constraints := CSet.add c (!constraints) in
      let rm c = constraints := CSet.remove c (!constraints) in

      let rec gen (env: evt) (e:expression) : typ =
        match e with
        | Int(i) -> TInt
        | Int(_) -> TInt
        | Bool(_)-> TBool
        | Unit -> TUnit
        | Var(nom_var) -> specialisation (Env.find nom_var env)
        | App(e1, e2)
          -> let type_f = gen env e1 in
             let type_param = gen env e2 in
             let type_retour = TVar(mk_new_str_vartyp()) in
             let _ = add (type_f, TFun(type_param, type_retour)) in
             type_retour
        | Fun(str, e)
          -> let vt = mk_new_str_vartyp() in
             let env' = Env.add str (T(TVar(vt))) env in
             TFun(TVar(vt), gen env' e)
        | Let(s, e, e2)
          -> let vt  = mk_new_str_vartyp() in
             let env'= Env.add s (T(TVar(vt))) env in
             let t_e = gen env' e in
             let gen_e = generalisation t_e vt in
             let evt'' = Env.add s gen_e env in
             gen evt'' e2

        | Op(op) -> type_operateur mk_new_str_vartyp op
        | Pair(e1, e2) -> TPair(gen env e1, gen env e2)
        | Newref(e) -> TRef(gen env e)
        | Sequence(e1, e2)
          -> let t_e1, t_e2 = gen env e1, gen env e2 in
             let _ = add (TUnit, t_e1) in
             t_e2
        | If(condition, e1, e2)
          -> let tb = gen env condition in
             let t1 = gen env e1 in
             let t2 = gen env e2 in
             let _ = add (tb, TBool) in 
             let _ = add (t1, t2) in 
             t1
             
        | While(condition, e)
          -> let tb = gen env condition in
             let texp = gen env e in
             let _ = add (tb, TBool) in
             let _ = add (texp, TUnit) in 
             TUnit
      in
      let t = gen env' e in
      (!constraints, t)
    in
    
    let resolution_contraintes cset t_exp =
      (* type de retour *) 
      let t_retour_gen = ref t_exp in 
      (* liste des contraintes à éliminer *) 
      let constraints = ref cset in

      let cset_map f cset = CSet.fold (fun c cset -> CSet.add (f c) cset) cset CSet.empty in
      let constraints_map f = (constraints := cset_map f (!constraints)) in
     
      let rm ct = constraints := CSet.remove ct (!constraints) in
      let add ct = constraints := CSet.add ct (!constraints) in

      
      let rec contains str_var t =
        match t with
        | TVar(str) -> str = str_var
        | TInt | TBool | TUnit -> false
                                
        | TFun(t1, t2) | TPair(t1, t2) -> (contains str_var t1 || contains str_var t2) 
        | TRef(t) -> contains str_var t
      in
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
                              raise (Bad_type("You have two parts of brain, 'left' and 'right'." ^
                                                " In the left side, there's nothing right."^
                                                  " In the right side, there's nothing left."))
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
                       | _ -> raise (Bad_type("Your birth certificate is an"^
                                                " apology letter from the condom factory."))
             in res ()
      in
      let _ = res () in
      (!t_retour_gen)
    in
    let (cset, t) = generation_contraintes () in
    resolution_contraintes cset t
end

(* exo 3 *)

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

  type expression =
    | Int    of int    (** Entier [n]    *)
    | Bool   of bool   (** Booléen [b]   *)
    | Unit             (** Unité [()]    *)
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
     type [T?], on pourra donner à [a] le type [T] dans la branche [e₂].
**)
module SubTypeChecker = struct
  open OptionTypes
  open SubAST
  
  module Env = Map.Make(String)
  type type_env = typ Env.t
  let is_subtype t1 t2 = 
	failwith "to do" 
  let type_expression env expr = 
	let rec t_exp env exp = 
		match exp with 
		| Int(_) -> TInt
		| Bool -> TBool
		| Unit -> TUnit 
		| Var(v) -> Env.find e env 
		| App(e1, e2)
			-> 	let t1 = t_exp env e1 in
				let t2 = t_exp env e2 in 
				let (t_param, t_retour) = 
					match t1 with
					| TFun(tp, tret) -> (tp, tret) 
					| _ -> failwith "eugneu mauvais types" 
					in
				if t_param = t1 || is_subtype t2 t_param 
				then t_retour
				else failwith "Mauvais type"
		| Fun(id, t_param, e) 
			-> 	TFun(t_param, t_exp (Env.add id t_param env)) 
		| Let(id, e1, e2) -> t_exp (Env.add id (t_exp env e1) env) e2  
		| Op(op) -> failwith "pas implémenté" 
		| Pair(e1, e2) -> let f = t_exp env in TPair(f e1, f e2)  
		| NewRef(e) -> TRef(t_exp env e) 
		| Sequence(e1, e2) 
			-> 	let f = t_exp env in 
				let t1, t2 = f e1, f e2 in 
				if t1 = TUnit 
				then t2 
				else failwith "mauvais type" 
		| If(cond, e1, e2)  (*peut-être une exn dans le cas isNull() *)
			->	let f = t_exp env in 
				let tc, t1, t2 = f cond, f e1, f e2 in 
				if tc = TBool && t1 = t2 (* pê prendre le cas de t1 sous-type de t2 *) 
				then t1 
				else failwith "mauvais type"
		| While(cond, e) 
			->	let tc, t = t_exp env cond, t_exp env e in
				if tc = TBool && t = TUnit 
				then TUnit
				else failwith "mal typé" 
		
	in
	failwith "pas implémenté" 
end

