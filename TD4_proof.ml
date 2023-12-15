(* Question 1: Type inference for a simply typed calculus *)

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string


(* 1.1: simple types *)

type ty = 
  | TyVar of tvar
  | TyArr of ty * ty
  | TyProd of ty * ty
  | TyCoprod of ty * ty
  | TyEmpty 
  | TyUnit 
  | Nat 
(* 1.2: λ-terms *)
type tm = 
  | Var of var
  | Abs of var * ty * tm
  | App of tm * tm
  | Pair of tm * tm
  | PrjL of tm
  | PrjR of tm 
  | Unit 
  | Zero 
  | Fst of ty * tm
  | Snd of ty * tm
  | Case of tm * tm * tm
  | Case_ of ty * tm
  | NatZero 
  | NatSucc of tm
  | NatRec of tm * tm * var * var * tm 
(* 1.3: String representation *)

(* string representation of a type *)
let rec string_of_ty = function 
  | TyVar x -> x
  | TyArr (x, y) -> Printf.sprintf "(%s => %s)" (string_of_ty x) (string_of_ty y)
  | TyProd (x, y) -> Printf.sprintf "(%s /\\ %s)" (string_of_ty x) (string_of_ty y)
  | TyCoprod (x, y) -> Printf.sprintf "(%s \\/ %s)" (string_of_ty x) (string_of_ty y)
  | TyEmpty -> Printf.sprintf("false")
  | TyUnit -> Printf.sprintf("true")
  | Nat -> Printf.sprintf("Nat")

(*  string representation of a term. *)
let rec string_of_tm = function 
  | Var x -> x
  | App (t, u) -> Printf.sprintf "(%s %s)" (string_of_tm t) (string_of_tm u)
  | Abs (x, a, t) -> Printf.sprintf "(λ(%s:%s).%s)" x (string_of_ty a)(string_of_tm t)
  | Pair (t1, t2) -> Printf.sprintf "(%s,%s)" (string_of_tm t1) (string_of_tm t2)
  | PrjL t -> Printf.sprintf "(π_l %s)" (string_of_tm t)
  | PrjR t -> Printf.sprintf "(π_r %s)" (string_of_tm t)
  | Unit -> Printf.sprintf "()"
  | Zero -> Printf.sprintf "0"
  | Fst (t, u) -> Printf.sprintf "(i_l %s %s)" (string_of_ty t) (string_of_tm u)
  | Snd (t, u) -> Printf.sprintf "(i_r %s %s)" (string_of_ty t) (string_of_tm u)
  | Case (t, u, v) -> Printf.sprintf "(case %s, %s, %s)" (string_of_tm t) (string_of_tm u) (string_of_tm v)
  | Case_ (t, u) -> Printf.sprintf "(case %s, %s)" (string_of_ty t) (string_of_tm u)
  | NatSucc t-> Printf.sprintf "(succ %s)" (string_of_tm t)
  | NatRec (t, u, a, b, v) -> Printf.sprintf "rec (%s, %s, %s, %s, %s)" (string_of_tm t) (string_of_tm u) 
                          (a) (b) (string_of_tm v)
  | NatZero -> Printf.sprintf "0"
  

                                                           

(* 1.4: Type inference *)

(* a type for typing contexts *)
type context = (var * ty) list

(* exception *)
exception Type_error 

(* infers the type of a term t in a given context Γ *)
let rec infer env = function 
  | Var x -> (try (List.assoc x env) with Not_found -> raise Type_error)
  | Abs (x, a, t) -> TyArr (a, (infer ((x, a)::env) t))
  | App (t, u) -> 
    (match infer env t with  
    | TyArr (a, b) -> check env u a; b
    | _ -> raise Type_error
    )
  | Pair (t, u) -> TyProd (infer env t, infer env u)
  | PrjL t -> (match infer env t with TyProd (a, b) -> a | _ -> raise Type_error)
  | PrjR t -> (match infer env t with TyProd (a, b) -> b | _ -> raise Type_error)
  | Unit -> TyUnit
  | Zero -> TyEmpty
  | Fst (t, u) -> (match infer env u with a -> TyCoprod (a, t))
  | Snd (t, u) -> (match infer env u with b -> TyCoprod (t, b))
  | Case (t, u, v) -> 
    (match infer env t with 
      | TyCoprod (a, b) -> 
        (
        match infer env u with
          | TyArr (a, c) ->
            (
              match infer env v with
              | TyArr (b, c) -> c
              | _ -> raise Type_error
            )
          | _ -> raise Type_error
        )
      | _ -> raise Type_error
    )
  | Case_  (t, u) -> t 
  | NatZero -> Nat
  | NatSucc (t) -> if infer env t = Nat then Nat else raise Type_error
  | NatRec (t, u, a, b, v) -> 
    let ty = infer env u in
    (
      check env t Nat;
      check ((a,Nat)::(b,ty)::env) t ty;
      ty
    )
(* 1.5, 1.6: Type checking and mutual recursive implementation*)
(*  checks whether a term has a given type *)
  and check env t a =
    if infer env t <> a then raise Type_error

(* 1.7: Other connectives *)

(* 1.8: Conjunction *)
let and_comm =  Abs ("x",TyProd(TyVar "A", TyVar "B"), Pair(PrjR(Var "x"), PrjL (Var "x")))

let () = print_endline (string_of_ty (infer [] and_comm))

(* 1.9: Truth *)
let truth = Abs ("x", TyArr(TyUnit, TyVar "A"), App(Var "x", Unit))
let () = print_endline (string_of_ty (infer [] truth))

(* 1.10:  Disjunction*)
let disjuction = Abs ("x", TyCoprod(TyVar "A", TyVar "B"), 
                Case (Var "x", Abs ("u", TyVar "A", Snd(TyVar "B", Var "u")), 
                Abs ("v", TyVar "B", Fst(TyVar "A", Var "v"))))
let () = print_endline (string_of_ty (infer [] disjuction))
(* Result:  ((A + B) => (B + A)) *)

(* 1.11: Falsity *)
let falsity = Abs ("x", TyProd(TyVar "A", TyArr (TyVar "A", TyEmpty)), Case_ (TyVar "B", App(PrjR (Var "x"), PrjL (Var "x"))))
let () = print_endline (string_of_ty (infer [] falsity))
(* Result: ((A /\ (A => false)) => B) *)

(* 1.12: Parsing strings *)

let () = Printexc.record_backtrace true
exception Parse_error
let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error
let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false
let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false
let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error
let lexer = Genlex.make_lexer ["("; ")"; "=>"; "/\\"; "\\/"; "fun"; "->"; ","; ":"; "fst"; "snd"; "T"; "left"; "right"; "not"; "case"; "of"; "|"; "absurd"; "_"; "Nat";"succ";"rec"; "0"]
let ty_of_tk s =
  let rec ty () = arr ()
  and arr () =
    let a = prod () in
    if peek_kwd s "=>" then TyArr (a, arr ()) else a
  and prod () =
    let a = sum () in
    if peek_kwd s "/\\" then TyProd (a, prod ()) else a
  and sum () =
    let a = base () in
    if peek_kwd s "\\/" then TyCoprod (a, sum ()) else a
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> TyVar x
    | Genlex.Kwd "(" ->
       let a = ty () in
       must_kwd s ")";
       a
    | Genlex.Kwd "T" -> TyUnit
    | Genlex.Kwd "_" -> TyEmpty
    | Genlex.Kwd "not" ->
       let a = base () in
       TyArr (a, TyEmpty)
    | _ -> raise Parse_error
  in
  ty ()
let tm_of_tk s =
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; ","; "case"; "fun"; "of"; "->"; "|"] in
  let ty () = ty_of_tk s in
  let rec tm () = app ()
  and app () =
    let t = ref (abs ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, abs ())
    done;
    !t
  and abs () =
    if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = ty () in
        must_kwd s ")";
        must_kwd s "->";
        let t = tm () in
        Abs (x, a, t)
      )
    else if peek_kwd s "case" then
      (
        let t = tm () in
        must_kwd s "of";
        let _ = ident s in
        must_kwd s "->";
        let u = tm () in
        must_kwd s "|";
        let _ = ident s in
        must_kwd s "->";
        let v = tm () in
        Case (t, u, v)
      )
    else
      base ()
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "0" -> Zero
    | Genlex.Kwd "(" ->
       if peek_kwd s ")" then
         Unit
       else
         let t = tm () in
         if peek_kwd s "," then
           let u = tm () in
           must_kwd s ")";
           Pair (t, u)
         else
           (
             must_kwd s ")";
             t
           )
    | Genlex.Kwd "fst" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       PrjL t
    | Genlex.Kwd "snd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       PrjR t
    | Genlex.Kwd "left" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let b = ty () in
       must_kwd s ")";
       Fst (b, t)
    | Genlex.Kwd "right" ->
       must_kwd s "(";
       let a = ty () in
       must_kwd s ",";
       let t = tm () in
       must_kwd s ")";
       Snd (a, t)
    | Genlex.Kwd "absurd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let a = ty () in
       must_kwd s ")";
       Case_ (a, t)
    | Genlex.Kwd "succ" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ")";
        Succ t
    | Genlex.Kwd "rec" ->
        must_kwd s "(";
        let n = tm () in
        must_kwd s ",";
        let z = tm () in
        must_kwd s ",";
        let x = ident s in
        let y = ident s in
        must_kwd s "->";
        let s = tm () in
        Rec (n,z,x,y,s)
    | _ -> raise Parse_error
  in
  tm ()
let ty_of_string a = ty_of_tk (lexer (Stream.of_string a))
let tm_of_string t = tm_of_tk (lexer (Stream.of_string t))
let () =
  let l = [
      "A => B";
      "A /\\ B";
      "T";
      "A \\/ B";
      "_";
      "not A"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))) l
  let () =
  let l = [
      "t u";
      "fun (x : A) -> t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))) l

(* 2.  Interactive prover *)

(* 2.1 String representation of contexts *)

let rec string_of_ctx ctx =
	match ctx with
	| [] 			-> ""
	| [(x, a)] 		-> x ^ " : " ^(string_of_ty a)
	| (x, a) :: l	-> (string_of_ctx l) ^ " , " ^ x ^ " : " ^ (string_of_ty a);;

(* Test *)
let () =
	let x = [("x", TyArr(TyVar "A", TyVar "B"));("y", TyProd (TyVar "A", TyVar "B"));("Z", TyVar "T")] in
	print_endline (string_of_ctx x);;

(* 2.2 Sequent *)
type sequent = context * ty

let string_of_seq = function (c, t) -> string_of_ctx c ^ " |- " ^ string_of_ty t

(* Test *)
let () = 
  let y = ([("x", TyArr(TyVar "A", TyVar "B"));("y", TyVar "B")]) in 
  let x = (y, TyVar "B") in
  print_endline (string_of_seq x);;

(* 2.3 An interactive prover *)
let rec prove env a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
     (
       match a with
       | TyArr (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b in
            Abs (x, a, t)
       | TyProd (a, b) ->
          if arg = "" then 
            let t1 = prove env a in
            let t2 = prove env b in
            Pair (t1, t2)
          else error "Wrong command for conjunction"
       | TyUnit -> Unit
       | Nat -> 
          if arg = "zero" then 
            Zero 
          else if arg = "succ" then
            let t = prove env Nat in
            NatSucc t 
          else error "Wrong command for natural numbers"
       | _ ->
          error "Don't know how to introduce this."
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer env t <> a then error "Not the right type."
     else (
      t
     )
  | "elim" ->
      (
        if arg = "" then error "Please provide an argument for elim." else (
          match (List.assoc arg env) with
          | TyArr (u, v) -> if v = a then let t = prove env u in App (Var arg, t)
            else error "Don't know how to eliminate this."
          | TyCoprod (u, v) -> let t1 = prove ((arg, u) :: env) a in 
                               let t2 = prove ((arg, v) :: env) a in 
                               Case (Var arg, Abs(arg, u, t1), Abs(arg, v, t2))
          | TyEmpty -> Case_ (a, Var arg)
          | _ 					-> error "Don't know how to eliminate this."
        )
        
      )
  | "cut" -> 
    if arg = "" then error "Please provide an argument for cut." 
    else
      let t = ty_of_string arg in
      let u = prove env (TyArr (t, a)) in
      let v = prove env t in 
      App (u,v)
  | "fst" -> 
    if arg = "" then error "Please provide an argument for fst."
    else (
      match (List.assoc arg env) with 
      | TyProd (u, v) when u = a -> PrjL(Var arg)
      | _ -> error "Don't know how to fst this."
    )
  | "snd" -> 
    if arg = "" then error "Please provide an argument for snd."
    else (
      match (List.assoc arg env) with 
      | TyProd (u, v) when v = a -> PrjR(Var arg)
      | _ -> error "Don't know how to snd this."
    )    
  | "left" ->
    if arg <> "" then error "Wrong command for the left."
    else (
      match a with 
      | TyCoprod (u, v) -> let x = prove env u in Fst(v, x)
      | _ -> error "Don't know how to left this."
    )
  | "right" ->
    if arg <> "" then error "Wrong command for the right."
    else (
      match a with
      | TyCoprod (u, v) -> let x = prove env v in Snd(u, x)
      | _ -> error "Don't know how to right this."
    )
  | cmd -> error ("Unknown command: " ^ cmd)
  
let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer [] t = a);
  print_endline "ok."