type var = string

type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  (* forget about the constructors below at first *)
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr 
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

let rec to_string : expr -> string = function 
  | Type -> "Type"
  | Var x -> x
  | App (t, u) -> Printf.sprintf "(%s %s)" (to_string t) (to_string u)
  | Abs (x, a, t) -> Printf.sprintf "(λ(%s:%s).%s)" x (to_string a)(to_string t)
  | Pi (x, a, b) -> Printf.sprintf "(π(%s:%s).%s)" x (to_string a)(to_string b)
  | Nat -> "Nat"
  | Z -> "Z"
  | S n -> Printf.sprintf "S(%s)" (to_string n)
  | Ind (a, m, n, t) -> Printf.sprintf "Ind(%s,%s,%s,%s)"
    (to_string a) (to_string m) (to_string n) (to_string t)
  | Eq (a, b) -> Printf.sprintf "Eq(%s,%s)" (to_string a) (to_string b)
  | Refl a -> Printf.sprintf "Refl(%s)" (to_string a)
  | J (a, b, c, d, e) -> Printf.sprintf "J(%s,%s,%s,%s,%s)" (to_string a) (to_string b) (to_string c) (to_string d) (to_string e)

let fresh_var =
  let n = ref 0 in
  function () ->
  n := !n + 1;
  "x" ^ string_of_int !n
  
let rec subst x t = function
  | Type -> Type
  | Var y -> if x = y then t else Var y
  | App (t1, t2) -> App (subst x t t1,subst x t t2)
  | Abs (y,ty,tm) -> 
    let z = fresh_var () in 
    Abs (z,subst x t ty, subst x t (subst y (Var z) tm))
  | Pi (y, u, v) -> 
    let z = fresh_var () in 
    Pi (z, subst x t u, subst x t (subst y (Var z) v))
  | Nat -> Nat
  | Z -> Z
  | S tm -> S (subst x t tm)
  | Ind (a, m, n, tm) -> Ind (subst x t a, subst x t m, subst x t n, subst x t tm)
  | Eq (tm1, tm2) -> Eq (subst x t tm1, subst x t tm2)
  | Refl tm -> Refl (subst x t tm)
  | J (p, r, a, b, e) -> J (subst x t p, subst x t r, subst x t a, subst x t b, subst x t e)

type context = (var * (expr * expr option)) list

let rec string_of_context = function
    | [] -> ""
    | [(x, (t, None))] -> x ^ " : " ^(to_string t)
    | [(x, (t, Some u))] -> x ^ " : " ^(to_string t) ^ " = " ^(to_string u)
    | (x, (t, None)) :: context -> string_of_context(context) ^ ", " ^ x ^ " : " ^(to_string t)
    | (x, (t, Some u)) :: context -> 
      string_of_context(context) ^ ", " ^ x ^ " : " ^(to_string t) ^ " = " ^(to_string u) 

(* 5.6 Normalization *)
let rec normalize context = function
    | Type -> Type
    | Var x -> (
        try match snd (List.assoc x context) with
          | Some tm -> normalize context tm
          | None -> Var x
        with Not_found -> Var x
    )
    | App (t1, t2) -> 
      (
        match normalize context t1 with
        | Abs (x, ty, t) -> 
          let t2 = normalize context t2 in
          normalize context (subst x t2 t)
        | t -> App (normalize context t, normalize context t2)
      )
    | Abs (x, t, u) -> let t = normalize context t in Abs (x, normalize context t, normalize ((x,(t,None))::context) u)
    | Pi (x, t, u) -> Pi (x, normalize context t, normalize context u)
    | Nat -> Nat
    | Z -> Z
    | S t -> S (normalize context t)
    | Ind (p, z, s, n) ->
      (
        match normalize context n with
        | Z -> normalize context z
        | S n -> 
          let s = normalize context s in
          normalize context (App (App (s,n),Ind (normalize context p,normalize context z,s,n)))
        | n -> Ind (normalize context p, normalize context z, normalize context s, n)
      ) 
    | Eq (t, u) -> Eq (normalize context t, normalize context u)
    | Refl t -> Refl (normalize context t)
    | J (p, r, x, y, e) ->
      (
        match normalize context e with 
        | Refl a when x = a && y = a -> normalize context (App (r, a))
        | e -> J (normalize context p, normalize context r, normalize context x, normalize context y, e)
      )
(* 5.7 α-conversion *)
let alpha = 
  let rec aux context u v = match u, v with
    | Type, Type -> true
    | Var x, Var y -> 
      let rec correspond x y = function
        | [] -> x = y
        | (a, b)::t -> if a = x then b = y else (b <> y && correspond x y t)
      in correspond x y context 
    | App (u1, u2), App (v1, v2) -> aux context u1 v1 && aux context u2 v2
    | Abs (x, ty1, t1), Abs (y, ty2, t2) -> aux context ty1 ty2 && aux ((x,y)::context) t1 t2
    | Pi (x, a1, b1), Pi(y, a2, b2) -> aux context a1 a2 && aux ((x,y)::context) b1 b2
    | Nat, Nat -> true
    | Z, Z -> true
    | S t, S u -> aux context t u
    | Ind (p, z, s, n), Ind (q, w, r, m) -> (aux context p q && aux context z w && aux context s r && aux context n m)
    | Eq (t1, u1), Eq (t2, u2) -> aux context t1 t2 && aux context u1 u2
    | Refl t, Refl u -> aux context t u
    | J (p, r, x, y, e), J (q, s, a, b, f) -> (aux context p q && aux context r s && aux context x a && aux context y b && aux context e f)
    |_ -> false

  in aux []


(* 5.8 Conversion *)
let conv context t1 t2 = alpha (normalize context t1) (normalize context t2)

(* 5.9 Type inference *)
exception Type_error

let rec infer context = function
  | Type -> Type
  | Var x -> (try fst (List.assoc x context) with Not_found -> raise Type_error)
  | App (t1, t2) -> 
    (
      let u = infer context t2 in 
      match infer context t1 with 
      | Pi (x, a, b) -> 
        if conv context a u then ((subst x t2 b))
        else raise Type_error
      | _ -> raise Type_error
    )
  | Abs (x, t, u) -> Pi (x, t, infer ((x, (t,None))::context) u)
  | Pi _ -> Type
  | Nat -> Type
  | Z -> Nat
  | S t -> if conv context (infer context t) Nat then Nat else raise Type_error
  | Ind (p, z, s, n) -> normalize context (App (p,n)) 
  | Eq (_, _) -> Type
  | Refl t -> Eq (t, t)
  | J (p, r, x, y, e) -> normalize context (App (App (App (p, x), y), e))
(* 5.10 Type checking *)
let check context u t = if not (conv context (infer context u) t) then raise Type_error

(* 5.11 Interaction loop *)
(** Parsing of expressions. *)
let () = Printexc.record_backtrace true
exception Parse_error
let lexer = Genlex.make_lexer ["("; ","; ")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type"; "Nat"; "Z"; "S"; "Ind"; "Eq"; "Refl"; "J"]
let of_tk s =
  let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error in
  let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false in
  let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false in
  let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error in
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type"] in
  let rec e () = abs ()
  and abs () =
    if peek_kwd s "Pi" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let b = e () in
        Pi (x, a, b)
      )
    else if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let t = e () in
        Abs (x, a, t)
      )
    else
      app ()
  and app () =
    let t = ref (arr ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, base ())
    done;
    !t
  and arr () =
    let t = base () in
    if peek_kwd s "=>" then
      let u = e () in
      Pi ("_", t, u)
    else
      t
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "Type" -> Type
    | Genlex.Kwd "Nat" -> Nat
    | Genlex.Kwd "Z" -> Z
    | Genlex.Kwd "S" ->
       let t = base () in
       S t
    | Genlex.Kwd "Ind" ->
       let p = base () in
       let z = base () in
       let ps = base () in
       let n = base () in
       Ind (p, z, ps, n)
    | Genlex.Kwd "Eq" ->
       let t = base () in
       let u = base () in
       Eq (t, u)
    | Genlex.Kwd "Refl" ->
       let t = base () in
       Refl t
    | Genlex.Kwd "J" ->
       let p = base () in
       let r = base () in
       let x = base () in
       let y = base () in
       let e = base () in
       J (p, r, x, y, e)
    | Genlex.Kwd "(" ->
       let t = e () in
       must_kwd s ")";
       t
    | _ -> raise Parse_error
  in
  e ()
let of_string a = of_tk (lexer (Stream.of_string a))

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
         let x, sa = split ':' arg in
         let a = of_string sa in
         check !env a Type;
         env := (x,(a,None)) :: !env;
         print_endline (x^" assumed of type "^to_string a)
      | "define" ->
         let x, st = split '=' arg in
         let t = of_string st in
         let a = infer !env t in
         env := (x,(a,Some t)) :: !env;
         print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
         print_endline (string_of_context !env)
      | "type" -> 
         let t = of_string arg in
         let a = infer !env t in
         print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
         let t, a = split '=' arg in
         let t = of_string t in
         let a = of_string a in
         check !env t a;
         print_endline "Ok."
      | "eval" ->
         let t = of_string arg in
         let _ = infer !env t in
         print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
 (* | e -> print_endline ("Error: "^Printexc.to_string e) *)
  done;
  print_endline "Bye."

