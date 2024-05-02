type var = string

type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr 
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

let rec to_string expr = match expr with 
|Var x -> x
|Abs(x, t, y) -> Printf.sprintf "fun (%s : %s) -> %s" x(to_string t)(to_string y)
|Type -> "Type"
|App (t, u) -> Printf.sprintf "(%s %s)" (to_string t) (to_string u)
|Pi(x, u,v)-> Printf.sprintf "Pi (%s : %s) -> %s" x (to_string u) (to_string v )
|Nat -> "Nat"
|Z -> "Z"
|S(t) -> "S("^to_string t^")"
|Ind(p,z,s,n) -> Printf.sprintf "Ind %s %s %s %s" (to_string p) (to_string z) (to_string s)(to_string n)
|Eq(t,u) -> Printf.sprintf "Eq %s %s" (to_string t)(to_string u)
|Refl(t) -> Printf.sprintf "Refl %s"(to_string t)
|J(a,b,c,d,e) -> Printf.sprintf "J %s %s %s %s %s" (to_string a)(to_string b)(to_string c)(to_string d)(to_string e)

let fresh_var =
  let counter = ref 0 in
  fun () ->
    counter := !counter + 1;
    "x" ^ string_of_int !counter
;;

(* fun (x:A) => A*)
(* Abs(x, A, x)*)
(* On substitue A par bool *)
(* Ici A = x t = Bool *)
let rec has_fv x = function
  | Var y -> y = x
  | App (t, u) -> has_fv x t || has_fv x u
  | Abs (y, _, t) -> x <> y && has_fv x t
  |_ ->(false)
let rec subst x t u =
  
  match u with 
  | Var y -> if x = y then t else Var y
  | App (u, v) -> App (subst x t u, subst x t v)
  | Abs (y, yType, u) ->
     if x = y then Abs (y, subst x t yType, u)
     else if not (has_fv y t) then Abs (y,subst x t yType, subst x t u)
     else
       let y' = fresh_var () in
       subst x t (Abs (y', subst x t yType, subst y (Var y') u))
  |Pi (y, yType, u) ->
        if x = y then Pi (y, subst x t yType, u)
        else if not (has_fv y t) then (Pi (y,subst x t yType, subst x t u))
        else
          
          let y' = fresh_var () in
        
          subst x t (Pi (y', subst x t yType, subst y (Var y') u))
  |Nat -> (u)
  |Eq(n,m)->Eq(subst x t n, subst x t m)
  |S(Var(d)) ->(if x=d then S(t) else u)
  |S(_) -> (u)
  |J(a,b,c,d,e)->(J(subst x t a, subst x t b, subst x t c, subst x t d, subst x t e))
  |Z -> Z
  |Ind(p,z,s,n) -> Ind(subst x t p, subst x t z, subst x t s, subst x t n)
  |Type -> Type 
  |Refl(n)->Refl(subst x t n)
  


type context = (var * (expr*expr option)) list 

let rec string_of_context cont = 
let socAux head = 
  match head with 
  |(var, infos) -> 
    (
  match infos with
  |(types, None)-> (var ^" : "^to_string types )
  |(types, Some(value)) ->(var^" : "^to_string types^" = "^to_string value)
  
  )
in 
  match cont with 
  |[] -> ""
  |head::rest ->((socAux head)^","^(string_of_context rest))


let rec red (context:context) = function
  | Var x -> (
    try
      let infos = 
        List.assoc x context in 
      match infos with 
      |(_, Some(valeur)) ->(Some valeur)
      |(_, None)->(None)
      with 
      |_ -> None
  )
  | App (Abs (x,_,t), u) ->
    (
      
      Some (subst x u t)
      )
  | App(Pi(x,_,t), u) -> (Some(subst x u t ))
  | App (t, u) ->
     (
       match red context t with
       | Some t' -> Some (App (t', u))
       | None ->
          match red context u with
          | Some u' -> Some (App (t, u'))
          | None -> None
     )
  | Abs (x, xType,t) ->
     (
       match red context t with
       | Some t' ->
        (match red context xType with
        |Some ntype -> (Some(Abs(x,ntype, t')))
        |None ->(Some(Abs(x,xType, t')))
        )
        
       | None -> (
        (match red context xType with
        |Some ntype -> (Some(Abs(x,ntype, t)))
        |None ->(None)
        )
       )
     )
  | Pi (x, tX, v) -> (
    match red context tX with 
  |Some ntype -> (match red context v with 
  |Some(vred)-> Some(Pi(x, ntype, vred))
  |None -> Some(Pi(x, ntype, v)))

  |None ->(
    match red context v with 
  |Some(vred)-> Some(Pi(x, tX, vred))
  |None -> None
  )
  )
  | Ind(_,z,_,Z) -> (Some(z))
  | Ind(p,z,s,S(n)) ->(Some(App(App(s,n),Ind(p,z,s,n))))
  | Ind(p,_,_,n) ->(Some(App(p,n)))
  | Nat -> (None)
  
  |Z ->(None)
  |S(m) ->(match red context m with 
  |None -> (None)
  |Some(term) -> (Some(S(term)))
  )
  |Type -> (None)
  |J(_,r,x,d,Refl(e)) when x =d&& x=e ->
    (
      
      Some(App(r,x))
    )


  |J(p,_,x,y,e) -> (Some(App(App(App(p,x),y),e)))
  |_-> (None)
    

let rec normalize  (context:context) t =
      match red (context:context) t with
      | Some t' ->(normalize context t')
      | None -> t


let alpha t u = 
  let rec aux s t u =
  match t, u with 
  Var x, Var y -> 
  (if x = y then true else if not (List.mem_assoc x s) then false else List.assoc x s = y
  )
  |App(t,u), App(t',u') -> 
  (
    aux s t t' && aux s u u' 
  )
  |Abs(x,xType,t), Abs(y,yType,u)->
    aux((x,y)::s) t u && aux((x,y)::s) xType yType
  |Type, Type -> (true)
  |Pi(x,xType,t), Pi(y,yType,v)->
    (
      

      let v1 = aux((x,y)::s) xType yType in 
      let v2 = aux ((x,y)::s) t v  in

      v1 && v2
    )
  |Nat, Nat -> (true)
  |Z, Z -> (true)
  |S(_),S(_) ->(true)
  |Eq(x,y), Eq(a,b)->((aux s x a && aux s y b)||(aux s x b && aux s y a))
  |_,_ -> (
    
  false)
in aux [] t u 
  
let conv context t u  = 

alpha (normalize context t)(normalize context u)

exception Type_error;;



let rec infer (context:context) expr =
  match normalize context expr with 
  |Var x -> (let typv = List.assoc x context in 
  match typv with 
  (typ,_) ->(typ))
  |App(t,u)-> (
    
    match t with 
    |Abs(x,_,v)->
    (
      infer context (subst x u v)
      )
    |Pi(x,_,endType) -> infer context (subst x  u endType)
    |Var _ -> (u)
    |Z -> (u)
    |_->raise Type_error;
    
  )
  |Abs(x,xType, v)-> Pi(x, xType,infer ((x, (xType,None))::context) v)
  |Type -> Type
  |Pi(_,_,_) -> Type
  |Nat -> Nat 
  |Z -> Nat
  |S(_) -> Nat 
  |Eq(x,y)-> Eq(x,y)
  |Refl(x) -> Refl(x)
  |J(_,_,_,_,_) -> Type
  |Ind(_,_,_,_) -> Type 
 


let check (context:context) expr1 expr2 =

  let expr1Type = (infer context expr1) in 
  let bool = conv context expr1Type expr2   in 
  

  match bool with 
  |true -> ()
  |false -> (raise Type_error)
 

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