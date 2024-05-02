

type tvar = string


type var = string





type ty =
  | Vari of tvar
  | Impl of ty * ty
  | Conj of ty * ty
  | Truthty
  | Falsety
  | Disj of  ty*ty 
  | Nat
  

type tm =
| Var of var
| App of tm * tm 
| Abs of var*ty*tm 
| Pair of tm * tm
| Fst of tm 
| Snd of tm 
| Truth 
| Left of ty * tm 
| Right of ty * tm 
| Case of tm *var * tm * var * tm 
| PCase of ty * tm 
| Zero
| Succ of tm
| Rec of tm * tm *var*var*tm

type context = (var * ty) list 
type sequent = context * ty


exception Type_error 



let rec eq_ty (type1:ty)(type2:ty) :bool= 
match type1 with 
  |Impl(a,b) -> 
   ( 
    match type2 with
    |Impl(c,d)->( eq_ty a c && eq_ty b d)
    |_ ->(false)
    )
  |Vari a ->
    (
      match type2 with
      |Vari x -> (String.equal x a)
      |_ ->(false)
    )
  |Conj(a,b) ->
  (
    match type2 with
    |Conj(c,d) -> ((eq_ty a c && eq_ty b d) || (eq_ty a d && eq_ty b c))
    |_->(false)
  )
  |Truthty -> 
    (match type2 with 
        |Truthty ->(true)
        |_ -> (false)
    )
  |Disj(a,b)->(match type2 with
  |Disj(c,d)->((eq_ty a c)&&(eq_ty b d) || (eq_ty a d) && (eq_ty b c))
  |_ -> (false)
  )
  |Falsety -> (match type2 with 
  |Falsety->(true)
  |_->(false))
  |Nat ->(
    match type2 with 
    |Nat ->(true)
    |_->(false)
  )
  


let rec string_of_ty = function 
|Vari x -> x 
|Impl(x,y) -> Printf.sprintf ("(%s ⇒ %s)") (string_of_ty x) (string_of_ty y)
|Conj(a,b) -> Printf.sprintf("(%s /\\ %s)") (string_of_ty a) (string_of_ty b)
|Truthty -> "⊤"
|Disj(a,b)-> Printf.sprintf("(%s \\/ %s)") (string_of_ty a) (string_of_ty b)
|Falsety -> "⊥"
|Nat -> "Nat"




(**
let ty = Impl(Impl(Vari("A"), Vari("B")),Impl(Vari("A"), Vari("C")));;

print_endline(string_of_ty ty);;
**)

let rec string_of_tm = function 
|Var x-> x
|App (t, u) -> Printf.sprintf "(%s %s)" (string_of_tm t) (string_of_tm u)
|Abs(x,typ,t) -> Printf.sprintf "(fun : (%s : %s) -> %s)" x (string_of_ty typ) (string_of_tm t)
|Pair(x,y) -> Printf.sprintf "<%s , %s>" (string_of_tm x) (string_of_tm y)
|Fst(x)->("π_l("^string_of_tm x^")")
|Snd(x)->("π_r("^string_of_tm x^")")
    |Truth -> "<>"
|Case(t,x,u,y,v)-> "case("^(string_of_tm t)^","^x^"->"^(string_of_tm u)^","^y^"->"^(string_of_tm v)^")"
|Left(ty, tm) -> "ι_l_"^string_of_ty(ty)^"("^string_of_tm(tm)^")"
|Right(ty, tm) -> "ι_r_"^string_of_ty(ty)^"("^string_of_tm(tm)^")"
|PCase(ty,tm) -> "case_"^string_of_ty(ty)^"("^string_of_tm(tm)^")"
|Succ(tm) -> "Succ"^string_of_tm(tm)
|Zero -> "Zero"
|Rec(t,u,x,y,v) -> "rec("^string_of_tm(t)^","^string_of_tm(u)^","^x^y^"->"^string_of_tm(v)^")"
(**

let type_a_b = Impl(Vari("A"), Vari("B"));;
let type_a = Vari("A");;
l
let test_tm = Abs("f", type_a_b, Abs("x", type_a, App(Var("f"), Var("x"))));;

print_endline(string_of_tm test_tm);;
**)


let rec infer_type (context:context) (tm:tm) = 
  match tm with 
    |Var x -> 
      (
   
        List.assoc x context
        
        
        )
    |App(t,u) ->
    (
     
      match infer_type context t with
      |Impl(a,b)->
        (
          
          try
          
          check_type context u a;
         
          b
          with
          |_-> raise Type_error

        )
      |Truthty ->
        (
        Truthty
        ) 
      |_-> Vari((string_of_tm t)^(string_of_tm u)^"   "^(string_of_ty (infer_type context t)))
    )
    |Abs(x,typ,t) -> 
    (
    
        Impl(typ, infer_type ((x,typ) :: context) t)
    )
    |Pair(x,y)-> Conj(infer_type context x, infer_type context y)
    
    |Fst(x)->(
      match x with 
      |Pair(a,_)-> infer_type context a
      
      |_-> match (infer_type context x) with
        |Conj(t1, _)->(t1)
        |ty -> ty
  
    )
    |Snd(x)->(
      match x with 
      |Pair(_,b)-> infer_type context b
      |_-> match (infer_type context x) with
        |Conj(_, t2)->(t2)
        |ty -> ty
    )
    |Case(t,x,u,y,v)->
      (
        
        match infer_type context t with 
        |Disj(a,b)->
          (
       
          let type1 = infer_type ((x,a)::context) u in
            
            let type2 = infer_type((y,b)::context)v in
    
           
            if(eq_ty type1 type2) then type1 else raise Type_error
            
            )
      
      
            
          
        |_->raise Type_error
      )
      |Right(t,x) -> (Disj(t,infer_type context x))
      |Left(t,x)->(Disj(infer_type context x,t))
    |Truth -> Truthty
    |PCase(t, u) -> (match (infer_type context u) with 
    |Falsety->(t)
    |x -> (
    print_endline("Type du truc dans le case");
    print_endline(string_of_ty x);  
    if( eq_ty x t ) then t else 
      match x with 
      |Disj(a,b)-> (if (eq_ty t a) then a else if (eq_ty t b) then b else (raise Type_error))
      |_->(print_endline("watila");raise Type_error))
      
    )
    |Zero -> (Nat)
    |Succ(tm) -> (
      try
      check_type (context) (tm) Nat;
       Nat
      with
      |_ -> raise Type_error
    )
    |Rec(t,u,x,y,v) ->
      (
        try
        check_type context t Nat;
        let uType = infer_type context u in 
        try
        check_type ((y, uType)::((x,Nat)::context)) v  uType;
        uType
        with 
        |_-> raise Type_error
      with 
      |_->raise Type_error
      )
    and check_type (context:context) (tm:tm) (ty:ty)=
if(eq_ty(infer_type context tm) ty)
then ()
else
  raise Type_error

let () =
print_endline("Prooving A/\\B => B/\\A");;
let and_comm = Abs("x", Conj(Vari("A"), Vari("B")), Pair(Snd(Var("x")), Fst(Var("x"))))
in print_endline(string_of_ty(infer_type [] and_comm));;


let ()=
let truth_implication = Abs("x", Impl(Truthty, Vari("A")), App(Var("x"), Truth))
in 
print_endline("Prooving (T => A )=> A");
print_endline(string_of_ty(infer_type [] truth_implication));;

let () =
let or_comm = Abs("x", Disj(Vari("A"),Vari("B")), Case(Var("x"), "x", Right(Vari("B"), Var("x")), "x",Left(Vari("A"), Var("x"))))
in 
print_endline("Prooving A\\/B => B\\/A");
print_endline(string_of_ty(infer_type [] or_comm));;



let false_fun = Abs("x", Conj(Vari("A"), Impl(Vari("A"), Falsety)), PCase(Vari("B"),App(Snd(Var("x")), Fst(Var("x")))));;
print_endline("Proving A/\\(A=>False)=>B");
print_endline(string_of_ty(infer_type [] false_fun));;


let rec string_of_ctx (context: context) : string = 
  match context with 
  | (var, ty) :: l ->
    (var ^ " : " ^ string_of_ty ty) ^
    (match l with
     | [] -> ""
     | _  -> " , " ^ string_of_ctx l)
  | [] -> ""


let string_of_seq (sequent:sequent) : string = 
match sequent with 
|(context, ty)->((string_of_ctx context)^" |- "^string_of_ty(ty))



(** -------------------------- START OF COPYING (--------------**)
let () = Printexc.record_backtrace true
exception Parse_error
let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error
let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false
let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false
let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error
let lexer = Genlex.make_lexer ["("; ")"; "=>"; "/\\"; "\\/"; "fun"; "->"; ","; ":"; "fst"; "snd"; "T"; "left"; "right"; "not"; "case"; "of"; "|"; "absurd"; "_";"Nat";"Ze"]
let ty_of_tk s =
  let rec ty () = arr ()
  and arr () =
    let a = prod () in
    if peek_kwd s "=>" then Impl(a, arr ()) else a
  and prod () =
    let a = sum () in
    if peek_kwd s "/\\" then Conj(a, prod ()) else a
  and sum () =
    let a = base () in
    if peek_kwd s "\\/" then Disj(a, sum ()) else a
  and base () =
    match Stream.next s with
    | Genlex.Kwd "Nat" -> Nat
    | Genlex.Ident x -> Vari x
    
    | Genlex.Kwd "(" ->
       let a = ty () in
       must_kwd s ")";
       a
    | Genlex.Kwd "T" -> Truthty
    | Genlex.Kwd "_" -> Falsety
    | Genlex.Kwd "not" ->
       let a = base () in
       Impl(a, Falsety)
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
        let x = ident s in
        must_kwd s "->";
        let u = tm () in
        must_kwd s "|";
        let y = ident s in
        must_kwd s "->";
        let v = tm () in
        Case (t, x, u, y, v)
      )
    else
      base ()
  and base () =
    match Stream.next s with

     
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "Ze" -> Zero
    | Genlex.Kwd "(" ->
       if peek_kwd s ")" then
         Truth
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
       Fst t
    | Genlex.Kwd "snd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Snd t
    | Genlex.Kwd "left" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let b = ty () in
       must_kwd s ")";
       Left (b, t)
    | Genlex.Kwd "right" ->
       must_kwd s "(";
       let a = ty () in
       must_kwd s ",";
       let t = tm () in
       must_kwd s ")";
       Right (a, t)
    | Genlex.Kwd "absurd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let a = ty () in
       must_kwd s ")";
       PCase (a, t)
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
      "not A";
      "Nat => Nat";
      
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
      "absurd(t,A)";
      "Ze"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))) l

(**Start of prover**)
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
      match arg with
      |"()"->(prove (("truth", Truthty)::env) a)
      |"Zero"->(prove(("Ze", Nat)::env)a)
      |_->(
       match a with
       | Impl(a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b in
            Abs (x, a, t)
       | Conj(a,b)->(
          Pair(prove env a, prove env b))
        |_->(
      
            let x = arg in let typcont = List.assoc x env in 
            match typcont with 

            |Nat -> (Succ(prove((arg, Nat)::env) a))
            |_ ->(
          error "Don't know how to introduce this.")))
     )
 
  | "exact" ->
     let t = tm_of_string arg in
     print_endline(string_of_tm t);
     if infer_type env t <> a then error "Not the right type."
     else t
  | "elim"->(
    let x = arg 
  in let typcont = List.assoc x env in
  match typcont with 
    |Impl(e,f)->(
      if eq_ty f a then let t = prove env e in 
      App(Var(x), t)
      else error "Can't eliminate this"
    )
    |Disj(aT,bT)->(
      
      Case(Var(x), x ,prove ((x,aT)::env) a, x, (prove ((x,bT)::env) a))
      )
    |Falsety ->
      (
        PCase(a, Var(x));
      )
      |Nat -> (
      
        (* Introduce the base case *)
        let base_case_name = "BC_" ^ x in
        let base_case_type = a in
        let env_with_base_case = (base_case_name, base_case_type) :: env in
        let base_case_proof = prove env_with_base_case a in

          (* Introduce the induction hypothesis *)
        let ih_name = "x_" ^ x in
        let env_with_ih = (ih_name, Nat) :: env in
        let yh= "y_" ^ x in
        let env_with_ind_step = (yh, a) :: env_with_ih in
        let e_s = prove env_with_ind_step a in

        (* Use nat_rect to eliminate the natural number *)
      Rec(Var(x), base_case_proof, ih_name, yh, e_s)

      )
    |_-> 
      error "Don't know how to eliminate this"

    
    
  )
  |"cut"->
    (
      let formula = ty_of_string arg in
      let f1 = prove env (Impl(formula, a)) in 
      let f2 = prove env formula in 
    App(f1,f2)
    )
    | "fst"->(
      let x = arg 
      in let typcont = List.assoc x env in 
      match typcont with 
      |Conj(first, _)->
        (
            if first <> a then Fst(prove ((x,first)::env) a)
            else
              Fst(Var(x))
        )
      |_->(error "Not a conjction"))
  | "snd"->(
        let x = arg 
        in let typcont = List.assoc x env in 
        match typcont with 
        |Conj(_,snd)->
          (
              if snd <> a then Snd(prove ((x,snd)::env) a)
              else
                Snd(Var(x))
          )
        |_->(error "Not a conjunction"))
  |"left" ->(
    match a with 
    |Disj(a,b)->(Left(b, prove env a))
    |_->error"not a disjunction"
  )
  |"right" ->(
    match a with 
    |Disj(a,b)->(Right(a, prove env b))
    |_->error"not a disjunction"
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
  print_endline(string_of_ty(infer_type [] t));
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok."



