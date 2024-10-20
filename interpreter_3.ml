(* part3 template *)
type name = string

type term =
  (* lambda calculus *)
  | Name of name
  | Fun of name * name * term
  | App of term * term
  (* extensions *)
  | Ifgz  of term * term * term
  | LetIn of name * term * term
  | Unit
  | Int of int 
  | Add of term * term
  | Sub of term * term
  | Mul of term * term
  | Div of term * term
  | Trace of term

(* parser for term language *)

(* util functions *)

let is_lower_case c =
  'a' <= c && c <= 'z'

let is_upper_case c =
  'A' <= c && c <= 'Z'

let is_alpha c =
  is_lower_case c || is_upper_case c

let is_digit c =
  '0' <= c && c <= '9'

let is_alphanum c =
  is_lower_case c ||
  is_upper_case c ||
  is_digit c

let is_blank c =
  String.contains " \012\n\r\t" c

let explode s =
  List.of_seq (String.to_seq s)

let implode ls =
  String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ (loop ())
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

(* end of util functions *)

(* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option =
  p (explode s)

let pure (x : 'a) : 'a parser =
  fun ls -> Some (x, ls)

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
  fun ls ->
    match p ls with
    | Some (a, ls) -> q a ls
    | None -> None

let (>>=) = bind
let (let*) = bind

let read : char parser =
  fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

let satisfy (f : char -> bool) : char parser =
  fun ls ->
  match ls with
  | x :: ls ->
    if f x then Some (x, ls)
    else None
  | _ -> None

let char (c : char) : char parser =
  satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None

let (>>) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) ->
    (match p2 ls with
     | Some (_, ls) -> Some (x, ls)
     | None -> None)
  | None -> None

let (<<) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls)  -> Some (x, ls)
  | None -> p2 ls

let (<|>) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None

let (>|=) = map

let (>|) = fun p c -> map p (fun _ -> c)

let rec many (p : 'a parser) : ('a list) parser =
  fun ls ->
  match p ls with
  | Some (x, ls) ->
    (match many p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> Some ([], ls)

let rec many1 (p : 'a parser) : ('a list) parser =
  fun ls ->
  match p ls with
  | Some (x, ls) ->
    (match many p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> None

let rec many' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) ->
    (match many' p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) ->
    (match many' p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> None

let whitespace : unit parser =
  fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c
    then Some ((), ls)
    else None
  | _ -> None

let ws : unit parser =
  (many whitespace) >| ()

let ws1 : unit parser =
  (many1 whitespace) >| ()

let digit : char parser =
  satisfy is_digit

let natural : int parser =
  fun ls ->
  match many1 digit ls with
  | Some (xs, ls) ->
    Some (int_of_string (implode xs), ls)
  | _ -> None

let literal (s : string) : unit parser =
  fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match cs, ls with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c
      then loop cs xs
      else None
    | _ -> None
  in loop cs ls

let keyword (s : string) : unit parser =
  (literal s) >> ws >| ()
  
(* end of parser combinators *)

let reserved = [
  "fun";
  "if";
  "then";
  "else";
  "let";
  "rec";
  "in";
  "trace";
  "main";
]

let name : string parser =
  let* xs1 = many1 (satisfy (fun c -> is_alpha c || c = '_')) in
  let* xs2 = 
    many (satisfy (fun c ->
      is_alphanum c ||
      (c = '_') ||
      (c = '\'')))
  in
  let s = (implode xs1) ^ (implode xs2) in
  if List.exists (fun x -> x = s) reserved
  then fail
  else pure s << ws

let name_parser () =
  let* n = name in
  pure (Name n)

let unit_parser () =
  let* _ = keyword "()" in
  pure (Unit)

let int_parser () =
  let* n = natural in
  pure (Int n) << ws

let rec term_parser0 () =
  let* _ = pure () in
  (name_parser ()) <|>
  (unit_parser ()) <|>
  (int_parser ()) <|>
  (keyword "(" >> term_parser () << keyword ")")

and term_parser1 () =
  let* es = many1 (term_parser0 ()) in
  match es with
  | e :: es ->
    pure (List.fold_left (fun acc e -> App (acc, e)) e es)
  | _ -> fail

and term_parser2 () =
  let* e = term_parser1 () in
  let opr () = 
    (let* _ = keyword "*" in
    let* e = term_parser1 () in
    pure ((fun e1 e2 -> Mul (e1, e2)), e))
    <|>
    (let* _ = keyword "/" in
    let* e = term_parser1 () in
    pure ((fun e1 e2 -> Div (e1, e2)), e))
  in
  let* es = many (opr ()) in
  pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

and term_parser3 () =
  let* e = term_parser2 () in
  let opr () = 
    (let* _ = keyword "+" in
    let* e = term_parser2 () in
    pure ((fun e1 e2 -> Add (e1, e2)), e))
    <|>
    (let* _ = keyword "-" in
    let* e = term_parser2 () in
    pure ((fun e1 e2 -> Sub (e1, e2)), e))
  in
  let* es = many (opr ()) in
  pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

and term_parser () = 
  let* _ = pure () in
  (keyword "trace" >> term_parser3 () >|= (fun e -> Trace e)) <|>
  (fun_parser ()) <|>
  (iflz_parser ()) <|>
  (letrec_parser ()) <|>
  (letin_parser ()) <|>
  (term_parser3 ())

and fun_parser () =
  let* _ = keyword "fun" in
  let* a = name in
  let* _ = keyword "->" in
  let* e = term_parser () in
  pure (Fun ("_", a, e))

and iflz_parser () =
  let* _ = keyword "if" in
  let* cond = term_parser () in
  let* _ = keyword "then" in
  let* e1 = term_parser () in
  let* _ = keyword "else" in
  let* e2 = term_parser () in
  pure (Ifgz (cond, e1, e2))

and letin_parser () =
  let* _ = keyword "let" in
  let* n = name in
  let* _ = keyword "=" in
  let* e1 = term_parser () in
  let* _ = keyword "in" in
  let* e2 = term_parser () in
  pure (LetIn (n, e1, e2))

and letrec_parser () =
  let* _ = keyword "let" in
  let* _ = keyword "rec" in
  let* n = name in
  let* args = many1 name in
  let* _ = keyword "=" in
  let* e1 = term_parser () in
  let (e1, _) =
    List.fold_right
      (fun arg (acc, len) ->
        let fn = if len = 1 then n else "_" in
        (Fun (fn, arg, acc), len - 1))
      args (e1, List.length args)
  in
  let* _ = keyword "in" in
  let* e2 = term_parser () in
  pure (LetIn (n, e1, e2))

(* Parse programs written in the term language. *)
let parse_prog (s : string) : (term * char list) option = 
  parse (ws >> term_parser ()) s
  


let rec compile (t:term) : string = 
  match t with 
    | LetIn (x,y,z) -> (match (x,y,z) with 
                                            | (var_name, Fun (x,y,z), scope) -> " Begin" ^ " Push " ^ var_name ^ compile (Fun (x,y,z)) ^ " Push " ^ var_name ^ " Lookup Let"  ^ (compile scope)  ^ " End"
                                            | (var_name, t1, scope) -> " Begin" ^ " Push " ^ var_name ^ compile t1 ^ " Let" ^ (compile scope) ^ " End"
                                            | _ -> "Error")
    | Add (t1,t2) -> (match (t1,t2) with 
                    | (Name n,Int x) -> " Push " ^ n ^ " Lookup"  ^  (compile t2) ^ "Add"
                    | (Int x, Name n) -> (compile t1) ^ " Push " ^ n ^ " Lookup"  ^  "Add"
                    | (Name x, Name y) -> " Push " ^ x ^ " Lookup"  ^  " Push " ^ y ^ " Lookup " ^ "Add"
                    | (x,y) -> (compile x) ^ (compile y) ^ " Add"
                    | _ -> "Error")
    | Sub (t1,t2) -> (match (t1,t2) with 
                    | (Name n,Int x) -> " Push " ^ n ^ " Lookup"  ^  (compile t2) ^ "Sub"
                    | (Int x, Name n) -> (compile t1) ^ " Push " ^ n ^ " Lookup"  ^  "Sub"
                    | (Name x, Name y) -> " Push " ^ x ^ " Lookup"  ^  " Push " ^ y ^ " Lookup " ^ "Sub"
                    | (x,y) -> (compile x) ^ (compile y) ^ " Sub"
                    | _ -> "Error")
    | Mul (t1,t2) -> (match (t1,t2) with 
                    | (Name n,Int x) -> " Push " ^ n ^ " Lookup"  ^  (compile t2) ^ "Mul"
                    | (Int x, Name n) -> (compile t1) ^ " Push " ^ n ^ " Lookup"  ^  "Mul"
                    | (Name x, Name y) -> " Push " ^ x ^ " Lookup"  ^  " Push " ^ y ^ " Lookup " ^ "Mul"
                    | (x,y) -> (compile x) ^ (compile y) ^ " Mul"
                    | _ -> "Error")
    | Div (t1,t2) -> (match (t1,t2) with 
                    | (Name n,Int x) -> " Push " ^ n ^ " Lookup"  ^  (compile t2) ^ "Div"
                    | (Int x, Name n) -> (compile t1) ^ " Push " ^ n ^ " Lookup"  ^  "Div"
                    | (Name x, Name y) -> " Push " ^ x ^ " Lookup"  ^  " Push " ^ y ^ " Lookup " ^ "Div"
                    | (x,y) -> (compile x) ^ (compile y) ^ " Div"
                    | _ -> "Error")
    | Ifgz (x,t1,t2) -> (match x with 
                      | Int n -> " Push " ^ (string_of_int n) ^ " If Begin " ^ (compile t1) ^ " End Else Begin " ^ (compile t2) ^ " End End"
                      | Name n -> " Push " ^ n ^ " Lookup " ^ " If Begin " ^ compile t1 ^ " End Else Begin " ^ (compile t2) ^ " End End "
                      | _ -> "Error")
    | Fun (n1, n2, t) -> " Fun " ^ n1 ^ " " ^ n2 ^ compile t ^ " End " 
    | App (t1,t2) -> compile t1 ^ compile t2 ^ " Call "
    | Int x -> " Push " ^ string_of_int x ^ " "
    | Trace x -> compile x ^ " Trace "
    | Name x -> " Push " ^ x ^ " Lookup "
    | Unit -> " Push () "
    | _ -> "Error"

let rec compile2 (t:term) : string = 
      match t with 
        | LetIn (n,t1,t2) -> "Begin Push " ^ n ^ " "  ^ compile2 t1 ^ " Let " ^ compile2 t2 ^ " End"
        | Add (t1,t2) -> (match (t1,t2) with 
                        | (Name n,Int x) -> " Push " ^ n ^ " Lookup"  ^  (compile2 t2) ^ "Add"
                        | (Int x, Name n) -> (compile2 t1) ^ " Push " ^ n ^ " Lookup"  ^  "Add"
                        | (Name x, Name y) -> " Push " ^ x ^ " Lookup"  ^  " Push " ^ y ^ " Lookup " ^ "Add"
                        | (x,y) -> (compile2 x) ^ (compile2 y) ^ " Add"
                        | _ -> "Error")
        | Sub (t1,t2) -> (match (t1,t2) with 
                        | (Name n,Int x) -> " Push " ^ n ^ " Lookup"  ^  (compile2 t2) ^ "Sub"
                        | (Int x, Name n) -> (compile2 t1) ^ " Push " ^ n ^ " Lookup"  ^  "Sub"
                        | (Name x, Name y) -> " Push " ^ x ^ " Lookup"  ^  " Push " ^ y ^ " Lookup " ^ "Sub"
                        | (x,y) -> (compile2 x) ^ (compile2 y) ^ " Sub"
                        | _ -> "Error")
        | Mul (t1,t2) -> (match (t1,t2) with 
                        | (Name n,Int x) -> " Push " ^ n ^ " Lookup"  ^  (compile2 t2) ^ "Mul"
                        | (Int x, Name n) -> (compile2 t1) ^ " Push " ^ n ^ " Lookup"  ^  "Mul"
                        | (Name x, Name y) -> " Push " ^ x ^ " Lookup"  ^  " Push " ^ y ^ " Lookup " ^ "Mul"
                        | (x,y) -> (compile2 x) ^ (compile2 y) ^ " Mul"
                        | _ -> "Error")
        | Div (t1,t2) -> (match (t1,t2) with 
                        | (Name n,Int x) -> " Push " ^ n ^ " Lookup"  ^  (compile2 t2) ^ "Div"
                        | (Int x, Name n) -> (compile2 t1) ^ " Push " ^ n ^ " Lookup"  ^  "Div"
                        | (Name x, Name y) -> " Push " ^ x ^ " Lookup"  ^  " Push " ^ y ^ " Lookup " ^ "Div"
                        | (x,y) -> (compile2 x) ^ (compile2 y) ^ " Div"
                        | _ -> "Error")
        | Ifgz (x,t1,t2) -> compile x ^ " If Begin " ^ compile2 t1 ^ " End Else Begin " ^ (compile2 t2) ^ " End End "
        | Fun (n1, n2, t) -> " Fun " ^ n1 ^ " " ^ n2 ^ " " ^ compile2 t ^ " End " ^ "Push " ^ n1 ^ " Lookup "
        | App (t1,t2) -> compile2 t1 ^ compile2 t2 ^ " Call "
        | Int x -> " Push " ^ string_of_int x ^ " "
        | Trace x -> compile2 x ^ " Trace "
        | Name x -> " Push " ^ x ^ " Lookup "
        | Unit -> " Push () "
        | _ -> "Error"



let test9 = match parse_prog "let rec eq x y =
if x then
  if y then eq (x - 1) (y - 1) else 0 
else
  if y then 0 else 1
in
let _ = trace (eq 10 10) in
let _ = trace (eq 1 (2 - 1)) in
let _ = trace (eq 9 (3 * 3)) in
let _ = trace (eq (25 / 5) (25 / 6)) in
()" with 
  | Some (x,y) -> x 
  | None -> Unit

let test9_compiled = compile2 test9;;



(* Compiles a program written in the Part3 Term Language to Part2 Stack Language.
 * Required by the autograder, do not change its type. *)
let compiler (src : string) : string =
  let parsed = match (parse_prog src) with 
                | Some (x,y) -> x 
                | _ -> Unit 
  in 
  compile2 parsed;;


let write_output s =
    (* Write message to file *)
    let oc = open_out "result.txt" in (* create or truncate file, return channel *)
      Printf.fprintf oc "%s\n" s; (* write something *)   
      close_out oc;;


let test10 = compiler "let rec fibo n =
let rec eq x y =
  if x then
    if y then eq (x - 1) (y - 1) else 0 
  else
    if y then 0 else 1
in
if eq n 0 then 0 else
if eq n 1 then 1 else
fibo (n - 1) + fibo (n - 2)
in
fibo 10"
in write_output test10;;

