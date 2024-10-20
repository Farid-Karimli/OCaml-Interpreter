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

(* Interprets a program written in the Part1 Stack Language.
 * Required by the autograder, do not change its type. *)



(* 2.1.1 Constants *)

type initial = Letter of char | Underscore
type const = Nat of int | Name of string | Unit | Closure of const * const * commands * env


(* 2.1.2 Programs *)

and command = Push of const | Add | Trace | Sub | Mul | 
              Div | If of commands * commands | Let | Lookup | Begin of commands | Function of const * const * commands | Call 
and commands = command list
and env = (const * const) list
(*prog = commands*)

(* 2.1.3 Programs *)

and value = VNat of int | VUnit | VName of string 

(* Parsers *)
let parse_const : const parser = 
  ws >> (
    natural >>= fun n -> pure (Nat n)
  ) <|> 
    (
      let* first = (satisfy is_alpha) <|> (char '_') in 
      let* rest = many ((satisfy is_alphanum)<|> (char '_') <|> (char '\'')) in 
      pure (Name (implode (first ::rest)))
    ) <|> (
      keyword "()" >> pure Unit
    )


let parse_push : command parser = 
  ws >>
  keyword "Push" >>= fun _ -> 
  parse_const >>= fun x -> 
  pure (Push x)


let parse_add : command parser = 
  ws >>
  keyword "Add" >>= fun _ -> 
  pure (Add)

let parse_mul : command parser = 
  ws >>
  keyword "Mul" >>= fun _ -> 
  pure (Mul)  

let parse_sub : command parser = 
  ws >>
  keyword "Sub" >>= fun _ -> 
  pure (Sub)  
let parse_div : command parser = 
  ws >>
  keyword "Div" >>= fun _ -> 
  pure (Div)  
let parse_div : command parser = 
  ws >>
  keyword "Div" >>= fun _ -> 
  pure (Div)  

let parse_trace : command parser = 
  ws >> 
  keyword "Trace" >>= fun _ ->
  pure (Trace)

let parse_let : command parser = 
  ws >> 
  keyword "Let" >>= fun _ -> 
  pure (Let)

let parse_lookup : command parser = 
  ws >> 
  keyword "Lookup" >>= fun _ -> 
  pure (Lookup)

let parse_call : command parser = 
  ws >> 
  keyword "Call" >>= fun _ -> 
  pure (Call)




let rec parse_coms2 () = 
  ws >> 
  parse_push 
  <|>
  parse_add
  <|>
  parse_sub 
  <|>
  parse_mul 
  <|>
  parse_div
  <|>
  parse_trace
  <|> 
  parse_if2 ()
  <|>
  parse_let 
  <|> 
  parse_lookup
  <|> 
  parse_begin_end ()
  <|> 
  parse_function ()
  <|> 
  parse_call 

and parse_if2 () = 
  ws >>
  keyword "If" >>= fun _ -> 
  many' (fun () -> parse_coms2 ()) >>= fun if_com -> 
  ws >> 
  keyword "Else" >>= fun _ -> 
  many' (fun () -> parse_coms2 ())>>= fun else_com ->
  ws >>
  keyword "End" >>= fun _ ->
  pure (If (if_com,else_com))

and parse_begin_end () =
  ws >> 
  keyword "Begin" >>= fun _ -> 
  many' (fun () -> parse_coms2 ()) >>= fun coms ->
  ws >> 
  keyword "End" >>= fun _ -> 
  pure (Begin (coms))

and parse_function () =
  ws >>
  keyword "Fun" >>= fun _ -> 
  ws >>
  parse_const >>= fun fname -> 
  ws >>
  parse_const >>= fun arg ->
  ws >>
  many' (fun () -> parse_coms2 ()) >>= fun coms -> 
  ws >>
  keyword "End" >>= fun _ ->
  pure (Function ((fname),(arg),coms))

let parse_string3 = 
  many (parse_coms2 ()) >>= fun lst -> 
  pure (lst)


(* End of Parsers *)







(* Helper functions *)
let extract_const (c: const) = 
  match c with 
  | Nat x -> (string_of_int x)
  | Name x -> x
  | Unit -> "()"
  | Closure (a,b,c,d) -> "<fun>"
  


let is_int (i: char list) = 
  match i with
  | '-' :: rest -> (match parse natural (implode rest) with 
      | Some (x,y) -> true
      | _ -> false)
  | [] -> false
  | _ -> (match parse natural (implode i) with 
      | Some (x,y) -> true
      | _ -> false)

let rec find_variable (var: string) (env: (const * const) list) = 
  match env with 
  | (Name name, value) :: rest -> if String.equal var name then Some (value) else find_variable var rest
  | _ -> None


let make_const str = 
  match str with
  | "()" -> Unit
  | s -> if (is_int (explode s)) then Nat (int_of_string s) else Name s

(* End of Helper functions *)




(* Interpreting step *)

let rec evaluate (stack: const list) (log: string list)  (command_list) (env)= 
  match command_list with 
  | Push val1 :: rest -> evaluate ((val1) :: stack) log rest env
  | Add :: rest -> (match stack with 
      | Nat n1 :: Nat n2 :: rest2 -> evaluate (Nat (n1+n2) :: rest2) log rest env 
      | _ -> None)
  | Sub :: rest -> (match stack with 
      |  Nat n1 :: Nat n2 :: rest2 -> evaluate (Nat (n2-n1) :: rest2) log rest env 
      | _ -> None)
  | Mul :: rest -> (match stack with 
      | Nat n1 :: Nat n2 :: rest2 -> evaluate (Nat (n2*n1) :: rest2) log rest env
      | _ -> None)
  | Div :: rest -> (match stack with 
      | Nat 0 :: n2 :: rest2 -> None
      | Nat n1 :: Nat n2 :: rest2 -> evaluate (Nat (n2/n1) :: rest2) log rest env
      | _ -> None)
  | Trace :: rest -> (match stack with 
      | Closure (a,b,c,d) :: rest2 -> evaluate (Unit :: rest2) ("<fun>" :: log) rest env 
      | top :: rest2 -> evaluate (Unit :: rest2) (extract_const (top) :: log) rest env 
      | _ -> None)
  | If (if_com, else_com) :: rest -> (match stack with 
      | Nat n1 :: rest2 -> 

        if (n1) > 0 then evaluate rest2 log (if_com @ rest) env
        else evaluate rest2 log (else_com @ rest) env 

      | _ -> None)
  | Let :: rest -> (match stack with 
      | value :: Name name :: rest2 -> evaluate rest2 log rest ((Name name, value) :: env) 
      | _ -> None)
  | Lookup :: rest -> ( match stack with
      | Name name :: rest2 ->  (match find_variable name env with
          | None -> None 
          | Some (y) -> evaluate (y :: rest2) log rest env
        ) 
      | _ -> None)
  | Begin (coms) :: rest -> (match evaluate [] log coms env with 
      | Some (x,y) -> evaluate ( x::stack) (y) rest env
      | _ -> None
    )
  | Function (fname, arg, coms) :: rest -> evaluate (stack) log rest ((fname, Closure (fname, arg, coms, env)) :: env)
  | Call :: rest  -> (match stack with 
      | argument :: Closure (fname, arg, coms,environ) :: rest2 -> (match evaluate [] log coms (( arg, argument) ::( fname, Closure (fname, arg, coms, env)) ::environ) with
          | Some (top, lst) -> evaluate ( top :: rest2) (lst) rest env 
          | _ -> None)
      | _ -> None
    )
  | [] -> (match stack with 
      | top :: rest -> Some (top,log)   
      | _ -> None)


(* End of interpreting step *)



let function_str = "Fun f x Push x Lookup Trace Push 1 End Push f Lookup Push 35 Call";;
let function_str2 = "Push x
Push 1
Let
Fun f z
    Push x
    Lookup
    Push x
    Push 2
    Let
End
Push x
Push 3
Let
Push f
Lookup
Push 4
Call";;
let rec_fun_str = "Fun f x Push x Lookup If Push x Lookup Trace Push f Lookup Push x Lookup Push 1 Sub Call Else Push () End End Push f Lookup Push 10 Call";;

let example = "Begin
Push x
Begin
Push x
Push 12
Push 0
Sub
Let
Begin
Push _
Push x
Lookup
Trace
Let
Begin
Push y
Push 32
Push 0
Sub
Let
Begin
Push _
Push y
Lookup
Trace
Let
Push x
Lookup
End
End
End
End
Let
Begin
Push x
Push x
Lookup
If
Begin
Push 99
Trace
End
Else
Begin
Push 13
Trace
End
End
Let
Push x
Lookup
End
End
";;
let example2 = "Push x
Push 3
Let
Begin
Push x
    Lookup
    Trace
    Push x
    Push 2
    Let
    Push x
    Lookup
    Trace
End
Push x
Lookup
Trace"





let basic_begin = "Push x
Push 3
Let
Begin
Push x
    Lookup
    Trace
    Push x
    Push 2
    Let
    Push x
    Lookup
    Trace
End
Push x
Lookup
Trace";;

let example5 = [Begin
[Push (Name "x"); Push (Name "x"); Lookup;
 If ([Begin [Push (Nat 99); Trace]], [Begin [Push (Nat 13); Trace]]);
    Let; Push (Name "x"); Lookup]]


let example7 = "Begin
Push x
Push 12
Push 0
Sub
Let
Begin
  Push _
  Push x
  Lookup
  Trace
  Let
  Begin
    Push y
    Push 32
    Push 0
    Sub
    Let
    Begin
      Push _
      Push y
      Lookup
      Trace
      Let
      Push x
      Lookup
    End
  End
End
End";;



(* Interpreter *)

let interpreter (src : string) : (string * string list) =
  let lst = 
    (match parse parse_string3 src with 
     | Some (x,y) -> x 
     | None -> [])
  in 
  match evaluate [] [] lst [] with
  | Some (s1,s2) -> (extract_const s1,s2)
  | _ -> ("Error",[])




let test18 = "Begin
Push eq
Fun eq x
Fun _ y
Push x
Lookup
If
Begin
Push y
Lookup
If
Begin
Push eq
Lookup
Push x
Lookup
Push 1
Sub
Call
Push y
Lookup
Push 1
Sub
Call
End
Else
Begin
Push 0
End
End
End
Else
Begin
Push y
Lookup
If
Begin
Push 0
End
Else
Begin
Push 1
End
End
End
End
End
Push _
Lookup
End
Push eq
Lookup
Let
Begin
Push gt
Fun gt x
Fun _ y
Push x
Lookup
If
Begin
Push y
Lookup
If
Begin
Push gt
Lookup
Push x
Lookup
Push 1
Sub
Call
Push y
Lookup
Push 1
Sub
Call
End
Else
Begin
Push 1
End
End
End
Else
Begin
Push 0
End
End
End
Push _
Lookup
End
Push gt
Lookup
Let
Begin
Push bsearch
Fun bsearch n
Fun _ i
Fun _ j
Begin
Push k
Push i
Lookup
Push j
Lookup
Add
Push 2
Div
Let
Begin
Push _
Push k
Lookup
Trace
Let
Push gt
Lookup
Push i
Lookup
Call
Push j
Lookup
Call
If
Begin
Push k
Lookup
End
Else
Begin
Begin
Push sq
Push k
Lookup
Push k
Lookup
Mul
Let
Push eq
Lookup
Push sq
Lookup
Call
Push n
Lookup
Call
If
Begin
Push k
Lookup
End
Else
Begin
Push gt
Lookup
Push n
Lookup
Call
Push sq
Lookup
Call
If
Begin
Push bsearch
Lookup
Push n
Lookup
Call
Push k
Lookup
Push 1
Add
Call
Push j
Lookup
Call
End
Else
Begin
Push bsearch
Lookup
Push n
Lookup
Call
Push i
Lookup
Call
Push k
Lookup
Push 1
Sub
Call
End
End
End
End
End
End
End
End
End
End
Push _
Lookup
End
Push _
Lookup
End
Push bsearch
Lookup
Let
Begin
Push sqrt
Fun sqrt n
Push bsearch
Lookup
Push n
Lookup
Call
Push 0
Call
Push n
Lookup
Call
End
Push sqrt
Lookup
Let
Begin
Push sq
Push 169
Let
Push sqrt
Lookup
Push sq
Lookup
Call
Trace
End
End
End
End
End
";;