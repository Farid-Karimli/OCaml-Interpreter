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
type const = Nat of int | Name of string | Unit 


(* 2.1.2 Programs *)

type command = Push of const | Add | Trace | Sub | Mul | 
               Div | If of commands * commands 
and commands = command list

(*prog = commands*)

(* 2.1.3 Programs *)

type value = VNat of int | VUnit | VName of string


(* Stack definition *)
type 'a stack = Stack of 'a list | Empty
let empty s = 
  match s with 
  | Empty -> true
  | _ -> false
let push s element = 
  match s with 
  | Stack list -> Stack (element :: list)
  | Empty -> Stack ([element])

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

let const_to_string constant = 
  match constant with
  | Nat x -> string_of_int x
  | Name x -> x
  | Unit -> "()"

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



let parse_coms'= 
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
    

let parse_if : command parser = 
   ws >>
    keyword "If" >>= fun _ -> 
    many1 parse_coms' >>= fun if_com -> 
    ws >> 
    keyword "Else" >>= fun _ -> 
    many1 parse_coms' >>= fun else_com ->
    ws >>
    keyword "End" >>= fun _ ->
    pure (If (if_com,else_com))


    let parse_coms = 
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
      parse_if

    
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
      

let extract_const (c: const) = 
  match c with 
  | Nat x -> (string_of_int x)
  | Name x -> x
  | Unit -> "()"

let is_int2 (i: 'a) = 
  match parse natural i with
  | Some (x,y) -> true
  | None -> false
  

  let is_int (i: char list) = 
    match i with
    | '-' :: rest -> (match parse natural (implode rest) with 
                      | Some (x,y) -> true
                      | _ -> false)
    | [] -> false
    | _ -> (match parse natural (implode i) with 
            | Some (x,y) -> true
            | _ -> false)
let parse_string2 = 
  many (parse_coms) >>= fun lst -> 
  pure (lst)

let parse_string3 = 
    many (parse_coms2 ()) >>= fun lst -> 
    pure (lst)



(* eval_command_list2 ((string_of_int value):: log) ((Push Unit) :: rest) 
   Push (Nat (value)) :: Trace :: rest -> ["Error"] *)
let rec eval_command_list2  (command_list : command list) =
  match command_list with
  | Push (Nat (val1)) :: Push (Nat (val2)) :: Add :: rest ->  eval_command_list2 ((Push (Nat (val1 + val2))) :: rest)
  | Push (Nat (val1)) :: Push (Nat (val2)) :: Mul :: rest ->  eval_command_list2 ((Push (Nat (val1 * val2))) :: rest)
  | Push (Nat (val1)) :: Push (Nat (val2)) :: Sub :: rest ->  eval_command_list2 ((Push (Nat (val1 - val2))) :: rest)
  | Push (Nat (val1)) :: Push (Nat (val2)) :: Div :: rest ->  if val2 != 0 then eval_command_list2 ((Push (Nat (val1 / val2))) :: rest) 
    else ["Error"]
  | [Push c] -> [const_to_string c]
  | _ -> ["Error"]

let rec evaluate (stack: 'a list) (log: string list)  (command_list) = 
  match command_list with 
  | Push val1 :: rest -> evaluate ((extract_const val1) :: stack) log rest
  | Add :: rest -> (match stack with 
      | n1 :: n2 :: rest2 -> if is_int (explode n1) && is_int (explode n2) then evaluate (string_of_int((int_of_string n1) + (int_of_string n2)) :: rest2) log rest else Some ("Error", [])
      | _ -> Some ("Error", []))
  | Sub :: rest -> (match stack with 
      | n1 :: n2 :: rest2 -> if is_int (explode n1) && is_int (explode n2) then evaluate (string_of_int((int_of_string n2) - (int_of_string n1)) :: rest2) log rest else Some ("Error", [])
      | _ -> Some ("Error", []))
  | Mul :: rest -> (match stack with 
      | n1 :: n2 :: rest2 -> if is_int (explode n1) && is_int (explode n2) then evaluate (string_of_int((int_of_string n1) * (int_of_string n2)) :: rest2) log rest else Some ("Error", [])
      | _ -> Some ("Error", []))
  | Div :: rest -> (match stack with 
      | "0" :: n2 :: rest2 -> Some ("Error",[])
      | n1 :: n2 :: rest2 -> if is_int (explode n1) && is_int (explode n2) then evaluate (string_of_int((int_of_string n2) / (int_of_string n1)) :: rest2) log rest else Some ("Error", [])
      | _ -> Some ("Error", []))
  | Trace :: rest -> (match stack with 
      | top :: rest2 -> evaluate ("()" :: rest2) ((top) :: log) rest
      | _ -> Some ("Error",[]))
  | If (if_com, else_com) :: rest -> (match stack with 
      | n1 :: rest2 -> 
              if is_int (explode n1) then 
                  if (int_of_string n1) > 0 then evaluate rest2 log (if_com @ rest) 
                  else evaluate rest2 log (else_com @ rest) 
              else Some ("Error",[])
      | _ -> Some ("Error",[]))
  | [] -> (match stack with 
      | top :: rest -> Some (top,log)
      | _ -> Some ("Error",[]))
  


let str = "Push 6 Push 3 Sub Push 0 Push 2 Push 1 Push 0 Sub Sub Push 0 Sub Sub Sub";;
let interpreter' (src : string) : (string * string list) =
  let lst = 
    (match parse parse_string2 src with 
      | Some (x,y) -> x 
      | None -> [])
  in 
   match evaluate [] [] lst with
    | Some (s1,s2) -> (s1,s2)
    | _ -> ("Error",[])

let interpreter (src : string) : (string * string list) =
      let lst = 
        (match parse parse_string3 src with 
          | Some (x,y) -> x 
          | None -> [])
      in 
       match evaluate [] [] lst with
        | Some (s1,s2) -> (s1,s2)
        | _ -> ("Error",[])

