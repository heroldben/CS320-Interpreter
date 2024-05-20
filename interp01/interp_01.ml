(* UTILITIES *)
let cons x xs = x :: xs
let explode s = List.of_seq (String.to_seq s)
let implode cs = String.of_seq (List.to_seq cs)
let is_digit c = '0' <= c && c <= '9'
let is_blank c = String.contains " \012\n\r\t" c
let is_upper_case c = 'A' <= c && c <= 'Z'

type 'a parser = char list -> ('a * char list) option

let satisfy f = function
  | c :: cs when f c -> Some (c, cs)
  | _ -> None

let char c = satisfy ((=) c)

let str s cs =
  let rec go = function
    | [], ds -> Some (s, ds)
    | c :: cs, d :: ds when c = d -> go (cs, ds)
    | _ -> None
  in go (explode s, cs)

let map f p cs =
  match p cs with
  | Some (x, cs) -> Some (f x, cs)
  | None -> None

let (>|=) p f = map f p
let (>|) p x = map (fun _ -> x) p

let seq p1 p2 cs =
  match p1 cs with
  | Some (x, cs) -> (
      match p2 cs with
      | Some (y, cs) -> Some ((x, y), cs)
      | None -> None
    )
  | None -> None

let (<<) p1 p2 = map fst (seq p1 p2)
let (>>) p1 p2 = map snd (seq p1 p2)

let map2 f p1 p2 =
  seq p1 p2 >|= fun (x, y) -> f x y

let optional p cs =
  match p cs with
  | Some (x, cs) -> Some (Some x, cs)
  | None -> Some (None, cs)

let rec many p cs =
  match p cs with
  | Some (x, cs) -> (
      match (many p cs) with
      | Some (xs, cs) -> Some (x :: xs, cs)
      | None -> Some ([x], cs)
    )
  | None -> Some ([], cs)

let many1 p = map2 cons p (many p)

let alt p1 p2 cs =
  match p1 cs with
  | Some x -> Some x
  | None ->
      match p2 cs with
      | Some x -> Some x
      | None -> None

let (<|>) = alt

let pure x cs = Some (x, cs)
let fail _ = None

let bind p f cs =
  match p cs with
  | Some (x, cs) -> f x cs
  | None -> None

let (>>=) = bind

let choice ps =
  List.fold_left (<|>) fail ps

let ws = many (satisfy is_blank)
let keyword w = str w << ws

let rec_parser p =
  pure () >>= p

let parse p s =
  match p (explode s) with
  | Some (x, []) -> Some x
  | _ -> None

(* END OF UTILITIES *)

(* ============================================================ *)

(* BEGINNING OF PROJECT CODE *)

type ident = string
type command
  = Drop                   (* drop *)
  | Swap                   (* swap *)
  | Dup                    (* dup *)
  | Trace                  (* . *)
  | Add                    (* + *)
  | Sub                    (* - *)
  | Mul                    (* * *)
  | Div                    (* / *)
  | Lt                     (* < *)
  | Eq                     (* = *)
  | Bind of ident          (* |> ID *)
  | Call of ident          (* # ID *)
  | If of program          (* ? prog ; *)
  | Def of ident * program (* def prog ; *)
  | Ident of ident         (* ID *)
  | Num of int             (* num *)
and program = command list

let is_lower_case c = 'a' <= c && c <= 'z'
let is_upper_case c = 'A' <= c && c <= 'Z'

(* White space can exist at the beginning and/or end*)
let parse_ident =
  ws >> many1 (satisfy is_upper_case) >|= implode << ws ;;

(* Examples 
   
1. parse parse_ident "YES" -> Some "YES"
2. parse parse_ident "YES " -> Some "YES"
3. parse parse_ident " YES" -> Some "YES"
4. parse parse_ident "YES NO" -> None
*)

(* Numbers, same rules for parse_ident, and leading zeros must be "removed" or not taken into consideration *)
let parse_num =
  ws >> (many1 (satisfy is_digit) >|= (fun digits -> int_of_string (implode digits))) << ws


let rec parse_com () =
  let parse_def =
    map2
      (fun id p -> Def (id, p))
      (keyword "def" >> parse_ident << ws)
      (parse_prog_rec () << char ';') 
  in
  let parse_basic_coms =  (* Parsing for Basic Commands *)   
    (keyword "drop" >| Drop << ws) <|>
    (keyword "swap" >| Swap << ws) <|>
    (keyword "dup" >| Dup << ws) <|>
    (char '.' >| Trace << ws) <|>
    (char '+' >| Add << ws) <|>
    (char '-' >| Sub << ws) <|>
    (char '*' >| Mul << ws) <|>
    (char '/' >| Div << ws) <|> 
    (char '<' >| Lt << ws) <|> 
    (char '=' >| Eq << ws)
  in
  let parse_bind_call_if_coms =
    ((keyword "|>" >> parse_ident) >|= (fun id -> Bind id) << ws) <|>
    ((char '#' >> parse_ident) >|= (fun id -> Call id) << ws) <|>
    ((char '?' >> parse_prog_rec () << char ';') >|= (fun prog -> If prog) << ws)
  in 
  ws >>
  parse_def <|> 
  parse_basic_coms <|> 
  parse_bind_call_if_coms <|> 
  (parse_ident >|= (fun ide -> Ident ide)) <|> 
  (parse_num >|= (fun number -> Num number))
  << ws
and parse_prog_rec () =
  many ((rec_parser parse_com) << ws)

let parse_prog (s : string) =
  let rec parse_helper chr_lst =
    match parse_com () chr_lst with
    | Some (command, rest) -> 
        (match parse_helper rest with
         | Some (lst_commands, other_rest) -> Some (command :: lst_commands, other_rest)
         | None -> Some ([command], rest))
    | None -> 
        if List.exists is_blank chr_lst then parse_helper (List.filter (fun chr -> not (is_blank chr)) chr_lst)
        else None
    
  in
  match parse_helper (explode s) with
  | Some (commands, []) -> Some commands  
  | _ -> None  

(* A VERY SMALL TEST SET *)
(*
let test = parse_prog "drop"
let out = Some [Drop]
let _ = assert (test = out)

let test = parse_prog "     .       "
let out = Some [Trace]
let _ = assert (test = out)

let test = parse_prog "  |> TEST   "
let out = Some [Bind "TEST"]
let _ = assert (test = out)

let test = parse_prog "  23 00345 + |> OK "
let out = Some [Num 23; Num 345; Add; Bind "OK"]
let _ = assert (test = out)

let test = parse_prog "  def NEG 0 - ; 2 #NEG 2 =    \n\n   "
let out = Some [Def ("NEG", [Num 0; Sub]); Num 2; Call "NEG"; Num 2; Eq]
let _ = assert (test = out)

let test = parse_prog "
  def ABS
    dup 0 swap < ?
      0 -
    ;
  ;

  30 0 -
  #ABS
  |> X
"
let out = Some
    [ Def ("ABS", [Dup; Num 0; Swap; Lt; If [Num 0; Sub]])
    ; Num 30; Num 0; Sub
    ;  Call "ABS"
    ;  Bind "X"
    ]
let _ = assert (test = out)
*)

(* EVALUATION *)

type stack = int list
type value
  = Num of int
  | Prog of program
type env = (ident * value) list
type trace = string list


(* Update Env Cases

1. New Ident
      - Add to top of Stack/beginning of List for env
2. Existing Ident
      - Replaces ident's old value with new value
*)

(* env -> ident -> value -> env *)
let update_env e x v = 
  if List.exists (fun (ide,curr_val) -> ide = x) e then
    List.map (fun (ide, curr_val) -> 
        if ide = x then (ide, v)
        else (ide, curr_val)) e
  else (x, v) :: e

(* Fetch Env Cases

1. fetch env ∅x = None
      - Empty Environment -> None
2. fetch env (update env e x v) x = Some v
      - Gets the Value of the updated ident
3. fetch env (update env e y v) x = fetch env e x (x ̸= y)
      - "Ignores" Newly updated (ident:value) pair and returns value of other ident
4. x not in Env -> None
      - ident is not in the environment
*)

(* env -> ident -> value option *)
let rec fetch_env e x = 
  match e with
  | [] -> None
  | (ide, value) :: rest -> 
      if ide = x then Some value
      else fetch_env rest x

(* Stack operations for eval_prog *)

(* Removes element at top of stack *)
let op_drop s t p =
  match s with
  | [] -> (s, "panic: stack underflow" :: t, [])  
  | _ :: tl -> (tl, t, p)  

(* Swaps top 2 elements at top of stack *)
let op_swap s t p =
  match s with 
  | h1 :: h2 :: tl -> (h2 :: h1 :: tl, t, p)  
  | [h] -> (s, "panic: stack underflow" :: t, [])
  | [] -> (s, "panic: stack underflow" :: t, [])  

(* Duplicates top of the stack value *)
let op_duplicate s t p =
  match s with
  | [] -> (s, "panic: stack underflow" :: t, [])
  | h1 :: tl -> (h1 :: h1 :: tl, t, p)

(* Removes top of element and adds to trace *)
let op_trace s t p =
  match s with
  | [] -> (s, "panic: stack underflow" :: t, [])
  | h1 :: tl -> (tl, string_of_int h1 :: t, p) ;;

let op_push s n =
  (n :: s)

(* Adds the sum of the top 2 elements and replaces them*)
let op_add s t p =
  match s with 
  | h1 :: h2 :: tl -> ((h1 + h2) :: tl, t, p)
  | [h] -> (s, "panic: stack underflow" :: t, [])
  | [] -> (s, "panic: stack underflow" :: t, [])  

(* Difference of the top 2 elements and replaces them*)
let op_sub s t p = 
  match s with 
  | h1 :: h2 :: tl -> ((h1 - h2) :: tl, t, p)
  | [h] -> (s, "panic: stack underflow" :: t, [])
  | [] -> (s, "panic: stack underflow" :: t, [])  

(* Gets product of top 2 elements in stack and replaces them *)
let op_multiply s t p = 
  match s with 
  | h1 :: h2 :: tl -> ((h1 * h2) :: tl, t, p)
  | [h] -> (s, "panic: stack underflow" :: t, [])
  | [] -> (s, "panic: stack underflow" :: t, [])

(* Divides the top 2 elements in the stack and replaces them *)
let op_divide s t p =
  match s with 
  | h1 :: 0 :: tl -> (s, "panic: divide by 0" :: t, [])
  | h1 :: h2 :: tl -> ((h1 / h2) :: tl, t, p)
  | [h] -> (s, "panic: stack underflow" :: t, [])
  | [] -> (s, "panic: stack underflow" :: t, [])

let op_less_than s t p = 
  match s with 
  | h1 :: h2 :: tl -> 
      if h1 < h2 then (1 :: tl, t, p)
      else (0 :: tl, t, p)
  | [h] -> (s, "panic: stack underflow" :: t, [])
  | [] -> (s, "panic: stack underflow" :: t, [])
  
let op_equal s t p = 
  match s with 
  | h1 :: h2 :: tl -> 
      if h1 = h2 then (1 :: tl, t, p)
      else (0 :: tl, t, p)
  | [h] -> (s, "panic: stack underflow" :: t, [])
  | [] -> (s, "panic: stack underflow" :: t, [])  ;;

let op_fetch s t e id p =
  match fetch_env e id with 
  | Some (Num n) -> (n::s, t,p)
  | _ -> (s, "panic: identifier must be a number" :: t, [])

let op_bind s t e id p =
  match s with
  | [] -> (s, "panic: stack underflow" :: t, [], [])  
  | h :: tl -> (tl, t, update_env e id (Num h), p)
;; 

let op_call s t e id p =
  match fetch_env e id with 
  | Some (Prog prog) -> (s, t, prog @ p)
  | _ -> (s, "panic: identifier must be a program" :: t, [])
;;

let op_if s t e q p =
  match s with
  | [] -> (s, "panic: stack underflow" :: t, []) 
  | h :: tl ->
      if h = 0 then (tl, t, p)
      else (tl, t, q @ p)  

(* stack -> env -> program -> trace *)
let eval_prog s e p =
  let rec eval_prog_helper s e p t =
    match p with
    | [] -> t  
    | Drop :: tl ->
        let (new_s, new_t, new_p) = op_drop s t tl in
        eval_prog_helper new_s e new_p new_t
    | Swap :: tl ->
        let (new_s, new_t, new_p) = op_swap s t tl in
        eval_prog_helper new_s e new_p new_t
    | Dup :: tl -> 
        let (new_s, new_t, new_p) = op_duplicate s t tl in
        eval_prog_helper new_s e new_p new_t
    | Trace :: tl -> 
        let (new_s, new_t, new_p) = op_trace s t tl in
        eval_prog_helper new_s e new_p new_t 
    | Num n :: tl ->  
        eval_prog_helper (op_push s n) e tl t
    | Add :: tl -> 
        let (new_s, new_t, new_p) = op_add s t tl in
        eval_prog_helper new_s e new_p new_t
    | Sub :: tl -> 
        let (new_s, new_t, new_p) = op_sub s t tl in
        eval_prog_helper new_s e new_p new_t
    | Mul :: tl -> 
        let (new_s, new_t, new_p) = op_multiply s t tl in
        eval_prog_helper new_s e new_p new_t 
    | Div :: tl -> 
        let (new_s, new_t, new_p) = op_divide s t tl in
        eval_prog_helper new_s e new_p new_t 
    | Lt :: tl -> 
        let (new_s, new_t, new_p) = op_less_than s t tl in
        eval_prog_helper new_s e new_p new_t
    | Eq :: tl -> 
        let (new_s, new_t, new_p) = op_equal s t tl in
        eval_prog_helper new_s e new_p new_t
    | Bind id :: tl ->
        let (new_s, new_t, new_e, new_p) = op_bind s t e id tl in
        eval_prog_helper new_s new_e new_p new_t 
    | Ident id :: tl ->  
        let (new_s, new_t, new_p) = op_fetch s t e id tl in
        eval_prog_helper new_s e new_p new_t
    | Def (id, prog) :: tl ->  
        let new_e = update_env e id (Prog prog) in
        eval_prog_helper s new_e tl t 
    | Call id :: tl ->
        let (new_s, new_t,new_p) = op_call s t e id tl in
        if new_p = [] then new_t
        else eval_prog_helper new_s e new_p new_t
    | If prog :: tl ->
        let (new_s, new_t,new_p) = op_if s t e prog tl in
        eval_prog_helper new_s e new_p new_t 
  in
  eval_prog_helper s e p [];; 


(* string -> trace option *)
let interp s = 
  match parse_prog s with 
  | Some lst_commands -> Some (eval_prog [] [] lst_commands)
  | None -> None

(* END OF PROJECT CODE *)

(* ============================================================ *)

(* UNCOMMENT TO RUN INTERPRETER *)

let print_trace t =
  let rec go t =
    match t with
    | [] -> ()
    | x :: t ->
      print_endline x;
      go t
  in go (List.rev t)


let main () =
  let input =
    let rec get_input s =
      try
        get_input (s ^ "\n" ^ read_line ())
      with End_of_file ->
        s
    in get_input ""
  in
  match interp input with
  | None -> print_endline "Parse Error"
  | Some t -> print_trace t

let _ = main ()

