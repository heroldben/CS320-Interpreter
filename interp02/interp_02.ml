(* UTILITIES *)
let cons x xs = x :: xs
let explode s = List.of_seq (String.to_seq s)
let implode cs = String.of_seq (List.to_seq cs)
let is_digit c = '0' <= c && c <= '9'
let is_blank c = String.contains " \012\n\r\t" c
let is_upper_case c = 'A' <= c && c <= 'Z'
let is_lower_case c = 'a' <= c && c <= 'z'

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
let ( let* ) = bind

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

(* REQUIRED TYPES *)

type ident = string

type const
  = Num of int
  | Bool of bool

type command
  = Push of const | Trace (* . *)
  | Add (* + *) | Mul (* * *) | Div (* / *)
  | And (* && *) | Or (* || *) | Not (* ~ *) 
  | Lt (* < *) | Eq (* = *)
  | If of program * program (* ? prog prog *)
  | While of program * program (* While prog prog *)
  | Bind of ident (* |> ID *) | Fetch of ident (* ID *)
  | Fun of program (* : <prog> ; *) 
  | Call (* # *) | Return (* Return *)
  | Debug of string

and program = command list

and bindings = (ident * value) list

and value
  = Const of const
  | Clos of
      { def_id : int
      ; captured : bindings
      ; prog : program
      }

type record =
  { id : int
  ; local : bindings
  ; called_def_id : int
  ; return_prog : program
  }

type stack = value list
type trace = string list
type env
  = Global of bindings
  | Local of record * env

(* get the id of the topmost record *)
let local_id = function
  | Global _ -> 0
  | Local (r, _) -> r.id

(* convert a value to a string *)
let to_string v =
  match v with
  | Const (Bool true) -> "True"
  | Const (Bool false) -> "False"
  | Const (Num n) -> string_of_int n
  | Clos _ -> "<Closure>"

(* PARSING *)

let parse_ident =
  map2
    (fun c cs -> implode (c :: cs))
    (satisfy is_lower_case)
    (many (satisfy (fun c -> is_lower_case c || is_digit c || c = '_')))

let parse_int =
  let mk_int sign cs =
    let abs = int_of_string (implode cs) in
    if Option.is_none sign
    then abs
    else -abs
  in
  map2
    mk_int
    (optional (char '-'))
    (many1 (satisfy is_digit))

let parse_bool =
  (str "True" >| true) <|> (str "False" >| false)

let parse_comment =
  char '(' >> many (satisfy ((<>) ')')) >> char ')' >| ()

let parse_debug =
  char '"' >> many (satisfy ((<>) '"')) << char '"' >|= implode

let ws = many (ws >> parse_comment) >> ws
let keyword w = str w << ws

let rec parse_com () =
  let parse_fun = (* TODO *)
    let* _ = keyword ":" in
    let* function_body = parse_prog_rec () in
    let* _ = keyword ";" in
    pure (Fun function_body)
  in
  let parse_if =
    let* _ = keyword "?" in
    let* ifc = parse_prog_rec () in
    let* _ = keyword ";" in
    let* elsec = parse_prog_rec () in
    let* _ = char ';' in
    pure (If (ifc, elsec))
  in
  let parse_while =
    let* _ = keyword "While" in
    let* check = parse_prog_rec () in
    let* _ = keyword ";" in
    let* body = parse_prog_rec () in
    let* _ = char ';' in
    pure (While (check, body)) 
  in
  let parse_push = 
    (parse_int >|= fun n -> Push (Num n)) <|> (parse_bool >|= fun b -> Push (Bool b))
  in
  ws >> choice
    (* TODO: Add more alternatives *)
    [ parse_fun
    ; parse_push
    ; parse_while
    ; parse_if
    ; parse_ident >|= (fun s -> Fetch s)
    ; parse_debug >|= (fun s -> Debug s)
    ; char '.' >| Trace
    ; char '+' >| Add
    ; char '*' >| Mul
    ; char '/' >| Div
    ; keyword "&&" >| And
    ; keyword "||" >| Or
    ; char '~' >| Not
    ; char '<' >| Lt
    ; char '=' >| Eq
    ; char '#' >| Call
    ; keyword "Return" >| Return 
    ] << ws
and parse_prog_rec () =
  many (rec_parser parse_com << ws)

let parse_prog = parse (ws >> parse_prog_rec ())

(* FETCHING AND UPDATING *)

(* fetch the value of `x` in the environment `e` *)
let rec fetch_env e x = 
  match e with
  | Global bindings -> List.assoc_opt x bindings (* Checks local binding and gets value pair *)
  | Local (record, next_e) ->
      match List.assoc_opt x record.local with
      | Some v -> Some v (* Value found, return the value *)
      | None -> fetch_env next_e x (* if no value, go to next *)

        let rec update_env e x v = 
        match e with (* Depends onf Global or Local *)
        | Global bindings -> Global (update_env_helper bindings x v) 
        | Local (record, next_env) ->
            Local ({record with local = update_env_helper record.local x v}, next_env)
      and update_env_helper bindings x v = (* Checks if (ident * value) needs to be added or updated *)
        if List.exists(fun (ide,_) -> ide = x) bindings then
          List.map (fun (ide, curr_val) -> 
              if ide = x then (ide, v) 
              else (ide, curr_val)) bindings  (* goes next *)
        else (x,v) :: bindings (* adds new (ident * value) pair *)

(* EVALUTION *)

(* make the panic configuration given a configuration *)
let panic (_, _, t, _) msg = [], Global [], ("panic: " ^ msg) :: t, []

let eval_step (c : stack * env * trace * program) =
  match c with
  (* Push *)
  | s, e, t, Push c :: p -> Const c :: s, e, t, p
  (* Trace *)
  | v :: s, e, t, Trace :: p -> s, e, to_string v :: t, p
  | [], _, _, Trace :: _ -> panic c "stack underflow (. on empty)"
  (* Add *)
  | Const (Num m) :: Const (Num n) :: s, e, t, Add :: p -> Const (Num (m + n)) :: s, e, t, p
  | _ :: _ :: _, _, _, Add :: _ -> panic c "type error (+ on non-integers)"
  | _ :: [], _, _, Add :: _ -> panic c "stack underflow (+ on single)"
  | [], _, _, Add :: _ -> panic c "stack underflow (+ on empty)"
  (* Multiply *)
  | Const (Num m) :: Const (Num n) :: s, e, t, Mul :: p -> Const (Num (m * n)) :: s, e, t, p
  | _ :: _ :: _, _, _, Mul :: _ -> panic c "type error (* on non-integers)"
  | _ :: [], _, _, Mul :: _ -> panic c "stack underflow (* on single)"
  | [], _, _, Mul :: _ -> panic c "stack underflow (* on empty)"
  (* Divide *)
  | Const (Num m) :: Const (Num n) :: s, e, t, Div :: p when n <> 0 -> Const (Num (m / n)) :: s, e, t, p
  | Const (Num m) :: Const (Num 0) :: s, e, t, Div :: p -> panic c "division by 0"
  | _ :: _ :: _, _, _, Div :: _ -> panic c "type error (/ on non-integers)"
  | _ :: [], _, _, Div :: _ -> panic c "stack underflow (/ on single)"
  | [], _, _, Div :: _ -> panic c "stack underflow (/ on empty)"
  (* And *)
  | Const (Bool m) :: Const (Bool n) :: s, e, t, And :: p -> Const ((Bool (m && n))) :: s, e, t, p
  | Const (Bool m) :: [], _, t, And :: _ -> panic c "stack underflow (&& on single)"
  | [], _, t, And :: _ -> panic c "stack underflow (&& on empty)"
  | Const (Bool m) :: _ :: _,_,t, And :: _ -> panic c "type error (&& on non-boolean)"
  | _ :: Const (Bool n) :: _,_,t, And :: _ -> panic c "type error (&& on non-boolean)"
  | _ :: _ :: _,_,t, And :: _ -> panic c "type error (&& on non-boolean)"
  (* Or *)
  | Const (Bool m) :: Const (Bool n) :: s, e, t, Or :: p -> Const ((Bool (m || n))) :: s, e, t, p
  | Const (Bool m) :: [], _, t, Or :: _ -> panic c "stack underflow (|| on single)"
  | [], _, t, Or :: _ -> panic c "stack underflow (|| on empty)"
  | Const (Bool m) :: _ :: _,_,t, Or :: _ -> panic c "type error (|| on non-boolean)"
  | _ :: Const (Bool n) :: _,_,t, Or :: _ -> panic c "type error (|| on non-boolean)"
  | _ :: _ :: _,_,t, Or :: _ -> panic c "type error (|| on non-boolean)"
  (* Not *)
  | Const (Bool m) :: s, e, t, Not :: p -> Const (Bool (not m)) :: s, e, t, p
  | Const _ :: _, _, t, Not :: _ -> panic c "type error (not on non-boolean)"
  | [], _, t, Not :: _ -> panic c "type error (not on empty)"
  (* Less Than *)
  | Const (Num m) :: Const (Num n) :: s, e, t, Lt :: p -> Const (Bool (m < n)) :: s, e, t, p
  | Const (Num m) :: [],_,t, Lt :: _ -> panic  c "stack underflow (< on single)"
  | [], _, t, Lt :: _ -> panic c "stack underflow (< on empty)"
  | Const (Num m) :: (Const _ :: _), _, t, Lt :: _ -> panic c "type error (< on non-integer)"
  | (Const _) :: Const (Num n) :: _, _, t, Lt :: _ -> panic c "type error (< on non-integer)"
  | (Const _ :: Const _ :: _), _, t, Lt :: _ -> panic c "type error (< on non-integer)"
  (* Equals *)
  | Const (Num m) :: Const (Num n) :: s, e, t, Eq :: p -> Const (Bool (m = n)) :: s, e, t, p
  | Const (Num m) :: [],_,t, Eq :: _ -> panic  c "stack underflow (= on single)"
  | [], _, t, Eq :: _ -> panic c "stack underflow (= on empty)"
  | Const (Num m) :: (Const _ :: _), _, t, Eq :: _ -> panic c "type error (= on non-integer)"
  | (Const _) :: Const (Num n) :: _, _, t, Eq :: _ -> panic c "type error (= on non-integer)"
  | (Const _ :: Const _ :: _), _, t, Eq :: _ -> panic c "type error (= on non-integer)"
  (* If-Else *)
  | Const (Bool true) :: s, e, t, If (q1, q2) :: p -> (s, e, t, q1 @ p)
  | Const (Bool false) :: s, e, t, If (q1, q2) :: p -> (s, e, t, q2 @ p)
  | Const _ :: _, _, t, If (q1, q2) :: _ -> panic c "type error (if on non-boolean)"
  | [], _, t, If (q1 ,q2) :: _ -> panic c "stack underflow (if on empty)"
  (* While *)
  (* Fetch *)
  | s, e, t, Fetch x :: p -> 
    (match fetch_env e x with
    | Some v -> v :: s, e, t, p 
    | None -> panic c "no value found")
  (* Assign/Update *)
  | v :: s, e, t, Bind x :: p -> (s, update_env e x v, t, p) (* updates *)
  | [], e, t, Bind x :: _ -> panic c "stack is empty"
  (* Call *)
  | [], _, t, Call :: _ -> panic c "stack underflow (call on empty)"
  | Clos { def_id : int; captured : bindings; prog = closure_prog} :: s, e, t, Call :: p ->
    let new_rec = {id = def_id; local = captured; called_def_id = def_id; return_prog = p} in
    (s, Local (new_rec, e), t, closure_prog)
  | _,_,t, Call :: _ -> panic c "stack underflow (no closure on stack)"
  | _ -> assert false 

let rec eval c =
  match c with
  | (_, Global _, t, []) -> t
  | _ -> eval (eval_step c)

let rec eval_prog p = eval ([], Global [], [], p)
let interp s = Option.map eval_prog (parse_prog s)

(* MAIN *)

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

(* let _ = main () *)

(* END OF FILE *)
