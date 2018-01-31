(** ParserUtils
  Types and useful functions to be used in the parser. **)

open Low

type 'a monad_type = globals -> runs_type -> state -> 'a

(** The main type carried in the parser. **)
type token_type = sExpRec_pointer result monad_type

type parser_result =
  | Success of token_type
  | Command of string


(** * Wrappers **)

let no_globals (f : runs_type -> state -> 'a) : 'a monad_type = fun _ -> f
let no_runs (f : globals -> state -> 'a) : 'a monad_type = fun g _ -> f g
let only_state (f : state -> 'a) : 'a monad_type = fun _ _ -> f

let tuple_to_result (f : (state * 'a) monad_type) : 'a result monad_type =
  fun g r s ->
    let (s, v) = f g r s in
    Result_success (s, v)

(** This function is inspired from the [install_and_save] function
  of the original interpreter. It takes into advantage the fact
  that ocamllex is functional: its behaviour is exactly the same
  than the install function. It here serves as a wrapper, to
  change the order of the arguments of [install]. **)
let install_and_save str : token_type = fun g r s ->
  install g r s (Print.string_to_char_list str)

let null : token_type = fun _ _ s -> Result_success (s, nULL)
let nilValue : token_type = fun g _ s -> Result_success (s, read_globals g (R_NilValue))

(* This looks like a bug: this function should have been extracted. *)
let make_Rcomplex r i = { rcomplex_r = r; rcomplex_i = i }


(** * Composing Functions **)

let bind (comp : token_type) (cont : (sExpRec_pointer -> 'a result) monad_type) : 'a result monad_type =
  fun g r s -> if_success (comp g r s) (cont g r)

let shift (f : 'a -> 'b monad_type) : ('a -> 'b) monad_type =
  fun g r s x -> f x g r s

(** Compose a [token_type] function to a simple function which
  only cares about its return value. **)
let lift1 f comp : token_type =
  bind comp f
let lift2 f comp1 comp2 : token_type =
  bind comp1 (shift (fun res1 ->
    bind comp2 (fun g r s res2 ->
      f g r s res1 res2)))
let lift3 f comp1 comp2 comp3 : token_type =
  bind comp1 (shift (fun res1 ->
    bind comp2 (shift (fun res2 ->
      bind comp3 (fun g r s res3 ->
        f g r s res1 res2 res3)))))
let lift4 f comp1 comp2 comp3 comp4 : token_type =
  bind comp1 (shift (fun res1 ->
    bind comp2 (shift (fun res2 ->
      bind comp3 (shift (fun res3 ->
        bind comp4 (fun g r s res4 ->
          f g r s res1 res2 res3 res4)))))))
let lift5 f comp1 comp2 comp3 comp4 comp5 : token_type =
  bind comp1 (shift (fun res1 ->
    bind comp2 (shift (fun res2 ->
      bind comp3 (shift (fun res3 ->
        bind comp4 (shift (fun res4 ->
          bind comp5 (fun g r s res5 ->
            f g r s res1 res2 res3 res4 res5)))))))))


(** * Functions from gram.y **)

(** The function [R_atof] has not been formalised. We instead rely
  on the OCaml function [float_of_string]. **)
let mkFloat str : token_type = fun g _ s ->
  let (s, e) = scalarReal g s (float_of_string str) in
  Result_success (s, e)
let mkInt str : token_type = fun g _ s ->
  let (s, e) = scalarInteger g s (int_of_string str) in
  Result_success (s, e)
let mkComplex str : token_type = fun g _ s ->
  let c = {
      rcomplex_r = 0. ;
      rcomplex_i = float_of_string str
    } in
  let (s, e) = alloc_vector_cplx g s (ArrayList.from_list [c]) in
  Result_success (s, e)

(** When creating an integer, R checks whether floats would be more
  precise, and if so, uses floats instead. **)
let mkIntCheck str =
  let f = float_of_string str in
  if f = float_of_int (int_of_float f) then
    mkInt str
  else mkFloat str


(** * Interfacing functions **)

let unescaped_char = function
  | '\\' -> Some '\\'
  | '"' -> Some '"'
  | '\'' -> Some '\''
  | 'n' -> Some '\n'
  | 'r' -> Some '\r'
  | 't' -> Some '\t'
  | 'b' -> Some '\b'
  | 'a' -> Some '\007'
  | 'f' -> Some '\012'
  | 'v' -> Some '\011'
  | '\n' -> Some '\n'
  | '`' -> Some '`'
  | _ -> None

let is_hexa c =
  (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

let is_octal c =
  c >= '0' && c <= '7'

let hex_meaning c =
  if c >= '0' && c <= '9' then int_of_char c - int_of_char '0'
  else if c >= 'a' && c <= 'f' then 10 + int_of_char c - int_of_char 'a'
  else if c >= 'A' && c <= 'F' then 10 + int_of_char c - int_of_char 'A'
  else assert false

let octal_meaning c =
  assert (is_octal c) ;
  hex_meaning c

let rec unescaped_R = function
  | [] -> []
  | '\\' :: 'x' :: h1 :: h2 :: l when is_hexa h1 && is_hexa h2 ->
    char_of_int (16 * hex_meaning h1 + hex_meaning h2) :: unescaped_R l
  | '\\' :: 'x' :: h1 :: l when is_hexa h1 ->
    char_of_int (hex_meaning h1) :: unescaped_R l
  | '\\' :: o1 :: o2 :: o3 :: l when is_octal o1 && is_octal o2 && is_octal o3 ->
    char_of_int (8 * 8 * octal_meaning o1 + 8 * octal_meaning o2 + octal_meaning o3) :: unescaped_R l
  | '\\' :: o1 :: o2 :: l when is_octal o1 && is_octal o2 ->
    char_of_int (8 * octal_meaning o1 + octal_meaning o2) :: unescaped_R l
  | '\\' :: c :: l when unescaped_char c <> None ->
    (match unescaped_char c with
     | Some c -> c :: unescaped_R l
     | None -> assert false)
  | '\\' :: l -> failwith "Unrecognised escape in character string."
  | c :: l -> c :: unescaped_R l


(** * Global variables used in the parser **)

(** The original file main/gram.y heavily uses imperative features of C.
  These features interacts with the lexer/parser in non trivial ways.
  The imperative variables declared here mimick these behaviours. **)

let eatLines = ref false

type contextp_type =
  | Contextp_Par (** '(' in the C. **)
  | Contextp_SqBra (** '[' in the C. **)
  | Contextp_Bra (** LBRACE in the C. **)
  | Contextp_If (** 'i' in the C. **)
  | Contextp_Empty (** ' ' or 0 in the C. **)

let contextp = ref [Contextp_Empty]

let contextp_hd () =
  match !contextp with
  | [] -> failwith "[parser] The variable “contextp” has no head."
  | i :: _ -> i

let contextp_pop () =
  match !contextp with
  | [] -> failwith "[parser] The variable “contextp” can’t be popped."
  | _ :: l -> contextp := l

let ifpop () =
  if contextp_hd () = Contextp_If then contextp_pop ()

let ifpush () =
  match contextp_hd () with
  | Contextp_Bra
  | Contextp_SqBra
  | Contextp_Par
  | Contextp_If -> contextp := Contextp_If :: !contextp
  | _ -> ()

let wifpop () =
  while contextp_hd () = Contextp_If do ifpop () done

let parseInit () =
  contextp := [Contextp_Empty] ;
  eatLines := false

