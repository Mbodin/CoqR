
type arrow =
  | Often
  | Normal
  | Rare

type token =
  | Str of string
  | Id of string

type rule =
  string * arrow * token list

type rule_automaton =
  (string *
    (token list list (** Often **)
    * token list list (** Normal **)
    * token list list (** Rare **))) list

