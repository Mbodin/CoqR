(** Extraction.
 * Extract R interpreter into OCaml. **)

Require Export Rfeatures Rinit.

Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

(* TODO: Clean. *)
(* As classical logic statements are now unused, they should not be extracted
   (otherwise, useless errors will be launched). *)
Extraction Inline (*epsilon epsilon_def*) classicT arbitrary indefinite_description (*Inhab_witness*) Fix isTrue.

Extraction "low.ml" setup_Rmainloop empty_state.

