(** * Notations for [Format.t] *)

(** Reexport only the notations. *)

Require Import Printf.Format.
Require Import Printf.FormatParser.

Declare Scope fmt_scope.
Delimit Scope fmt_scope with fmt.
Bind Scope fmt_scope with Format.t.

String Notation Format.t parse_opt print : fmt_scope.
