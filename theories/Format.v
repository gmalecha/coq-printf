Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Printf.Flags.

(** ** Error handling in dependent types *)

(** This tagged unit type indicates an error in the computation of a type. *)
Variant tyerror {A : Type} (a : A) : Set := Invalid.

(** Construct a dependent type from a computation which may fail. *)
Definition for_good {E R : Type} (er : E + R) (k : R -> Type) : Type :=
  match er with
  | inl e => tyerror e
  | inr r => k r
  end.

(** Apply a dependent function to the result of a computation when it is successful. *)
Definition on_success {E R : Type} {er : E + R} {k : R -> Type} (f : forall r, k r)
  : for_good er k
  :=
  match er with
  | inl e => Invalid e
  | inr r => f r
  end.

(** ** String utilities *)

Infix "::" := String : string_scope.

Definition ascii_digit (c : ascii) : nat :=
  match c with
  | "0" => 0
  | "1" => 1
  | "2" => 2
  | "3" => 3
  | "4" => 4
  | "5" => 5
  | "6" => 6
  | "7" => 7
  | "8" => 8
  | "9" => 9
  | "a" | "A" => 10
  | "b" | "B" => 11
  | "c" | "C" => 12
  | "d" | "D" => 13
  | "e" | "E" => 14
  | "f" | "F" => 15
  | _ => 0
  end%char.

(** ** Format strings *)

Module Format.

Variant number_type : Type :=
| Binary
| Octal
| Decimal
| HexLower
| HexUpper
.

Variant type : Type :=
| Number : number_type -> type
| String
| Char
.

(** Well-formed format strings *)
Inductive t : Type :=
| Empty
| Literal : ascii -> t -> t
| Hole : type -> options -> t -> t
.

(** Parser state machine. *)
Local Variant state : Type :=
| Ini                                   (* Initial state *)
| Spec (inWidth : bool) (o : options)  (* Parsing specifier *)
  (* [inWidth]: [true] if we're in the middle of the width segment *)
  (* [o]: currently accumulated options *)
.

(** Parser error: dump the remaining string, that serves to locate the error. *)
Variant error : Type :=
| ErrorAt (i : state) (s : string)
.

(** Parse string [s] in state [i] into a format which is passed to the final
  continuation [k], or return an error. *)
Local Fixpoint parse_ {r : Type} (i : state) (k : t -> r) (s0 : string)
  : error + r
  :=
  match i, s0 with
    (* The initial state looks for ["%"], indicating a specifier,
       and keeps the rest as literal. *)
  | Ini, "" => inr (k Empty)
  | Ini, "%" :: "%" :: s => parse_ Ini (fun fmt => k (Literal "%" fmt)) s
  | Ini, "%" :: s => parse_ (Spec false default_options) k s
  | Ini, c :: s => parse_ Ini (fun fmt => k (Literal c fmt)) s

  | Spec _ _, "" => inl (ErrorAt i s0)
  | Spec w o, a :: s =>
    (* When parsing a specifier, the next character is either:
       - a specifier character, then update the format and go back to the initial state;
       - or a flag (or width) character, then update the options accordingly. *)
    let specifier (t : type) := parse_ Ini (fun fmt => k (Hole t o fmt)) s in
    let flag (inWidth : bool) (o : options) := parse_ (Spec inWidth o) k s in
    match a, w with
    | "s", _ => specifier String
    | "c", _ => specifier Char
    | "b", _ => specifier (Number Binary)
    | "o", _ => specifier (Number Octal)
    | "d", _ => specifier (Number Decimal)
    | "x", _ => specifier (Number HexLower)
    | "X", _ => specifier (Number HexUpper)
    | "-", false => flag false (update_option_justify o LeftJustify)
    | "+", false => flag false (update_option_sign o true)
    | " ", false => flag false (update_option_space o true)
    | "#", false => flag false (update_option_prefix o true)
    | "0", false => flag false (update_option_zero_pad o true)
    | ("1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"), _
    | "0", true  => flag true (update_option_width o (ascii_digit a))
    | _, _ => inl (ErrorAt i s0)
    end%char
  end%string.

Definition parse : string -> error + t := parse_ Ini id.

Definition hole_type (ty : type) : Type :=
  match ty with
  | Number _ => nat
  | String => string
  | Char => ascii
  end.

(** Type of continuations associated with format string [fmt],
    with result type [r]. *)
Fixpoint holes (r : Type) (fmt : t) : Type :=
  match fmt with
  | Empty => r
  | Hole ty _ fmt => hole_type ty -> holes r fmt
  | Literal _ fmt => holes r fmt
  end.

End Format.
