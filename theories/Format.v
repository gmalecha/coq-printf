Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
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
  : for_good er k :=
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

(** Encoded number format. *)
Variant number_enctype : Type :=
| Binary
| Octal
| Decimal
| HexLower
| HexUpper
.

(** Decoded type. *)
Variant number_dectype : Type :=
| T_Nat
| T_N
.

(** Data type of a specifier. *)
Variant type : Type :=
| Number : number_enctype -> number_dectype -> type
| SDecimal (* Signed decimal number, with type Z *)
| String
| Char
.

(** Well-formed format strings *)
Inductive t : Type :=
| Empty
| Literal : ascii -> t -> t
| Hole : type -> options -> t -> t
.

Local Variant spec_state : Type :=
| Flags
| Width
| TySpec (t : number_dectype)
.

(** Parser state machine. *)
Local Variant state : Type :=
| Ini                                  (* Initial state *)
| Spec (j : spec_state) (o : options)  (* Parsing specifier *)
  (* [j]: inner specifier parsing state *)
  (* [o]: currently accumulated options *)
.

(** Parser error: dump the remaining string, that serves to locate the error. *)
Variant error : Type :=
| ErrorAt (i : state) (s : string)
.

(** Parse string [s] in state [i] into a format which is passed to the final
  continuation [k], or return an error. *)
Local Fixpoint parse_ {r : Type} (i : state) (k : t -> r) (s0 : string)
  : error + r :=
  match i, s0 with
    (* The initial state looks for ["%"], indicating a specifier,
       and keeps the rest as literal. *)
  | Ini, "" => inr (k Empty)
  | Ini, "%" :: "%" :: s => parse_ Ini (fun fmt => k (Literal "%" fmt)) s
  | Ini, "%" :: s => parse_ (Spec Flags default_options) k s
  | Ini, c :: s => parse_ Ini (fun fmt => k (Literal c fmt)) s

  | Spec _ _, "" => inl (ErrorAt i s0)
  | Spec j o, a :: s =>
    (* When parsing a specifier, the next character is either:
       - a specifier character, then update the format and go back to the initial state;
       - or a flag (or width) character, then update the options accordingly. *)
    let specifier (t : type) := parse_ Ini (fun fmt => k (Hole t o fmt)) s in
    let flag (j : spec_state) (o : options) := parse_ (Spec j o) k s in
    let typ (t : number_dectype) := parse_ (Spec (TySpec t) o) k s in
    let number b := Number b
      match j with
      | TySpec t => t
      | _ => T_Nat
      end in
    match a, j with
    | "s", _ => specifier String
    | "c", _ => specifier Char
    | "b", _ => specifier (number Binary)
    | "o", _ => specifier (number Octal)
    | "d", _ => specifier (number Decimal)
    | "x", _ => specifier (number HexLower)
    | "X", _ => specifier (number HexUpper)
    | "N", _ => typ T_N
    | "Z", (Flags | Width) =>
      match s with
      | "d" :: s => parse_ Ini (fun fmt => k (Hole SDecimal o fmt)) s
      | _ => inl (ErrorAt i s0)
      end
    | "-", Flags => flag Flags (update_option_justify o LeftJustify)
    | "+", Flags => flag Flags (update_option_sign o true)
    | " ", Flags => flag Flags (update_option_space o true)
    | "#", Flags => flag Flags (update_option_prefix o true)
    | "0", Flags => flag Flags (update_option_zero_pad o true)
    | ("1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"), (Flags | Width)
    | "0", Width  => flag Width (update_option_width o (ascii_digit a))
    | _, _ => inl (ErrorAt i s0)
    end%char
  end%string.

Definition parse : string -> error + t := parse_ Ini id.

Definition dectype_type (t : number_dectype) : Type :=
  match t with
  | T_Nat => nat
  | T_N => N
  end.

Definition hole_type (ty : type) : Type :=
  match ty with
  | Number _ t => dectype_type t
  | SDecimal => Z
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
