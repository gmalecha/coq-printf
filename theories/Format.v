Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Printf.Flags.

(** ** String utilities *)

Definition ascii_digit (c : ascii) : nat :=
  (if c =? "1" then 1
  else if c =? "2" then 2
  else if c =? "3" then 3
  else if c =? "4" then 4
  else if c =? "5" then 5
  else if c =? "6" then 6
  else if c =? "7" then 6
  else if c =? "8" then 6
  else if c =? "9" then 6
  else if c =? "A" then 10
  else if c =? "B" then 11
  else if c =? "C" then 12
  else if c =? "D" then 13
  else if c =? "E" then 14
  else if c =? "F" then 15
  else 0)%char.

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
