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

Local Infix "::" := String : string_scope.

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

Variant spec_state : Type :=
| Flags
| Width
| TySpec (t : number_dectype)
.

(** Parser state machine. *)
Variant state : Type :=
| Ini                                  (* Initial state *)
| Spec (j : spec_state) (o : options)  (* Parsing specifier *)
  (* [j]: inner specifier parsing state *)
  (* [o]: currently accumulated options *)
.

(** Parser error: dump the remaining string, that serves to locate the error. *)
Variant error : Type :=
| ErrorAt (i : state) (s : string)
.

Definition digit1to9 (c : ascii) : bool :=
  (c =? "1")%char ||
  (c =? "2")%char ||
  (c =? "3")%char ||
  (c =? "4")%char ||
  (c =? "5")%char ||
  (c =? "6")%char ||
  (c =? "7")%char ||
  (c =? "8")%char ||
  (c =? "9")%char.

Definition isFlagsOrWidth (j : _) : bool :=
  match j with
  | Flags | Width => true
  | TySpec _ => false
  end.

Definition isWidth (j : _) : bool :=
  match j with
  | Width => true
  | Flags | TySpec _ => false
  end.

Definition isFlags (j : _) : bool :=
  match j with
  | Flags => true
  | Width | TySpec _ => false
  end.

(** Parse string [s] in state [i] into a format which is passed to the final
  continuation [k], or return an error. *)
Local Fixpoint parse_ {r : Type} (i : state) (k : t -> r) (s0 : string)
  : error + r :=
  match i, s0 with
    (* The initial state looks for ["%"], indicating a specifier,
       and keeps the rest as literal. *)
  | Ini, ""%string => inr (k Empty)
  | Ini, c :: s =>
    if (c =? "%")%char then
      let continue (_ : unit) := parse_ (Spec Flags default_options) k s in
      match s with
      | c' :: s =>
        if (c' =? "%")%char then parse_ Ini (fun fmt => k (Literal "%" fmt)) s
        else continue tt
      | _ => continue tt
      end
    else
      parse_ Ini (fun fmt => k (Literal c fmt)) s

  | Spec _ _, ""%string => inl (ErrorAt i s0)
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
    if a =? "s" then specifier String
    else if a =? "c" then specifier Char
    else if a =? "b" then specifier (number Binary)
    else if a =? "o" then specifier (number Octal)
    else if a =? "d" then specifier (number Decimal)
    else if a =? "x" then specifier (number HexLower)
    else if a =? "X" then specifier (number HexUpper)
    else if a =? "N" then typ T_N
    else if a =? "Z" then
      match j, s with
      | (Flags | Width), c :: s => if c =? "d"%char then parse_ Ini (fun fmt => k (Hole SDecimal o fmt)) s
        else inl (ErrorAt i s0)
      | _, _ => inl (ErrorAt i s0)
      end
    else if ((digit1to9 a && isFlagsOrWidth j) || ((a =? "0")%char && isWidth j))%bool then
      flag Width (update_option_width o (ascii_digit a))
    else
    match j with
    | Flags =>
      if a =? "-" then flag Flags (update_option_justify o LeftJustify)
      else if a =? "+" then flag Flags (update_option_sign o true)
      else if a =? " " then flag Flags (update_option_space o true)
      else if a =? "#" then flag Flags (update_option_prefix o true)
      else if a =? "0" then flag Flags (update_option_zero_pad o true)
      else inl (ErrorAt i s0)
    | _ => inl (ErrorAt i s0)
    end
  end%char%string.

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
