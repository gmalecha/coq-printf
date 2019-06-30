(** Numbers represented as lists of digits. *)

Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Local Open Scope N.

Inductive digits : Set :=
| Zero
| Digit : digits -> N -> digits
.

Arguments digits : clear implicits.

Section Digits.

Context (base : N).

(** Add two digits and a carry *)
Definition adder (d d0 c : N) : N * N :=
  let s := c + d + d0 in
  if s <? base then (0, s) else (1, s - base).

(* [2 * n + d0] *)
Fixpoint double_plus (c : N) (n : digits) :=
  match n with
  | Zero =>
    if c =? 0 then Zero else Digit Zero c
  | Digit n d =>
    let (c, d) := adder d d c in
    Digit (double_plus c n) d
  end.

Fixpoint digits_of_pos (p : positive) :=
  match p with
  | xH => Digit Zero 1
  | xI p => double_plus 1 (digits_of_pos p)
  | xO p => double_plus 0 (digits_of_pos p)
  end.

Definition digits_of_N (n : N) :=
  match n with
  | N0 => Digit Zero 0
  | Npos p => digits_of_pos p
  end.

End Digits.

Definition binary_ascii (n : N) : ascii :=
  match n with
  | 0 =>  "0"%char
  | _ =>  "1"%char
  end.

Definition octal_ascii (n : N) : ascii :=
  match n with
  | 0 =>  "0"%char
  | 1 =>  "1"%char
  | 2 =>  "2"%char
  | 3 =>  "3"%char
  | 4 =>  "4"%char
  | 5 =>  "5"%char
  | 6 =>  "6"%char
  | _ =>  "7"%char
  end.

Definition decimal_ascii (n : N) : ascii :=
  match n with
  | 8 =>  "8"%char
  | 9 =>  "9"%char
  | _ => octal_ascii n
  end.

Definition hex_ascii (n : N) : ascii :=
  match n with
  | 10 => "a"%char
  | 11 => "b"%char
  | 12 => "c"%char
  | 13 => "d"%char
  | 14 => "e"%char
  | 15 => "f"%char
  | _  => decimal_ascii n
  end.

Definition hex_ascii_upper (n : N) : ascii :=
  match n with
  | 10 => "A"%char
  | 11 => "B"%char
  | 12 => "C"%char
  | 13 => "D"%char
  | 14 => "E"%char
  | 15 => "F"%char
  | _  => decimal_ascii n
  end.

Local Fixpoint string_of_digits_
    (digit : N -> ascii)
    (s : string)
    (n : digits)
  : string
  :=
  match n with
  | Zero => s
  | Digit n d => string_of_digits_ digit (String (digit d) s) n
  end.

Definition string_of_digits (digit : N -> ascii) : digits -> string :=
  string_of_digits_ digit "".

Definition string_of_N (base : N) (digit : N -> ascii) (n : N) : string :=
  string_of_digits digit (digits_of_N base n).
