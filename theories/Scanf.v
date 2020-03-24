Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Printf.Justify.
Require Import Printf.Flags.
Require Import Printf.Format.

Require Export Printf.FormatNotations.

Set Primitive Projections.

Local Infix "::" := String : string_scope.

Definition fmt_parser (R : Type) (fmt : Format.t) : Type :=
  Format.holes (string -> option R) fmt -> string -> option R.

Definition parser (R A : Type) : Type :=
  (A -> string -> option R) -> string -> option R.

Definition base (ty : Format.number_enctype) : N :=
  match ty with
  | Format.Binary => 2
  | Format.Octal => 8
  | Format.Decimal => 10
  | Format.HexLower | Format.HexUpper => 16
  end.

Module Read.

Local Open Scope N.
Local Open Scope char.

Definition binary (c : ascii) : option N :=
  if c =? "0" then Some 0
  else if c =? "1" then Some 1
  else None.

Definition octal (c : ascii) : option N :=
  if c =? "0" then Some 0
  else if c =? "1" then Some 1
  else if c =? "2" then Some 2
  else if c =? "3" then Some 3
  else if c =? "4" then Some 4
  else if c =? "5" then Some 5
  else if c =? "6" then Some 6
  else if c =? "7" then Some 7
  else None.

Definition decimal (c : ascii) : option N :=
  if c =? "0" then Some 0
  else if c =? "1" then Some 1
  else if c =? "2" then Some 2
  else if c =? "3" then Some 3
  else if c =? "4" then Some 4
  else if c =? "5" then Some 5
  else if c =? "6" then Some 6
  else if c =? "7" then Some 7
  else if c =? "8" then Some 8
  else if c =? "9" then Some 9
  else None.

Definition hex (c : ascii) : option N :=
  if c =? "0" then Some 0
  else if c =? "1" then Some 1
  else if c =? "2" then Some 2
  else if c =? "3" then Some 3
  else if c =? "4" then Some 4
  else if c =? "5" then Some 5
  else if c =? "6" then Some 6
  else if c =? "7" then Some 7
  else if c =? "8" then Some 8
  else if c =? "9" then Some 9
  else if ((c =? "a")%char || (c =? "A")%char)%bool then Some 10
  else if ((c =? "b")%char || (c =? "B")%char)%bool then Some 11
  else if ((c =? "c")%char || (c =? "C")%char)%bool then Some 12
  else if ((c =? "d")%char || (c =? "D")%char)%bool then Some 13
  else if ((c =? "e")%char || (c =? "E")%char)%bool then Some 14
  else if ((c =? "f")%char || (c =? "F")%char)%bool then Some 15
  else None.

Definition digit (ty : Format.number_enctype) : ascii -> option N :=
  match ty with
  | Format.Binary => binary
  | Format.Octal => octal
  | Format.Decimal => decimal
  | Format.HexLower | Format.HexUpper => hex
  end.

End Read.

Section Parser.

Local Open Scope string.

Context {R : Type}.

(** The body of the recursive definitions of [parse_N] and [parse_N'].
  If the next character is a digit, accumulate it into [x] and call [continue]
  on the updated state and the remaining string.
  Else if the state [x] is empty, fail.
  Otherwise, terminate by calling [k].

  To ensure the subsequent definitions are guarded, [continue] is applied to a
  subterm of [s0].
  *)
Local Definition parse_N_ (base : N) (digit : ascii -> option N)
    (k : N -> string -> option R)
    (continue : option N -> string -> option R)
    (x : option N)
    (s0 : string)
  : option R :=
  match s0 with
  | "" =>
    match x with
    | None => None
    | Some n => k n ""
    end
  | c :: s =>
    match digit c with
    | None =>
      match x with
      | None => None
      | Some n => k n s0
      end
    | Some d =>
      match x with
      | None => continue (Some d) s
      | Some n => continue (Some (n * base + d)%N) s
      end
    end
  end.

(** Parse a number given a translation from characters to numbers. *)
Definition parse_N (base : N) (digit : ascii -> option N) : parser R N := fun k =>
  let fix _parse_N (x : option N) (s0 : string) :=
    parse_N_ base digit k _parse_N x s0
  in _parse_N None.

(** Parse a number of at most [w] characters. *)
Definition parse_N' (w : nat) (base : N) (digit : ascii -> option N)
  : parser R N :=
  fun k =>
  let fix _parse_N (w : nat) (x : option N) (s0 : string) :=
    match w with
    | O =>
      match x with
      | None => None
      | Some n => k n s0
      end
    | S w => parse_N_ base digit k (_parse_N w) x s0
    end
  in _parse_N w None.

Definition parse_char : parser R ascii := fun k s =>
  match s with
  | "" => None
  | c :: s => k c s
  end.

Definition parse_this_char (c : ascii)
  : parser R unit :=
  fun k s =>
  match s with
  | "" => None
  | c' :: s =>
    if Ascii.ascii_dec c c'
    then k tt s
    else None
  end.

Definition is_whitespace (c : ascii) : bool :=
  (c =? " ")%char ||
  (c =? "009")%char ||
  (c =? "010")%char ||
  (c =? "011")%char ||
  (c =? "012")%char ||
  (c =? "013")%char.

Definition parse_whitespace : parser R unit := fun k =>
  fix consume s0 :=
    match s0 with
    | c :: s =>
      if is_whitespace c then consume s else k tt s0
    | _ => k tt s0
    end.

(** Body of the recursive definition of [parse_string] and [parse_string']. *)
Local Definition parse_string_
    (continue : parser R string)
    (k : string -> string -> option R)
    (s0 : string)
  : option R :=
  match s0 with
  | "" => k "" s0
  | c :: s =>
    if is_whitespace c
    then k "" s0
    else continue (fun z => k (c :: z)) s
  end.

(** Read up to the next whitespace character *)
Definition parse_string : parser R string :=
  fix _parse_string k (s : string) :=
    parse_string_ _parse_string k s.

(** Read at most [w] characters up to the next whitespace character. *)
Definition parse_string' : nat -> parser R string :=
  fix _parse_string w k (s : string) :=
    match w with
    | O => k "" s
    | S w => parse_string_ (_parse_string w) k s
    end.

Definition parse_number
    (b : Format.number_enctype)
    (t : Format.number_dectype)
    (o : options)
  : parser R (Format.dectype_type t) :=
  fun k s =>
  let parse :=
    match option_width o with
    | None => parse_N
    | Some w => parse_N' w
    end
  in
  let from_N : N -> Format.dectype_type t :=
    match t return _ -> _ t with
    | Format.T_Nat => N.to_nat
    | Format.T_N => id
    end in
  let continue s := parse (base b) (Read.digit b) (fun n => k (from_N n)) s in
  match b, s with
  | (Format.HexLower | Format.HexUpper), (c1 :: c2 :: s2) as s =>
    if ((c1 =? "0")%char && ((c2 =? "x")%char || (c2 =? "X")%char))%bool
    then continue s2
    else continue s
  | _, c1 :: s1 =>
    if (c1 =? "+")%char
    then continue s1
    else continue s
  | _, _ => continue s
  end.

Definition parse_signed
    (o : options)
  : parser R Z :=
  fun k s =>
  let parse :=
    match option_width o with
    | None => parse_N
    | Some w => parse_N' w
    end 10%N Read.decimal
  in
  let parse_minus s := parse (fun n => k (Z.opp (Z.of_N n))) s in
  let parse_plus s := parse (fun n => k (Z.of_N n)) s in
  match s with
  | c :: s' =>
    if (c =? "-")%char then parse_minus s'
    else if (c =? "+")%char then parse_plus s'
    else parse_plus s
  | _ => parse_plus s
  end.

Definition parse_hole (ty : Format.type) (o : options)
  : parser R (Format.hole_type ty) :=
  match ty with
  | Format.String =>
    match option_width o with
    | None => parse_string
    | Some w => parse_string' w
    end
  | Format.Char => parse_char
  | Format.Number b t => parse_number b t o
  | Format.SDecimal => parse_signed o
  end.

Fixpoint sscanf (fmt : Format.t)
  : fmt_parser R fmt :=
  match fmt with
  | Format.Empty => fun k => k
  | Format.Literal c fmt => fun k =>
    if (c =? " ")%char
    then parse_whitespace (fun _ => sscanf fmt k)
    else parse_this_char c (fun _ => sscanf fmt k)
  | Format.Hole ty o fmt => fun k => parse_hole ty o (fun x => sscanf fmt (k x))
  end.

End Parser.
