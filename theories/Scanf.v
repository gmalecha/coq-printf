Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Printf.Justify.
Require Import Printf.Flags.
Require Import Printf.Format.

Set Primitive Projections.

Definition fmt_parser (R : Type) (fmt : Format.t) : Type :=
  Format.holes (string -> option R) fmt -> string -> option R.

Definition parser (R A : Type) : Type :=
  (A -> string -> option R) -> string -> option R.

Definition base (ty : Format.number_type) : N :=
  match ty with
  | Format.Binary => 2
  | Format.Octal => 8
  | Format.Decimal => 10
  | Format.HexLower | Format.HexUpper => 16
  end.

Module Read.

Local Open Scope char.
Local Open Scope N.

Definition binary (c : ascii) : option N :=
  match c with
  | "0" => Some 0
  | "1" => Some 1
  | _ => None
  end.

Definition octal (c : ascii) : option N :=
  match c with
  | "0" => Some 0
  | "1" => Some 1
  | "2" => Some 2
  | "3" => Some 3
  | "4" => Some 4
  | "5" => Some 5
  | "6" => Some 6
  | "7" => Some 7
  | _ => None
  end.

Definition decimal (c : ascii) : option N :=
  match c with
  | "0" => Some 0
  | "1" => Some 1
  | "2" => Some 2
  | "3" => Some 3
  | "4" => Some 4
  | "5" => Some 5
  | "6" => Some 6
  | "7" => Some 7
  | "8" => Some 8
  | "9" => Some 9
  | _ => None
  end.

Definition hex (c : ascii) : option N :=
  match c with
  | "0" => Some 0
  | "1" => Some 1
  | "2" => Some 2
  | "3" => Some 3
  | "4" => Some 4
  | "5" => Some 5
  | "6" => Some 6
  | "7" => Some 7
  | "8" => Some 8
  | "9" => Some 9
  | "a" | "A" => Some 10
  | "b" | "B" => Some 11
  | "c" | "C" => Some 12
  | "d" | "D" => Some 13
  | "e" | "E" => Some 14
  | "f" | "F" => Some 15
  | _ => None
  end.

Definition digit (ty : Format.number_type) : ascii -> option N :=
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
  : option R
  :=
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
  : parser R N
  := fun k =>
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
  : parser R unit
  := fun k s =>
  match s with
  | "" => None
  | c' :: s =>
    if Ascii.eqb c c'
    then k tt s
    else None
  end.

Definition is_whitespace (c : ascii) : bool :=
  match c with
  | " " | "009" | "010" | "011" | "012" | "013" => true
  | _ => false
  end%char.

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
  : option R
  :=
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

Definition parse_hole (ty : Format.type) (o : options)
  : parser R (Format.hole_type ty)
  :=
  match ty with
  | Format.String =>
    match option_width o with
    | None => parse_string
    | Some w => parse_string' w
    end
  | Format.Char => parse_char
  | Format.Number b
    => fun k s =>
      let parse :=
        match option_width o with
        | None => parse_N
        | Some w => parse_N' w
        end
      in
      match b, s with
      | (Format.HexLower | Format.HexUpper), "0" :: ("x" | "X") :: s
      | _, "+" :: s
      | _, s
        => parse (base b) (Read.digit b) (fun n => k (N.to_nat n)) s
      end
  end.

Local Fixpoint parse_fmt (fmt : Format.t)
  : fmt_parser R fmt
  :=
  match fmt with
  | Format.Empty => fun k => k
  | Format.Literal " " fmt => fun k => parse_whitespace (fun _ => parse_fmt fmt k)
  | Format.Literal c fmt => fun k => parse_this_char c (fun _ => parse_fmt fmt k)
  | Format.Hole ty o fmt => fun k => parse_hole ty o (fun x => parse_fmt fmt (k x))
  end.

Definition sscanf (s : string) : for_good (Format.parse s) (fmt_parser R) :=
  on_success parse_fmt.

End Parser.
