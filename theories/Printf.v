Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Wf.
Require Import Coq.Program.Basics.

Require Import Printf.Justify.
Require Import Printf.Flags.
Require Import Printf.Format.

Set Primitive Projections.

(* Justify *)
Definition justify_string (o : options) (s : string) : string :=
  let a := if option_zero_pad o then "0"%char else " "%char in
  match option_width o with
  | None => s
  | Some width =>
    match option_justify o with
    | LeftJustify => left_justify_string a width s
    | RightJustify => right_justify_string a width s
    end
  end.

(* sign *)
Definition sign_string (o : options) (s : string) : string :=
  match(option_sign o,option_space o) with
  | (true,_) => String "+" s
  | (_,true) => String " " s
  | (_,_) => s
  end.

(* prefix *)
Definition prefix_string (o : options) (prefix : string) (n : nat) (s : string) : string :=
  match n with
  | 0 => s
  | S _ => if option_prefix o then
             append prefix s
           else
             s
  end.

Definition binary_ascii (n : nat) : ascii :=
  match n with
  | 0 =>  "0"%char
  | _ =>  "1"%char
  end.

Definition octal_ascii (n : nat) : ascii :=
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

Definition decimal_ascii (n : nat) : ascii :=
  match n with
  | 8 =>  "8"%char
  | 9 =>  "9"%char
  | _ => octal_ascii n
  end.

Definition hex_ascii (n : nat) : ascii :=
  match n with
  | 10 => "a"%char
  | 11 => "b"%char
  | 12 => "c"%char
  | 13 => "d"%char
  | 14 => "e"%char
  | 15 => "f"%char
  | _  => decimal_ascii n
  end.

Definition hex_ascii_upper (n : nat) : ascii :=
  match n with
  | 10 => "A"%char
  | 11 => "B"%char
  | 12 => "C"%char
  | 13 => "D"%char
  | 14 => "E"%char
  | 15 => "F"%char
  | _  => decimal_ascii n
  end.

Program Fixpoint nat_to_string
         (base : nat | 1 < base)
         (to_digit : nat -> ascii)
         (acc: string)
         (n:nat) {measure n}
         : string :=
  let acc' := (String (to_digit (n mod base)) acc) in
  if Compare_dec.le_gt_dec n (base - 1) then
    acc'
  else
    nat_to_string base to_digit acc' (n / base)
.
Next Obligation.
  eapply Nat.div_lt.
  assert(base - 1 > 0).
  apply Minus.lt_O_minus_lt.
  rewrite <- Minus.minus_n_O.
  apply Lt.lt_S_n.
  rewrite <- Minus.pred_of_minus.
  assert (Ha' := Nat.lt_succ_pred 1 base).
  rewrite Ha'; assumption.
  assert (Hb' := Gt.gt_trans n (base - 1) 0).
  apply Hb'; assumption.
  assumption.
Qed.

Program Definition binary_string (n : nat) :=
  nat_to_string 2 binary_ascii EmptyString n.


Program Definition hex_string (n : nat) :=
  nat_to_string 16 hex_ascii EmptyString n.
Next Obligation.
  apply Lt.lt_n_S; apply Gt.gt_Sn_O.
Defined.

Program Definition hex_string_upper (n : nat) :=
  nat_to_string 16 hex_ascii_upper EmptyString n.
Next Obligation.
  apply Lt.lt_n_S; apply Gt.gt_Sn_O.
Defined.

Program Definition octal_string (n : nat) :=
  nat_to_string 8 octal_ascii EmptyString n.
Next Obligation.
  apply Lt.lt_n_S; apply Gt.gt_Sn_O.
Defined.

Program Definition decimal_string (n : nat) :=
  nat_to_string 10 decimal_ascii EmptyString n.
Next Obligation.
  apply Lt.lt_n_S; apply Gt.gt_Sn_O.
Defined.

(* helper methods to format *)
Definition format_s
           (o : options)
           (s : string)
           (x : string) : string :=
  let text := justify_string o s in
  (String.append text x).

Definition format_nat
           (f : nat -> string)
           (prefix : option string)
           (o : options)
           (n : nat) : string -> string :=
  let text := f n in
  let text := match prefix with
              | Some prefix' => prefix_string o prefix' n text
              | None => text
              end in
  format_s o text.

Definition format_b : options -> nat -> string -> string :=
  format_nat binary_string None.

Definition format_o : options -> nat -> string -> string :=
  format_nat octal_string (Some "0"%string).

Definition format_d (o : options) : nat -> string -> string :=
  format_nat (fun (n : nat) => sign_string o (decimal_string n)) None o.

Definition format_x : options -> nat -> string -> string :=
  format_nat hex_string (Some "0x"%string).

Definition format_X : options -> nat -> string -> string :=
  format_nat hex_string_upper (Some "0X"%string).

Definition format (ty : Format.type)
  : options -> Format.hole_type ty -> string -> string
  :=
  match ty return _ -> Format.hole_type ty -> _ with
  | Format.Number Format.Binary => format_b
  | Format.Number Format.Octal => format_o
  | Format.Number Format.Decimal => format_d
  | Format.Number Format.HexLower => format_x
  | Format.Number Format.HexUpper => format_X
  | Format.String => format_s
  | Format.Char => fun o c => format_s o (c :: "")
  end.

Local Fixpoint sprintf' (acc : string -> string) (fmt : Format.t)
  : Format.holes string fmt
  :=
  match fmt return Format.holes string fmt with
  | Format.Empty => acc ""%string
  | Format.Literal c fmt => sprintf' (fun s => acc (c :: s)%string) fmt
  | Format.Hole ty o fmt => fun x => sprintf' (fun s => acc (format ty o x s)) fmt
  end.

Definition sprintf (s : string) : for_good (Format.parse s) (Format.holes string) :=
  on_success (sprintf' id).
