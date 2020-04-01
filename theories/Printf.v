Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.

Require Import Printf.Justify.
Require Import Printf.Flags.
Require Import Printf.Format.
Require Import Printf.Digits.

Require Export Printf.FormatNotations.

Set Primitive Projections.

Local Infix "::" := String : string_scope.

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

Local Open Scope N.

(* prefix *)
Definition prefix_string (o : options) (prefix : string) (n : N) (s : string) : string :=
  match n with
  | 0 => s
  | _ => if option_prefix o then
             append prefix s
           else
             s
  end.

(* helper methods to format *)
Definition format_s
           (o : options)
           (s : string)
           (x : string) : string :=
  let text := justify_string o s in
  (String.append text x).

Definition format_nat
           (f : N -> string)
           (prefix : option string)
           (o : options)
           (n : N) : string -> string :=
  let text := f n in
  let text := match prefix with
              | Some prefix' => prefix_string o prefix' n text
              | None => text
              end in
  format_s o text.

Definition format_b : options -> N -> string -> string :=
  format_nat binary_string None.

Definition format_o : options -> N -> string -> string :=
  format_nat octal_string (Some "0"%string).

Definition format_d (o : options) : N -> string -> string :=
  format_nat (fun (n : N) => sign_string o (decimal_string n)) None o.

Definition format_x : options -> N -> string -> string :=
  format_nat hex_string (Some "0x"%string).

Definition format_X : options -> N -> string -> string :=
  format_nat hex_string_upper (Some "0X"%string).

Definition format_number (b : Format.number_enctype) (t : Format.number_dectype)
  : options -> Format.dectype_type t -> string -> string :=
  fun o =>
  let format_ :=
    match b with
    | Format.Binary => format_b
    | Format.Octal => format_o
    | Format.Decimal => format_d
    | Format.HexLower => format_x
    | Format.HexUpper => format_X
    end o in
  match t as t0 return Format.dectype_type t0 -> _ with
  | Format.T_Nat => fun n => format_ (N.of_nat n)
  | Format.T_N => fun n => format_ n
  end.

Definition format_Z : options -> Z -> string -> string :=
  fun o n =>
  let format_ := format_nat decimal_string None o in
  match n with
  | Z0 => format_ 0
  | Zpos p => fun s =>
    if option_sign o
    then ("+" :: format_ (Npos p) s)%string
    else         format_ (Npos p) s
  | Zneg p => fun s => ("-" :: format_ (Npos p) s)%string
  end.

Definition format (ty : Format.type)
  : options -> Format.hole_type ty -> string -> string :=
  match ty return _ -> Format.hole_type ty -> _ with
  | Format.Number b t => format_number b t
  | Format.SDecimal => format_Z
  | Format.String => format_s
  | Format.Char => fun o c => format_s o (c :: "")
  end.

Fixpoint sprintf' (acc : string -> string) (fmt : Format.t)
  : Format.holes string fmt :=
  match fmt return Format.holes string fmt with
  | Format.Empty => acc ""%string
  | Format.Literal c fmt => sprintf' (fun s => acc (c :: s)%string) fmt
  | Format.Hole ty o fmt => fun x => sprintf' (fun s => acc (format ty o x s)) fmt
  end.

Definition sprintf (fmt : Format.t) : Format.holes string fmt :=
  sprintf' id fmt.
