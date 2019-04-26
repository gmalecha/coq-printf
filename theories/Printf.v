Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Printf.Justify.
(* Require Import Coq.omega.Omega. *)

Require Import Coq.Program.Wf.
Inductive justify : Set := LeftJustify | RightJustify.
(*
 reference :
 http://www.cplusplus.com/reference/cstdio/printf/  *)
(* %[flags]     [width]  specifier  *)
(* %(-|+| |#|0)^* (\d+)    specifier  *)
Record options := { option_justify : justify ;        (* '-'   : left justify                   x *)
                          option_sign : bool ;        (* '+'   : precede with plus sign         x *)
                          option_space : bool ;       (* ' '   : space if no sign displayed     x *)
                          option_prefix : bool ;      (* '#'   : precede with o x X , 0 0x 0X
                                                                 for values different than zero x *)
                          option_zero_pad : bool ;    (* '0'   : padd with 0's instead of space x *)
                          option_width : option nat ; (* (\d+) : width of field                 x *)
                        }.



(* default options *)
Definition default_options : options := {| option_justify :=  RightJustify ;
                                           option_sign := false;
                                           option_space := false;
                                           option_prefix := false;
                                           option_zero_pad := false;
                                           option_width := None;
                                        |}.
Definition update_option_justify o v :=
  {| option_justify := v ;
     option_sign := option_sign o ;
     option_space := option_space o ;
     option_prefix := option_prefix o ;
     option_zero_pad := option_zero_pad o;
     option_width := option_width o;
  |}.

Definition update_option_sign o v :=
  {| option_justify := option_justify o ;
     option_sign := v ;
     option_space := option_space o ;
     option_prefix := option_prefix o ;
     option_zero_pad := option_zero_pad o;
     option_width := option_width o;
  |}.

Definition update_option_space o v :=
  {| option_justify := option_justify o ;
     option_sign := option_sign o ;
     option_space := v ;
     option_prefix := option_prefix o ;
     option_zero_pad := option_zero_pad o;
     option_width := option_width o;
  |}.

Definition update_option_prefix o v :=
  {| option_justify := option_justify o ;
     option_sign := option_sign o ;
     option_space := option_space o ;
     option_prefix := v ;
     option_zero_pad := option_zero_pad o;
     option_width := option_width o;
  |}.

Definition update_option_zero_pad o v :=
  {| option_justify := option_justify o ;
     option_sign := option_sign o ;
     option_space := option_space o ;
     option_prefix := option_prefix o ;
     option_zero_pad := v;
    option_width := option_width o;
  |}.

Definition update_option_width' o width' :=
  {| option_justify := option_justify o ;
     option_sign := option_sign o ;
     option_space := option_space o ;
     option_prefix := option_prefix o ;
     option_zero_pad := option_zero_pad o;
     option_width := width'
  |}.

Definition update_option_width o width :=
  update_option_width'
    o
    (match option_width o with
     | None => Some width
     | Some width' => Some ((10 * width') + width)
     end).


Theorem option_identity :
  forall o justify sign space prefix zero_pad width ,
         (update_option_width'
         (update_option_zero_pad
         (update_option_prefix
         (update_option_space
         (update_option_sign
         (update_option_justify o justify)
         sign)
         space)
         prefix)
         zero_pad)
         width) =
         {| option_justify := justify ;
            option_sign := sign ;
            option_space := space ;
            option_prefix := prefix ;
            option_zero_pad := zero_pad ;
            option_width := width
         |}.
intros.
unfold update_option_width'.
reflexivity.
Qed.

(* justify *)
Definition justify_string (s : string) (o : options) : string :=
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
Definition sign_string (s : string) (o : options) : string :=
  match(option_sign o,option_space o) with
  | (true,_) => String "+" s
  | (_,true) => String " " s
  | (_,_) => s
  end.

(* prefix *)
Definition prefix_string (prefix : string) (n : nat) (s : string) (o : options) : string :=
  match n with
  | 0 => s
  | S _ =>
  if option_prefix o then
    append prefix s
  else
    s
  end.



Fixpoint binary_ascii (n : nat) : ascii :=
  match n with
  | 0 =>  "0"%char
  | _ =>  "1"%char
  end.

Fixpoint octal_ascii (n : nat) : ascii :=
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

Fixpoint decimal_ascii (n : nat) : ascii :=
  match n with
  | 8 =>  "8"%char
  | 9 =>  "9"%char
  | _  => octal_ascii n
  end.

Fixpoint hex_ascii (n : nat) : ascii :=
  match n with
  | 10 => "a"%char
  | 11 => "b"%char
  | 12 => "c"%char
  | 13 => "d"%char
  | 14 => "e"%char
  | 15 => "f"%char
  | _  => decimal_ascii n
  end.

Fixpoint hex_ascii_upper (n : nat) : ascii :=
  match n with
  | 10 => "A"%char
  | 11 => "B"%char
  | 12 => "C"%char
  | 13 => "D"%char
  | 14 => "E"%char
  | 15 => "F"%char
  | _  => decimal_ascii n
  end.
Check hex_ascii.


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

Fixpoint holes (fmt : string) : Type :=
  match fmt with
  | EmptyString => string
  | String "%" fmt => hole fmt
  | String _ fmt => holes fmt
  end
with hole (fmt : string) : Type :=
  match fmt with
  | EmptyString => string
  | String "s" fmt => string -> holes fmt
  | String "b" fmt => nat -> holes fmt
  | String "o" fmt => nat -> holes fmt
  | String "d" fmt => nat -> holes fmt
  | String "x" fmt => nat -> holes fmt
  | String "X" fmt => nat -> holes fmt
  | String "c" fmt => ascii -> holes fmt
  | String "%" fmt => holes fmt
  | String "-" fmt => hole fmt
  | String "+" fmt => hole fmt
  | String " " fmt => hole fmt
  | String "#" fmt => hole fmt
  | String "0" fmt => hole fmt
  | String "1" fmt => width fmt
  | String "2" fmt => width fmt
  | String "3" fmt => width fmt
  | String "4" fmt => width fmt
  | String "5" fmt => width fmt
  | String "6" fmt => width fmt
  | String "7" fmt => width fmt
  | String "8" fmt => width fmt
  | String "9" fmt => width fmt
  | String  x  fmt => holes fmt
  end
with width (fmt : string) : Type :=
  match fmt with
  | EmptyString => string
  | String "s" fmt => string -> holes fmt
  | String "b" fmt => nat -> holes fmt
  | String "o" fmt => nat -> holes fmt
  | String "d" fmt => nat -> holes fmt
  | String "x" fmt => nat -> holes fmt
  | String "X" fmt => nat -> holes fmt
  | String "c" fmt => ascii -> holes fmt
  | String "%" fmt => holes fmt
  | String "0" fmt => width fmt
  | String "1" fmt => width fmt
  | String "2" fmt => width fmt
  | String "3" fmt => width fmt
  | String "4" fmt => width fmt
  | String "5" fmt => width fmt
  | String "6" fmt => width fmt
  | String "7" fmt => width fmt
  | String "8" fmt => width fmt
  | String "9" fmt => width fmt
  | String  x  fmt => holes fmt
  end.

(* helper methods to format *)
Definition format_s (s : string) (o : options) (x : string) : string :=
  let text := justify_string s o in
  (String.append text x).

Definition format_b (n : nat) (o : options) (x : string) : string :=
  let text := justify_string (binary_string n) o in
  (String.append text x).

Definition format_o (n : nat) (o : options) (x : string) : string :=
  let text := octal_string n in
  let text := prefix_string "0"%string n text o in
  let text := justify_string text o in
  (String.append text x).

Definition format_d (n : nat) (o : options) (x : string) : string :=
  let text := justify_string (sign_string (decimal_string n) o) o in
  (String.append text x).

Definition format_x (n : nat) (o : options) (x : string) : string :=
  let text := hex_string n in
  let text := prefix_string "0x"%string n text o in
  let text := justify_string text o in
  (String.append text x).

Definition format_X (n : nat) (o : options) (x : string) : string :=
  let text := hex_string_upper n in
  let text := prefix_string "0X"%string n text o in
  let text := justify_string text o in
  (String.append text x).


Local Fixpoint sprintf' (acc : string -> string) (fmt : string) {struct fmt} : holes fmt :=
  match fmt as fmt return holes fmt with
  | EmptyString => acc EmptyString
  | String "%" fmt =>
    print_val default_options acc fmt
  | String a fmt =>
    sprintf' (fun x => acc (String a x)) fmt
  end
      with print_val
           (o : options)
           (acc : string -> string)
           (fmt : string) {struct fmt} : hole fmt :=
    match fmt as fmt return hole fmt with
    | EmptyString => acc EmptyString
    | String "s" fmt => fun s => sprintf' (fun x => acc (format_s s o x)) fmt
    | String "b" fmt => fun n => sprintf' (fun x => acc (format_b n o x)) fmt
    | String "o" fmt => fun n => sprintf' (fun x => acc (format_o n o x)) fmt
    | String "d" fmt => fun n => sprintf' (fun x => acc (format_d n o x)) fmt
    | String "x" fmt => fun n => sprintf' (fun x => acc (format_x n o x)) fmt
    | String "X" fmt => fun n => sprintf' (fun x => acc (format_X n o x)) fmt
    | String "c" fmt => fun c => sprintf' (fun x => acc (String c x)) fmt
    | String "%" fmt =>          sprintf' (fun x => acc (String "%" x)) fmt
    | String "-" fmt => print_val (update_option_justify o LeftJustify) acc fmt
    | String "+" fmt => print_val (update_option_sign o true) acc fmt
    | String " " fmt => print_val (update_option_space o true) acc fmt
    | String "#" fmt => print_val (update_option_prefix o true) acc fmt
    | String "0" fmt => print_val (update_option_zero_pad o true) acc fmt
    | String "1" fmt => width_val (update_option_width o 1) acc fmt
    | String "2" fmt => width_val (update_option_width o 2) acc fmt
    | String "3" fmt => width_val (update_option_width o 3) acc fmt
    | String "4" fmt => width_val (update_option_width o 4) acc fmt
    | String "5" fmt => width_val (update_option_width o 5) acc fmt
    | String "6" fmt => width_val (update_option_width o 6) acc fmt
    | String "7" fmt => width_val (update_option_width o 7) acc fmt
    | String "8" fmt => width_val (update_option_width o 8) acc fmt
    | String "9" fmt => width_val (update_option_width o 9) acc fmt
    | String a   fmt =>          sprintf' (fun x => acc (String a x)) fmt
    end with width_val
             (o : options)
             (acc : string -> string)
             (fmt : string) {struct fmt} : width fmt :=
      match fmt as fmt return width fmt with
      | EmptyString => acc EmptyString
      | String "s" fmt => fun s => sprintf' (fun x => acc (format_s s o x)) fmt
      | String "b" fmt => fun n => sprintf' (fun x => acc (format_b n o x)) fmt
      | String "o" fmt => fun n => sprintf' (fun x => acc (format_o n o x)) fmt
      | String "d" fmt => fun n => sprintf' (fun x => acc (format_d n o x)) fmt
      | String "x" fmt => fun n => sprintf' (fun x => acc (format_x n o x)) fmt
      | String "X" fmt => fun n => sprintf' (fun x => acc (format_X n o x)) fmt
      | String "c" fmt => fun c => sprintf' (fun x => acc (String c x)) fmt
      | String "%" fmt =>          sprintf' (fun x => acc (String "%" x)) fmt
      | String "0" fmt => width_val (update_option_width o 0) acc fmt
      | String "1" fmt => width_val (update_option_width o 1) acc fmt
      | String "2" fmt => width_val (update_option_width o 2) acc fmt
      | String "3" fmt => width_val (update_option_width o 3) acc fmt
      | String "4" fmt => width_val (update_option_width o 4) acc fmt
      | String "5" fmt => width_val (update_option_width o 5) acc fmt
      | String "6" fmt => width_val (update_option_width o 6) acc fmt
      | String "7" fmt => width_val (update_option_width o 7) acc fmt
      | String "8" fmt => width_val (update_option_width o 8) acc fmt
      | String "9" fmt => width_val (update_option_width o 9) acc fmt
      | String a   fmt => sprintf' (fun x => acc (String a x)) fmt
      end.


Definition sprintf := sprintf' (fun x => x).
