(** * Parse [string] to [Format.t] and print [Format.t] to [list Byte.byte] *)

Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Require Import Printf.Flags.
Require Import Printf.Format.
Require Import Printf.Digits.

Local Infix "::" := String.String : string_scope.

Import Format.

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

Definition parse_opt (s : list Byte.byte) : option t :=
  match parse (string_of_list_byte s) with
  | inl _ => None
  | inr fmt => Some fmt
  end.

Local Open Scope list_scope.

Definition print_options (opts : options) (etc : list Byte.byte) : list Byte.byte :=
  let etc :=
    match option_width opts with
    | None => etc
    | Some n => (list_byte_of_string (decimal_string (N.of_nat n)) ++ etc)%list
    end in
  let etc := if option_zero_pad opts then byte_of_ascii "0" :: etc else etc in
  let etc := if option_prefix opts then byte_of_ascii "#" :: etc else etc in
  let etc := if option_space opts then byte_of_ascii " " :: etc else etc in
  let etc := if option_sign opts then byte_of_ascii "+" :: etc else etc in
  match option_justify opts with
  | LeftJustify => byte_of_ascii "-" :: etc
  | RightJustify => etc
  end.

Definition print_type (ty : type) (etc : list Byte.byte) : list Byte.byte :=
  match ty with
  | Number enc dec =>
    let enc_letter := byte_of_ascii
      match enc with
      | Binary => "b"
      | Octal => "o"
      | Decimal => "d"
      | HexLower => "x"
      | HexUpper => "X"
      end in
    match dec with
    | T_Nat => enc_letter :: etc
    | T_N => byte_of_ascii "N" :: enc_letter :: etc
    end
  | SDecimal => byte_of_ascii "Z" :: byte_of_ascii "d" :: etc
  | String => byte_of_ascii "s" :: etc
  | Char => byte_of_ascii "c" :: etc
  end.

Fixpoint print (fmt : t) : list Byte.byte :=
  let pc := byte_of_ascii "%" in
  match fmt with
  | Empty => nil
  | Literal c fmt =>
    if (c =? "%")%char then pc :: pc :: print fmt
    else byte_of_ascii c :: print fmt
  | Hole ty opts fmt =>
    pc :: print_options opts (print_type ty (print fmt))
  end.

Section Test.

Let roundtrip (s : string) : Prop :=
  match parse s with
  | inl _ => False
  | inr fmt => string_of_list_byte (print fmt) = s
  end.

Let roundtrip_test : roundtrip " %% %11d %+Nd %-Zd %x %NX %033s % #c".
Proof. reflexivity. Qed.

End Test.
