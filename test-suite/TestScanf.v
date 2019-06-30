Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Printf.Scanf.

Local Open Scope string_scope.

Definition ret {A B : Type} (a : A) (_ : B) : option A := Some a.

Goal sscanf "Hello, %s" ret "Hello, world!" = Some "world!".
Proof.
  reflexivity.
Qed.

Goal sscanf "%d, %d, %d, ..." (fun a b c _ => Some (a, b, c)) "1, 2, 3, ..."
  = Some (1, 2, 3).
Proof.
  reflexivity.
Qed.

Goal sscanf "%d%%" ret "100%" = Some 100.
Proof.
  reflexivity.
Qed.

Goal sscanf "%c" ret "x" = Some "x"%char.
Proof.
  reflexivity.
Qed.

Goal sscanf "%o" ret "2322" = Some 1234.
Proof.
  reflexivity.
Qed.

Goal sscanf "%x" ret "4d2" = Some 1234.
Proof.
  reflexivity.
Qed.

Goal sscanf "%X" ret "4D2" = Some 1234.
Proof.
  reflexivity.
Qed.

Goal sscanf "%b" ret "10011010010" = Some 1234.
Proof.
  reflexivity.
Qed.

Goal sscanf "%Nd" ret "1234" = Some 1234%N.
Proof.
  reflexivity.
Qed.

Goal sscanf "%NX" ret "4D2" = Some 1234%N.
Proof.
  reflexivity.
Qed.

Goal sscanf "%Nx" ret "4d2" = Some 1234%N.
Proof.
  reflexivity.
Qed.

Goal sscanf "%Zd" ret "1234" = Some 1234%Z.
Proof.
  reflexivity.
Qed.

Goal sscanf "%Zd" ret "-1234" = Some (-1234)%Z.
Proof.
  reflexivity.
Qed.

Goal sscanf "%Zd" ret "+1234" = Some 1234%Z.
Proof.
  reflexivity.
Qed.

Goal sscanf "%o, %x, %X, %b, ..."
            (fun a b c d _ => Some (a, b, c, d))
            "2322, 4d2, 4D2, 10011010010, ..."
  = Some (1234, 1234, 1234, 1234).
Proof.
  reflexivity.
Qed.

Goal sscanf " %3X" (fun n s => Some (n, s)) " 4D2ABC" = Some (1234, "ABC").
Proof.
  reflexivity.
Qed.

Goal sscanf "%5X" (fun n s => Some (n, s)) "004D21" = Some (1234, "1").
Proof.
  reflexivity.
Qed.

Goal sscanf "%d" ret "+1234" = Some 1234.
Proof.
  reflexivity.
Qed.

Goal sscanf "%X" ret "0X4D2" = Some 1234.
Proof.
  reflexivity.
Qed.

Goal sscanf "%x" ret "0x4d2" = Some 1234.
Proof.
  reflexivity.
Qed.

Goal sscanf "%Zd" ret "-32" = Some (-32)%Z.
Proof.
  reflexivity.
Qed.
