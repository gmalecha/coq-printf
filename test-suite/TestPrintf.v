Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Printf.Printf.

Local Open Scope string_scope.

Example test_hex_1234: (hex_string 1234) = "4d2"%string.
Proof.
  unfold hex_string.
  reflexivity.
Qed.

Example test_4: (hex_string 4) = "4"%string.
Proof.
  unfold hex_string.
  reflexivity.
Qed.

Example test_1234_hex_upper: (hex_string_upper 1234) = "4D2"%string.
Proof.
  unfold hex_string.
  reflexivity.
Qed.

Example test_1234_octal: (octal_string 1234) = "2322"%string.
Proof.
  unfold hex_string.
  reflexivity.
Qed.

Goal sprintf "Hello, %s!" "world" = "Hello, world!".
Proof.
  reflexivity.
Qed.

Goal sprintf "%d, %d, %d, ..." 1 2 3 = "1, 2, 3, ...".
Proof.
  reflexivity.
Qed.

Goal sprintf "%d%%" 100 = "100%".
Proof.
  reflexivity.
Qed.

Goal sprintf "%c" "x"%char = "x".
Proof.
  reflexivity.
Qed.

Goal sprintf "%o" 1234 = "2322".
Proof.
  reflexivity.
Qed.

Goal sprintf "%x" 1234 = "4d2".
Proof.
  reflexivity.
Qed.

Goal sprintf "%X" 1234 = "4D2".
Proof.
  reflexivity.
Qed.

Goal sprintf "%b" 1234 = "10011010010".
Proof.
  reflexivity.
Qed.

Goal (sprintf "%o, %x, %X, %b, ..." 1234 1234 1234 1234) = "2322, 4d2, 4D2, 10011010010, ...".
Proof.
  reflexivity.
Qed.

Goal (sprintf "%4X" 1234) = " 4D2".
Proof.
  reflexivity.
Qed.

Goal (sprintf "%05X" 1234) = "004D2".
Proof.
  reflexivity.
Qed.

Goal sprintf "%-4X" 1234 = "4D2 "%string.
Proof.
  reflexivity.
Qed.

Goal sprintf "%-05X" 1234 = "4D200"%string.
Proof.
  reflexivity.
Qed.

Goal sprintf "% d" 1234 = " 1234"%string.
Proof.
  reflexivity.
Qed.

Goal sprintf "%+d" 1234 = "+1234"%string.
Proof.
  reflexivity.
Qed.


Goal sprintf "%-#05X" 1234 = "0X4D2"%string.
Proof.
  reflexivity.
Qed.

Goal sprintf "%-#05X" 0 = "00000"%string.
Proof.
  reflexivity.
Qed.

Goal sprintf "%-#05x" 1234 = "0x4d2"%string.
Proof.
  reflexivity.
Qed.
