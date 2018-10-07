Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Printf.Printf.

Local Open Scope string_scope.

Goal printf "Hello, %s!" "world" = "Hello, world!".
Proof. reflexivity. Qed.

Goal printf "%d, %d, %d, ..." 1 2 3 = "1, 2, 3, ...".
Proof. reflexivity. Qed.

Goal printf "%d%%" 100 = "100%".
Proof. reflexivity. Qed.

Goal printf "%c" "x"%char = "x".
Proof. reflexivity. Qed.