Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Printf.Printf.

Local Open Scope string_scope.

Goal sprintf "Hello, %s!" "world" = "Hello, world!".
Proof. reflexivity. Qed.

Goal sprintf "%d, %d, %d, ..." 1 2 3 = "1, 2, 3, ...".
Proof. reflexivity. Qed.

Goal sprintf "%d%%" 100 = "100%".
Proof. reflexivity. Qed.

Goal sprintf "%c" "x"%char = "x".
Proof. reflexivity. Qed.