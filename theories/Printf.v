Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import ExtLib.Programming.Show.

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
  | String "d" fmt => nat -> holes fmt
  | String "c" fmt => ascii -> holes fmt
  | String "%" fmt => holes fmt
  | String x fmt => holes fmt
  end.


Local Fixpoint printf' (acc : string -> string) (fmt : string) {struct fmt}
: holes fmt :=
  match fmt as fmt return holes fmt with
  | EmptyString => acc EmptyString
  | String "%" fmt =>
    print_val acc fmt
  | String a fmt =>
    printf' (fun x => acc (String a x)) fmt
  end
with print_val (acc : string -> string) (fmt : string) {struct fmt}
: hole fmt :=
  match fmt as fmt return hole fmt with
  | EmptyString => acc EmptyString
  | String "s" fmt => fun s =>
    printf' (fun x => acc (String.append s x)) fmt
  | String "d" fmt => fun n =>
    printf' (fun x => acc (String.append (to_string n) x)) fmt
  | String "c" fmt => fun c =>
    printf' (fun x => acc (String c x)) fmt
  | String "%" fmt =>
    printf' (fun x => acc (String "%" x)) fmt
  | String a fmt =>
    printf' (fun x => acc (String a x)) fmt
  end.

Definition printf := printf' (fun x => x).

Local Open Scope string_scope.

Compute printf "%d %s %c" 5 "hello" "b"%char.
