(* This implementation was a helpful reference
   https://gist.github.com/rntz/aaaaf7a0bdb1cc65c49adb6adde29728
*)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

(* Drop returns the string left after removing the first n characters. *)
Fixpoint drop (n : nat) (s : string) :=
  match n with
  | 0 => s
  | S n => match s with
           | EmptyString => EmptyString
           | String _ s => drop n s
           end
  end.

Theorem drop_spec : forall l r , drop (length l) (l ++r ) = r.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  apply IHl.
Qed.

(* Take returns the first n characters of the string or the string itself *)
Fixpoint take (n : nat) (s : string):=
  match n with
  | 0 => EmptyString
  | S n => match s with
           | EmptyString => EmptyString
           | String c s => String c (take n s)
           end
  end.

Theorem take_spec : forall l r , take (length l) (l ++r ) = l.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite -> IHl.
  reflexivity.
Qed.

(* replicate returns a string of length n comprised of character a.  *)
Fixpoint replicate (a : ascii) (n : nat) :=
  match n with
  | 0 => EmptyString
  | S n' => String a (replicate a n')
  end.

(* string_uniform is a proposition testing if a string is comprised only of a given character *)
Fixpoint string_uniform (a : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String h t => (h = a) /\ string_uniform a t
  end.

Theorem replicate_uniform : forall a n , string_uniform a (replicate a n).
Proof.
  intros.
  induction n.
  simpl.
  auto.
  simpl.
  split.
  reflexivity.
  assumption.
Qed.


Theorem replicate_length : forall a n , length (replicate a n) = n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
Qed.


(* left justify *)

Definition left_justify_string
           (a : ascii )
           (n : nat)
           (s : string) : string := s ++ (replicate a (n - (length s))).

Theorem length_sn : forall s a , S(length s) = length (String a s).
Proof.
  reflexivity.
Qed.

Theorem left_justify_padding' : forall (a : ascii) (n : nat) (s : string) ,
    drop (length s) (left_justify_string a n s) = replicate a (n - (length s)).
Proof.
  intros.
  induction s.
  simpl.
  rewrite <- Minus.minus_n_O.
  unfold left_justify_string.
  simpl.
  rewrite <- Minus.minus_n_O.
  reflexivity.
  simpl.
  unfold left_justify_string.
  simpl.
  simpl.
  assert (Ha' := drop_spec s (replicate a (n - S (length s)))).
  apply Ha'.
Qed.

Theorem left_justify_padding : forall (a : ascii) (n : nat) (s : string) ,
    string_uniform a (drop (length s) (left_justify_string a n s)).
Proof.
  intros.
  rewrite -> left_justify_padding'.
  apply replicate_uniform.
Qed.

Theorem distribute_length : forall l r , length (l ++ r ) = length l + (length r).
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Theorem alternate_max : forall n m , max n m = n + (m - n).
Proof.
  intros n.
  induction n as [| n IHn] ; intros m.
  simpl. apply Minus.minus_n_O.
  destruct m.
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
  simpl.
  assert(forall n m, n = m -> S n = S m).
  intros.
  rewrite H.
  reflexivity.
  apply H.
  apply IHn.
Qed.

Theorem left_justify_length :
        forall (a : ascii) (n : nat) (s : string) ,
          length (left_justify_string a n s) = max (length s) n.
Proof.
  intros.
  rewrite -> alternate_max.
  intros.
  induction s.
  simpl.
  unfold left_justify_string.
  simpl.
  rewrite -> replicate_length.
  reflexivity.
  simpl.
  rewrite -> distribute_length.
  rewrite -> replicate_length.
  reflexivity.
Qed.

Theorem lemma_replicate : forall a n s ,
    take (S n) (String a s) = String a (take n s).
Proof.
  intros.
  reflexivity.
Qed.

Theorem string_associative : forall a s t ,
    append (String a s) t = String a (append s t).
Proof.
  reflexivity.
  Qed.

Theorem take_replicate : forall a n s ,
    take (length s) (s ++ (replicate a n)) = s.
Proof.
  intros.
  induction s.
  reflexivity.
  rewrite <- length_sn.
  rewrite -> string_associative.
  rewrite -> lemma_replicate .
  rewrite -> IHs.
  reflexivity.
Qed.

Theorem left_padding :
  forall (n : nat) (a : ascii) (s : string) ,
    take (length s) (left_justify_string a n s) = s.
Proof.
 intros.
 induction s.
 reflexivity.
 simpl.
 rewrite -> take_replicate.
 reflexivity.
Qed.

(* right justify *)
Definition right_justify_string
           (a : ascii )
           (n : nat)
           (s : string) : string := (replicate a (n - (length s))) ++ s.

Theorem drop_replicate : forall a n s , drop n ((replicate a n)  ++ s) = s.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  apply IHn.
Qed.

Theorem right_justify_padding' : forall (a : ascii) (n : nat) (s : string) ,
    take (n - (length s)) (right_justify_string a n s) = replicate a (n - (length s)).
Proof.
  intros.
  assert (Ha' := take_spec (replicate a (n - (length s))) s).
  rewrite  replicate_length in Ha'.
  unfold right_justify_string.
  rewrite -> Ha'.
  reflexivity.
Qed.

Theorem right_justify_padding : forall (a : ascii) (n : nat) (s : string) ,
    string_uniform a (take (n - (length s)) (right_justify_string a n s)).
Proof.
  intros.
  rewrite -> right_justify_padding'.
  apply replicate_uniform.
Qed.

Theorem right_padding :
  forall (n : nat) (a : ascii) (s : string) ,
    drop (n - (length s)) (right_justify_string a n s) = s.
Proof.
 intros.
 induction s.
 simpl.
 rewrite -> Nat.sub_0_r.
 induction n.
 simpl.
 unfold right_justify_string.
 reflexivity.
 apply drop_replicate.
 unfold right_justify_string.
 apply drop_replicate.
Qed.

Theorem right_justify_length :
        forall (a : ascii) (n : nat) (s : string) ,
          length (right_justify_string a n s) = max (length s) n.
Proof.
  intros.
  rewrite -> alternate_max.
  destruct s.
  simpl.
  unfold right_justify_string.
  simpl.
  rewrite -> distribute_length.
  rewrite -> replicate_length.
  simpl.
  rewrite -> Nat.sub_0_r.
  rewrite -> plus_n_O.
  reflexivity.
  unfold right_justify_string.
  simpl.
  rewrite -> distribute_length.
  rewrite -> replicate_length.
  simpl.
  rewrite -> Nat.add_comm.
  rewrite -> plus_Sn_m.
  reflexivity.
Qed.
