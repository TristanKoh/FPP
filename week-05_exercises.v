(* week-05_exercises.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)

(* ********** *)

(* 
Your name:
Bernard Boey
Tristan Koh

Your e-mail address:
bernard@u.yale-nus.edu.sg
tristan.koh@u.yale-nus.edu.sg

Your student number:
A0191234L
A0191222R

*)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Fixpoint nat_fold_right (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    s (nat_fold_right V z s n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_right V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_right V z s (S n') =
    s (nat_fold_right V z s n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

(* ***** *)

Fixpoint nat_fold_left (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    nat_fold_left V (s z) s n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_left V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_left V z s (S n') =
    nat_fold_left V (s z) s n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* ********** *)

Lemma about_nat_fold_left :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_left V (s z) s n = s (nat_fold_left V z s n).
Proof.
  intros V z s n.
  revert z.
  induction n as [ | n' IHn'].
  - intro z.
    rewrite -> (fold_unfold_nat_fold_left_O V z s).
    exact (fold_unfold_nat_fold_left_O V (s z) s).
  - intro z.
    rewrite -> (fold_unfold_nat_fold_left_S V z s n').
    rewrite -> (fold_unfold_nat_fold_left_S V (s z) s n').
    Check (IHn' (s z)).
    exact (IHn' (s z)).
Qed.  

Lemma about_nat_fold_right :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_right V (s z) s n = s (nat_fold_right V z s n).
Proof.
  intros V z s n.
  induction n as [ | n' IHn'].
  - rewrite -> (fold_unfold_nat_fold_right_O V z s).
    exact (fold_unfold_nat_fold_right_O V (s z) s).
  - rewrite -> (fold_unfold_nat_fold_right_S V z s n').
    rewrite -> (fold_unfold_nat_fold_right_S V (s z) s n').
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem folding_left_and_right :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_left V z s n = nat_fold_right V z s n.
Proof.
  intros V z s n.
  revert z.
  induction n as [ | n' IHn'].
  - intro z.
    rewrite -> (fold_unfold_nat_fold_left_O V z s).
    rewrite -> (fold_unfold_nat_fold_right_O V z s).
    reflexivity.
  - intro z.
    rewrite -> (fold_unfold_nat_fold_left_S V z s n').
    rewrite -> (fold_unfold_nat_fold_right_S V z s n').
    rewrite -> (about_nat_fold_left V z s n').
    rewrite -> (IHn' z).
    reflexivity.

  Restart.

  intros V z s n.
  revert z.
  induction n as [ | n' IHn'].
  - intro z.
    rewrite -> (fold_unfold_nat_fold_left_O V z s).
    rewrite -> (fold_unfold_nat_fold_right_O V z s).
    reflexivity.
  - intro z.
    rewrite -> (fold_unfold_nat_fold_left_S V z s n').
    rewrite -> (fold_unfold_nat_fold_right_S V z s n').
    rewrite <- (about_nat_fold_right V z s n').
    Check (IHn' (s z)).
    exact (IHn' (s z)).
Qed.    


(* ********** *)

Fixpoint mul_v0_aux (i j : nat) : nat :=
  match i with
    | O => 0
    | S i' => j + (mul_v0_aux i' j)
  end.

Lemma fold_unfold_mul_v0_aux_O :
  forall j : nat,
    mul_v0_aux O j = 0.
Proof.
  fold_unfold_tactic mul_v0_aux.
Qed.

Lemma fold_unfold_mul_v0_aux_S :
  forall i' j : nat,
    mul_v0_aux (S i') j = j + (mul_v0_aux i' j).
Proof.
  fold_unfold_tactic mul_v0_aux.
Qed.

Definition mul_v0 (i j : nat) : nat :=
  mul_v0_aux i j.

Definition mul_v0_alt (i j : nat) : nat :=
  nat_fold_right nat 0 (fun ih => j + ih) i.

Definition specification_of_mul (mul : nat -> nat -> nat) :=
  (forall j : nat,
      mul O j = 0)
  /\
  (forall i' j : nat,
      mul (S i') j = j + (mul i' j)).


Proposition there_is_at_most_one_function_satisfying_the_specification_of_mul :
  forall mul1 mul2 : nat -> nat -> nat,
    specification_of_mul mul1 ->
    specification_of_mul mul2 ->
    forall i j : nat,
      mul1 i j = mul2 i j.
Proof.
  unfold specification_of_mul.
  intros mul1 mul2 [S1_O S1_S] [S2_O S2_S] i j.
  induction i as [ | i' IHi'].
  - rewrite -> (S2_O j).
    exact (S1_O j).
  - rewrite -> (S1_S i' j).
    rewrite -> (S2_S i' j).
    rewrite -> IHi'.
    reflexivity.
Qed.

Proposition mul_v0_safisfies_the_specification_of_mul :
  specification_of_mul mul_v0.
Proof.
  unfold specification_of_mul, mul_v0.
  split.
  - intro j.
    exact (fold_unfold_mul_v0_aux_O j).
  - intros i' j.
    exact (fold_unfold_mul_v0_aux_S i' j).
Qed.


Proposition mul_v0_alt_safisfies_the_specification_of_mul :
  specification_of_mul mul_v0_alt.
Proof.
  unfold specification_of_mul, mul_v0_alt.
  split.
  - intro j.
    exact (fold_unfold_nat_fold_right_O nat 0 (fun ih => j + ih)).
  - intros i' j.
    exact (fold_unfold_nat_fold_right_S nat 0 (fun ih => j + ih) i').
Qed.


Proposition mul_v0_and_mul_v0_alt_are_equivalent :
  forall i j : nat,
    mul_v0 i j = mul_v0_alt i j.
Proof.
  intros i j.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_mul
           mul_v0
           mul_v0_alt
           mul_v0_safisfies_the_specification_of_mul
           mul_v0_alt_safisfies_the_specification_of_mul
           i
           j).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_mul
           mul_v0
           mul_v0_alt
           mul_v0_safisfies_the_specification_of_mul
           mul_v0_alt_safisfies_the_specification_of_mul
           i
           j).
Qed.
  
(* ***** *)

Fixpoint mul_v1_aux (i j a : nat) : nat :=
  match i with
    | O => a
    | S i' => mul_v1_aux i' j (j + a)
  end.

Lemma fold_unfold_mul_v1_aux_O :
  forall j a : nat,
    mul_v1_aux O j a = a.
Proof.
  fold_unfold_tactic mul_v1_aux.
Qed.

Lemma fold_unfold_mul_v1_aux_S :
  forall i' j a : nat,
    mul_v1_aux (S i') j a =  mul_v1_aux i' j (j + a).
Proof.
  fold_unfold_tactic mul_v1_aux.
Qed.

Definition mul_v1 (i j : nat) : nat :=
  mul_v1_aux i j 0.

Lemma about_mul_v1_aux :
  forall i j a : nat,
    mul_v1_aux i j a = a + mul_v1_aux i j 0.
Proof.
  intro i.
  induction i as [ | i' IHi'].
  - intros j a.
    rewrite -> (fold_unfold_mul_v1_aux_O j a).
    rewrite -> (fold_unfold_mul_v1_aux_O j 0).
    rewrite -> (Nat.add_0_r a).
    reflexivity.
  - intros j a.
    rewrite -> (fold_unfold_mul_v1_aux_S i' j a).
    rewrite -> (fold_unfold_mul_v1_aux_S i' j 0).
    rewrite -> (Nat.add_0_r j).
    rewrite -> (IHi' j (j + a)).
    rewrite -> (IHi' j j).
    Search (_ + (_ + _)).
    rewrite -> (Nat.add_shuffle3 a j (mul_v1_aux i' j 0)).
    rewrite -> (Nat.add_assoc j a (mul_v1_aux i' j 0)).
    reflexivity.
Qed.

Proposition mul_v1_safisfies_the_specification_of_mul :
  specification_of_mul mul_v1.
Proof.
  unfold specification_of_mul, mul_v1.
  split.
  - intro j.
    exact (fold_unfold_mul_v1_aux_O j 0).
  - intros i' j.
    rewrite -> (fold_unfold_mul_v1_aux_S i' j).
    rewrite -> (Nat.add_0_r j).
    exact (about_mul_v1_aux i' j j).
Qed.

Proposition mul_v0_and_mul_v1_are_equivalent :
  forall i j : nat,
    mul_v0 i j = mul_v1 i j.
Proof.
  intros i j.
  unfold mul_v0, mul_v1.
  induction i as [ | i' IHi'].
  - rewrite -> (fold_unfold_mul_v1_aux_O j 0).
    exact (fold_unfold_mul_v0_aux_O j).
  - rewrite -> (fold_unfold_mul_v0_aux_S i' j).
    rewrite -> (fold_unfold_mul_v1_aux_S i' j 0).
    rewrite -> IHi'.
    rewrite -> (Nat.add_0_r j).
    rewrite -> (about_mul_v1_aux i' j j).
    reflexivity.
Qed.

Definition mul_v1_alt (i j : nat) : nat :=
  nat_fold_left nat 0 (fun ih => j + ih) i.

Proposition mul_v1_alt_safisfies_the_specification_of_mul :
  specification_of_mul mul_v1_alt.
Proof.
  unfold specification_of_mul, mul_v1_alt.
  split.
  - intro j.
    exact (fold_unfold_nat_fold_left_O nat 0 (fun ih => j + ih)).
  - intros i' j.
    rewrite -> (fold_unfold_nat_fold_left_S nat 0 (fun ih => j + ih) i').
    Check (about_nat_fold_left nat 0 (fun ih : nat => j + ih) i').
    rewrite -> (about_nat_fold_left nat 0 (fun ih : nat => j + ih) i').
    reflexivity.
Qed.

Proposition mul_v1_and_mul_v1_alt_are_equivalent :
  forall i j : nat,
    mul_v1 i j = mul_v1_alt i j.
Proof.
  intros i j.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_mul
           mul_v1
           mul_v1_alt
           mul_v1_safisfies_the_specification_of_mul
           mul_v1_alt_safisfies_the_specification_of_mul
           i
           j).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_mul
           mul_v1
           mul_v1_alt
           mul_v1_safisfies_the_specification_of_mul
           mul_v1_alt_safisfies_the_specification_of_mul
           i
           j).
Qed.

Corollary mul_v0_and_mul_v1_are_equivalent_alt :
  forall i j : nat,
    mul_v0 i j = mul_v1 i j.
Proof.
  intros i j.
  rewrite -> (mul_v0_and_mul_v0_alt_are_equivalent).
  rewrite -> (mul_v1_and_mul_v1_alt_are_equivalent).
  unfold mul_v0_alt, mul_v1_alt.
  rewrite -> (folding_left_and_right nat 0 (fun ih : nat => j + ih) i).
  reflexivity.
Qed.


  
(* ********** *)

(* end of week-05_exercises.v *)
