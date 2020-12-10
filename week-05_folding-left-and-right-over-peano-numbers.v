(* week-05_folding-left-and-right-over-peano-numbers.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2020 *)

(* ********** *)

(* Your name:
   Your student ID number:
   Your e-mail address: 

   Your name:
   Your student ID number:
   Your e-mail address: 

   Your name:
   Your student ID number:
   Your e-mail address: 

   Your name:
   Your student ID number:
   Your e-mail address: 
*)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Definition specification_of_power (power : nat -> nat -> nat) :=
  (forall x : nat,
      power x 0 = 1)
  /\
  (forall (x : nat)
          (n' : nat),
      power x (S n') = x * power x n').

(* ***** *)

Proposition there_is_at_most_one_function_satisfying_the_specification_of_power :
  forall power1 power2 : nat -> nat -> nat,
    specification_of_power power1 ->
    specification_of_power power2 ->
    forall x n : nat,
      power1 x n = power2 x n.
Proof.
  intros power1 power2.
  unfold specification_of_power.
  intros [S1_O S1_S] [S2_O S2_S] x n.
  induction n as [ | n' IHn'].
  - rewrite -> (S2_O x).
    exact (S1_O x).
  - rewrite -> (S1_S x n').
    rewrite -> (S2_S x n').
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ***** *)

Definition test_power (candidate : nat -> nat -> nat) : bool :=
  (candidate 2 0 =? 1) &&
  (candidate 10 2 =? 10 * 10) &&
  (candidate 3 2 =? 3 * 3).

(* ***** *)

Fixpoint power_v0_aux (x n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    x * power_v0_aux x n'
  end.

Definition power_v0 (x n : nat) : nat :=
  power_v0_aux x n.

Compute (test_power power_v0).

Lemma fold_unfold_power_v0_aux_O :
  forall x : nat,
    power_v0_aux x 0 = 1.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Lemma fold_unfold_power_v0_aux_S :
  forall x n' : nat,
    power_v0_aux x (S n') = x * power_v0_aux x n'.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Proposition power_v0_safisfies_the_specification_of_power :
  specification_of_power power_v0.
Proof.
  unfold specification_of_power, power_v0.
  split.
  - exact fold_unfold_power_v0_aux_O.
  - exact fold_unfold_power_v0_aux_S.
Qed.

(* ***** *)

Fixpoint power_v1_aux (x n a : nat) : nat :=
  match n with
  | O =>
    a
  | S n' =>
    power_v1_aux x n' (x * a)
  end.

Definition power_v1 (x n : nat) : nat :=
  power_v1_aux x n 1.

Compute (test_power power_v1).

Lemma fold_unfold_power_v1_aux_O :
  forall x a : nat,
    power_v1_aux x 0 a =
    a.
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

Lemma fold_unfold_power_v1_aux_S :
  forall x n' a : nat,
    power_v1_aux x (S n') a =
    power_v1_aux x n' (x * a).
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

(* ***** *)

(* Eureka lemma: *)

Lemma about_power_v0_aux_and_power_v1_aux :
  forall x n a : nat,
    power_v0_aux x n * a = power_v1_aux x n a.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_O x).
    rewrite -> (fold_unfold_power_v1_aux_O x a).
    exact (Nat.mul_1_l a).
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_S x n').
    rewrite -> (fold_unfold_power_v1_aux_S x n' a).
    Check (IHn' (x * a)).
    rewrite <- (IHn' (x * a)).
    rewrite -> (Nat.mul_comm x (power_v0_aux x n')).
    Check (Nat.mul_assoc).
    symmetry.
    exact (Nat.mul_assoc (power_v0_aux x n') x a).
Qed.

Theorem power_v0_and_power_v1_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  unfold power_v0, power_v1.
  Check (about_power_v0_aux_and_power_v1_aux x n 1).
  rewrite <- (Nat.mul_1_r (power_v0_aux x n)).
  exact (about_power_v0_aux_and_power_v1_aux x n 1).
Qed.

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

Definition power_v0_alt (x n : nat) : nat :=
  nat_fold_right nat 1 (fun ih => x * ih) n.

Compute (test_power power_v0_alt).

Proposition power_v0_alt_safisfies_the_specification_of_power :
  specification_of_power power_v0_alt.
Proof.
  unfold specification_of_power, power_v0_alt.
  split.
  - intro x.
    rewrite -> (fold_unfold_nat_fold_right_O nat 1 (fun ih : nat => x * ih)).
    reflexivity.
  - intros x n'.
    rewrite -> (fold_unfold_nat_fold_right_S nat 1 (fun ih : nat => x * ih) n').
    reflexivity.
Qed.

Corollary power_v0_and_power_v0_alt_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v0_alt x n.
Proof.
  intros x n.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_safisfies_the_specification_of_power
           power_v0_alt_safisfies_the_specification_of_power
           x
           n).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_safisfies_the_specification_of_power
           power_v0_alt_safisfies_the_specification_of_power
           x
           n).
Qed.

(* ***** *)

Definition power_v1_alt (x n : nat) : nat :=
  nat_fold_left nat 1 (fun ih => x * ih) n.

Compute (test_power power_v1_alt).

Lemma power_v1_and_power_v1_alt_are_equivalent_aux :
  forall x n a : nat,
    power_v1_aux x n a = nat_fold_left nat a (fun ih : nat => x * ih) n.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_power_v1_aux_O x a).
    rewrite -> (fold_unfold_nat_fold_left_O nat a (fun ih : nat => x * ih)).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_power_v1_aux_S x n' a).
    rewrite -> (fold_unfold_nat_fold_left_S nat a (fun ih : nat => x * ih)).
    Check (IHn' (x * a)).
    exact (IHn' (x * a)).
Qed.    

Proposition power_v1_and_power_v1_alt_are_equivalent :
  forall x n : nat,
    power_v1 x n = power_v1_alt x n.
Proof.
  intros x n.
  unfold power_v1, power_v1_alt.
  exact (power_v1_and_power_v1_alt_are_equivalent_aux x n 1).
Qed.

(* ********** *)

Lemma about_nat_fold_left :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_left V (s z) s n = s (nat_fold_left V z s n).
Proof.
Admitted.

Lemma about_nat_fold_right :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_right V (s z) s n = s (nat_fold_right V z s n).
Proof.
Admitted.

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

(*
    rewrite -> (about_nat_fold_left V z s n').
    rewrite -> (IHn' z).
    reflexivity.
 *)
    rewrite <- (about_nat_fold_right V z s n').
    Check (IHn' (s z)).
    exact (IHn' (s z)).
Qed.    
    
(* ********** *)

Corollary power_v0_and_power_v1_are_equivalent_alt :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  rewrite -> (power_v0_and_power_v0_alt_are_equivalent x n).
  rewrite -> (power_v1_and_power_v1_alt_are_equivalent x n).
  unfold power_v0_alt, power_v1_alt.
  symmetry.
  exact (folding_left_and_right nat 1 (fun ih : nat => x * ih) n).
Qed.

(* ********** *)

Fixpoint add_v0 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => S (add_v0 i' j)
  end.

(*
Definition add_v0_alt (i j : nat) : nat :=
  ...nat_fold_right...
*)

(*
Proposition add_v0_and_add_v0_alt_are_equivalent :
  forall i j : nat,
    add_v0 i j = add_v0_alt i j.
*)

(* ***** *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v1 i' (S j)
  end.

(*
Definition add_v1_alt (i j : nat) : nat :=
  ...nat_fold_left...
*)

(*
Proposition add_v1_and_add_v1_alt_are_equivalent :
  forall i j : nat,
    add_v1 i j = add_v1_alt i j.
*)

(* ********** *)

Fixpoint mul_v0_aux (i j : nat) : nat :=
  match i with
    | O => 0
    | S i' => j + (mul_v0_aux i' j)
  end.

Definition mul_v0 (i j : nat) : nat :=
  mul_v0_aux i j.

Lemma fold_unfold_mul_v0_O :
  forall j : nat,
    mul_v0_aux O j = 0.
Proof.
  fold_unfold_tactic mul_v0_aux.
Qed.

Lemma fold_unfold_mul_v0_S :
  forall i' j : nat,
    mul_v0_aux (S i') j = j + (mul_v0_aux i' j).
Proof.
  fold_unfold_tactic mul_v0_aux.
Qed.

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

Proposition mul_v0_safisfies_the_specification_of_power :
  specification_of_mul mul_v0.
Proof.
  unfold specification_of_mul, mul_v0.
  split.
  - intro j.
    rewrite -> (fold_unfold_mul_v0_O j).
    reflexivity.
  - intros i' j.
    rewrite -> (fold_unfold_mul_v0_S i' j).
    reflexivity.
Qed.


Proposition mul_v0_alt_safisfies_the_specification_of_power :
  specification_of_mul mul_v0_alt.
Proof.
  unfold specification_of_mul, mul_v0_alt.
  split.
  - intro j.
    rewrite -> (fold_unfold_nat_fold_right_O nat 0 (fun ih => j + ih)).
    reflexivity.
  - intros i' j.
    rewrite -> (fold_unfold_nat_fold_right_S nat 0 (fun ih => j + ih) i').
    reflexivity.
Qed.


Proposition mul_v0_and_mul_v0_alt_are_equivalent :
  forall i j : nat,
    mul_v0 i j = mul_v0_alt i j.
Proof.
  intros i j.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_mul
           mul_v0
           mul_v0_alt
           mul_v0_safisfies_the_specification_of_power
           mul_v0_alt_safisfies_the_specification_of_power
           i
           j).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_mul
           mul_v0
           mul_v0_alt
           mul_v0_safisfies_the_specification_of_power
           mul_v0_alt_safisfies_the_specification_of_power
           i
           j).
Qed.
  
  

(* ***** *)

Fixpoint mul_v1_aux (i j a : nat) : nat :=
  match i with
    | O => a
    | S i' => mul_v1_aux i' j (j + a)
  end.

Definition mul_v1 (i j : nat) : nat :=
  mul_v1_aux i j 0.

(*
Definition mul_v1_alt (i j : nat) : nat :=
  ...nat_fold_left...
*)

(*
Proposition mul_v1_and_mul_v1_alt_are_equivalent :
  forall i j : nat,
    mul_v1 i j = mul_v1_alt i j.
*)

(* ********** *)

(* end of week-05_folding-left-and-right-over-peano-numbers.v *)
