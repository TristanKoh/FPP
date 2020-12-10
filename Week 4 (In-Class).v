Search (_ + _ = _ + _).

Proposition foo :
  forall P Q R1 R2 : Prop,
    P -> (P -> Q) -> (Q -> R1) /\ (Q -> R2) -> R1 /\ R2.
Proof.
  intros P Q R1 R2 H_P H_P_implies_Q [H_Q_implies_R1 H_Q_implies_R2].
  split.
  - apply H_Q_implies_R1.
    apply H_P_implies_Q.
    apply H_P.
  - apply H_Q_implies_R2.
    apply H_P_implies_Q.
    apply H_P.
    
  Restart.

  intros P Q R1 R2 H_P H_P_implies_Q [H_Q_implies_R1 H_Q_implies_R2].
  Check (H_P_implies_Q H_P).
  Check (H_Q_implies_R1 (H_P_implies_Q H_P)).
  Check (H_Q_implies_R2 (H_P_implies_Q H_P)).
  Check (conj (H_Q_implies_R1 (H_P_implies_Q H_P)) (H_Q_implies_R2 (H_P_implies_Q H_P))).
  exact (conj (H_Q_implies_R1 (H_P_implies_Q H_P)) (H_Q_implies_R2 (H_P_implies_Q H_P))).

  Restart.

  intros P Q R1 R2 H_P H_P_implies_Q [H_Q_implies_R1 H_Q_implies_R2].
  apply H_P_implies_Q in H_P.
  Check (H_Q_implies_R1 H_P).
  Check (H_Q_implies_R2 H_P).
  Check (conj (H_Q_implies_R1 H_P) (H_Q_implies_R2 H_P)).
  exact (conj (H_Q_implies_R1 H_P) (H_Q_implies_R2 H_P)).
  Show Proof.

  Restart.

  intros P Q R1 R2 H_P H_P_implies_Q [H_Q_implies_R1 H_Q_implies_R2].
  assert (H_Q := H_P_implies_Q H_P).
  Show Proof.
  Check (H_Q_implies_R1 H_Q).
  Check (H_Q_implies_R2 H_Q).
  Check (conj (H_Q_implies_R1 H_Q) (H_Q_implies_R2 H_Q)).
  exact (conj (H_Q_implies_R1 H_Q) (H_Q_implies_R2 H_Q)).
Qed.

Ltac fold_unfold_tactic name :=
  intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Definition test_power (candidate : nat -> nat -> nat) : bool :=
  (candidate 2 0 =? 1) &&
  (candidate 10 2 =? 100) &&
  (candidate 3 2 =? 9).

Definition specification_of_power (power: nat -> nat -> nat) :=
  (forall x : nat,
      power x 0 = 1)
  /\
  (forall (x: nat)
          (n' : nat),
      power x (S n') = x * power x n').

Theorem soundness_of_test_power :
  forall power : nat -> nat -> nat,
    specification_of_power power ->
    test_power power = true.
Proof.
  intro power.
  unfold specification_of_power.
  intros [S_power_0 S_power_S].
  unfold test_power.
  Check (S_power_0 2).
  rewrite -> (S_power_0 2).
  Search (_ =? _).
  Check (Nat.eqb_refl 1).
  rewrite -> (Nat.eqb_refl 1).
  Search (true && _ = _).
  Check (true && (true && true), (true && true) && true).
  Check (andb_true_l (power 10 2 =? 100)).
  rewrite -> (andb_true_l (power 10 2 =? 100)).
  assert (helpful :
            forall x : nat,
              power x 2 = x * x).
  { intro x.
    Check (S_power_S x 1).
    rewrite -> (S_power_S x 1).
    Check (S_power_S x 0).
    rewrite -> (S_power_S x 0).
    rewrite -> (S_power_0 x).
    rewrite -> (Nat.mul_1_r x).
    reflexivity. }
  rewrite -> (helpful 10).
  rewrite -> (helpful 3).

Abort.



Proposition identity :
  forall A : Prop,
    A -> A.
Proof.
  intros A H_A.
  apply H_A.
Qed.

Proposition modus_ponens :
  forall A B : Prop,
    A -> (A -> B) -> B.
Proof.
  intros A B H_A H_A_implies_B.
  apply H_A_implies_B.
  apply H_A.
  Show Proof.
  (* (fun (A B : Prop) (H_A : A) (H_A_implies_B : A -> B) => H_A_implies_B H_A) *)
  Restart.

  intros A B H_A H_A_implies_B.
  Check (H_A_implies_B H_A).
  exact (H_A_implies_B H_A).
  Show Proof.
  (* (fun (A B : Prop) (H_A : A) (H_A_implies_B : A -> B) => H_A_implies_B H_A) *)
Qed.


Fixpoint power_v0 (x n : nat) : nat :=
  match n with
  | 0 =>
    1
  | S n' =>
    x * (power_v0 x n')
  end.

Lemma fold_unfold_power_v0_0 :
  forall x : nat,
    power_v0 x 0 =
    1.
Proof.
  fold_unfold_tactic power_v0.
Qed.
  
Lemma fold_unfold_power_v0_S :
  forall x n' : nat,
    power_v0 x (S n') =
    x * (power_v0 x n').
Proof.
  fold_unfold_tactic power_v0.
Qed.

Fixpoint power_v1_aux (x n a : nat) : nat :=
  match n with
  | 0 =>
    a
  | S n' =>
    power_v1_aux x n' (x * a)
  end.

Lemma fold_unfold_power_v1_aux_0 :
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

Definition power_v1 (x n : nat) : nat :=
  power_v1_aux x n 1.

Lemma about_power_v0_and_power_v1_aux :
  forall x n a : nat,
   power_v0 x n * a = power_v1_aux x n a.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_power_v0_0 x).
    rewrite -> (fold_unfold_power_v1_aux_0 x a).
    exact (Nat.mul_1_l a).
  - intro a.
    rewrite -> (fold_unfold_power_v0_S x n').
    rewrite -> (fold_unfold_power_v1_aux_S x n' a).
    Check (IHn' (x * a)).
    rewrite <- (IHn' (x * a)).
    rewrite -> (Nat.mul_comm x (power_v0 x n')).
    Check (Nat.mul_assoc).
    symmetry.
    exact (Nat.mul_assoc (power_v0 x n') x a).
Qed.

    
Theorem power_v0_and_power_v1_are_equivalent_aux :
  forall x n : nat,
    power_v0 x n = power_v1_aux x n 1.
Proof.
  intros x n.
  induction n as [ | n' IHn']. (* because x is constant, doesn't need to change *)
  - rewrite -> (fold_unfold_power_v0_0 x).
    rewrite -> (fold_unfold_power_v1_aux_0 x 1).
    reflexivity.
  - rewrite -> (fold_unfold_power_v0_S x n').
    rewrite -> (fold_unfold_power_v1_aux_S x n' 1).
    rewrite -> (Nat.mul_1_r x).
    Check (about_power_v0_and_power_v1_aux x n' x).
    rewrite <- (about_power_v0_and_power_v1_aux x n' x).
    Search (_ * _ = _ * _).
    Check (Nat.mul_comm x (power_v0 x n')).
    exact (Nat.mul_comm x (power_v0 x n')).
Qed.
(*  case n' as [ | n'']. (* or use destruct. same keyword *)
    + rewrite -> (fold_unfold_power_v0_0 x).
      rewrite -> (fold_unfold_power_v1_aux_0 x x).
      exact (Nat.mul_1_r x).
    + rewrite -> (fold_unfold_power_v0_S x n'').
      rewrite -> (fold_unfold_power_v1_aux_S x n'' x). *)




Theorem power_v0_and_power_v1_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  unfold power_v1.
  Check (about_power_v0_and_power_v1_aux x n 1).
  rewrite <- (Nat.mul_1_r (power_v0 x n)).
  exact (about_power_v0_and_power_v1_aux x n 1).
Qed.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 =>
    0
  | S n' => match n' with
            | 0 =>
              1
            | S n'' =>
              fib n' + fib n''
            end
  end.

Lemma fold_unfold_lemma_fib_0 :
  fib 0 =
  0.
Proof.
  fold_unfold_tactic fib.
Qed.

Lemma fold_unfold_lemma_fib_S :
  forall n' : nat,
    fib (S n') =
    match n' with
    | 0 =>
      1
    | S n'' =>
      fib n' + fib n''
    end.
Proof.
  fold_unfold_tactic fib.
Qed.

Corollary fold_unfold_lemma_fib_SS :
  forall n'' : nat,
    fib (S (S n'')) =
    fib (S n'') + fib n''.
Proof.
  intro n''.
  Check (fold_unfold_lemma_fib_S (S n'')).
  exact (fold_unfold_lemma_fib_S (S n'')).
Qed.
