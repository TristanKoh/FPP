Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib n'' + fib (S n'').

Theorem there_is_at_most_one_fibonacci_function :
  forall fib1 fib2 : nat -> nat,
    specification_of_the_fibonacci_function fib1 ->
    specification_of_the_fibonacci_function fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_the_fibonacci_function.
  intros [H_fib1_0 [H_fib1_1 H_fib1_SS]]
         [H_fib2_0 [H_fib2_1 H_fib2_SS]]
         n.
  induction n as [ | n' IHn'].
  - rewrite -> H_fib2_0.
    exact H_fib1_0.
  - case n' as [ | n''].
    + rewrite -> H_fib2_1.
      exact H_fib1_1.
    + rewrite -> (H_fib1_SS n'').
      rewrite -> (H_fib2_SS n'').
      rewrite <- IHn'.
  Restart. (* Induction Hypothesis not strong enough. Revert doesn't help *)

  (* Prove more general statements first *)
  intros fib1 fib2.
  unfold specification_of_the_fibonacci_function.
  intros [H_fib1_0 [H_fib1_1 H_fib1_SS]]
         [H_fib2_0 [H_fib2_1 H_fib2_SS]]
         n.
  assert (H_stronger :
            forall m : nat,
              fib1 m = fib2 m /\ fib1 (S m) = fib2 (S m)).
  { intro m.
    induction m as [ | m' [IHm' IHSm']].
    - rewrite -> H_fib2_0.
      rewrite -> H_fib2_1.
      exact (conj H_fib1_0 H_fib1_1).
    - rewrite -> (H_fib1_SS m').
      rewrite -> (H_fib2_SS m').
      rewrite -> IHm'.
      rewrite -> IHSm' at 2.
      (*
      split.
      + exact IHSm'.
      + reflexivity.
       *)
      split; [exact IHSm' | reflexivity]. (* means the same as above *)
  }
  Check (H_stronger n).
  destruct (H_stronger n) as [ly _].
  exact ly.
Qed.         
                      



(*

mathematical induction (aka weak inductioN)

P(0)   forall k : nat, P(k) -> P(S k)
-------------------------------------
forall n : nat, P(n)

course-of-value induction:

P(0)   forall k : nat, P(0) /\ P(1) /\ ... /\ P(k) -> P(S k)
------------------------------------------------------------
forall n : nat, P(n)

strong induction:

P(0)   forall k : nat, (forall i <= k, P(i)) -> P(S k)
------------------------------------------------------
forall n : nat, P(n)

*)

Check nat.
Check nat_ind.


Lemma nat_ind1 :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.
Proof.
  intros P P_0 P_S n.
  induction n as [ | n' IHn'].
  - exact P_0.
  - Check (P_S n').
    Check (P_S n' IHn').
    exact (P_S n' IHn').
Qed. (* We have used mathematical induction to prove mathematical induction *)


Theorem there_is_at_most_one_fibonacci_function' :
  forall fib1 fib2 : nat -> nat,
    specification_of_the_fibonacci_function fib1 ->
    specification_of_the_fibonacci_function fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_the_fibonacci_function.
  intros [H_fib1_0 [H_fib1_1 H_fib1_SS]]
         [H_fib2_0 [H_fib2_1 H_fib2_SS]]
         n.
  assert (H_stronger :
            forall m : nat,
              fib1 m = fib2 m /\ fib1 (S m) = fib2 (S m)).
  { intro m.
    induction m as [ | m' [IHm' IHSm']] using nat_ind1.
    - rewrite -> H_fib2_0.
      rewrite -> H_fib2_1.
      exact (conj H_fib1_0 H_fib1_1).
    - rewrite -> (H_fib1_SS m').
      rewrite -> (H_fib2_SS m').
      rewrite -> IHm'.
      rewrite -> IHSm' at 2.
      split; [exact IHSm' | reflexivity].
  }
  Check (H_stronger n).
  destruct (H_stronger n) as [ly _].
  exact ly.
Qed.         

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n))) ->
    forall n : nat, P n.
Proof.
  intros P P_0 P_1 P_SS n.
  assert (H_stronger :
            forall m : nat,
              P m /\ P (S m)).
  { intro m.
    induction m as [ | m' [IHm' IHSm']].
    - exact (conj P_0 P_1).
    - Check (P_SS m' IHm' IHSm').
      Check (conj IHSm' (P_SS m' IHm' IHSm')).
      exact (conj IHSm' (P_SS m' IHm' IHSm')).
  }
  Check (H_stronger n).
  destruct (H_stronger n) as [ly _].
  exact ly.
Qed.

Theorem there_is_at_most_one_fibonacci_function'' :
  forall fib1 fib2 : nat -> nat,
    specification_of_the_fibonacci_function fib1 ->
    specification_of_the_fibonacci_function fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_the_fibonacci_function.
  intros [H_fib1_0 [H_fib1_1 H_fib1_SS]]
         [H_fib2_0 [H_fib2_1 H_fib2_SS]]
         n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> H_fib2_0.
    exact H_fib1_0.
  - rewrite -> H_fib2_1.
    exact H_fib1_1.
  - rewrite -> (H_fib1_SS n').
    rewrite -> (H_fib2_SS n').
    rewrite -> IHn'.
    rewrite -> IHSn'.
    reflexivity.
Qed.



Lemma nat_ind1' :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.
Proof.
  intros P P_0 P_S n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - exact P_0.
  - Check (P_S 0).
    Check (P_S 0 P_0).
    exact (P_S 0 P_0).
  - Check (P_S (S n')).
    Check (P_S (S n') IHSn').
    exact (P_S (S n') IHSn').
Qed.

(*
forall n, evenp (S (S n)) = evenp n
 *)

Fixpoint evenp1 (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | S n' =>
    negb (evenp1 n')
  end.

Fixpoint evenp2 (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | 1 =>
    false
  | S (S n') =>
    evenp2 n'
  end.

Lemma fold_unfold_evenp1_0 :
  evenp1 0 = true.
Proof.
  fold_unfold_tactic evenp1.
Qed.

Lemma fold_unfold_evenp1_S :
  forall n' : nat,
    evenp1 (S n') = negb (evenp1 n').
Proof.
  fold_unfold_tactic evenp1.
Qed.

Lemma fold_unfold_evenp2_0 :
  evenp2 0 = true.
Proof.
  fold_unfold_tactic evenp2.
Qed.

Lemma fold_unfold_evenp2_S :
  forall n' : nat,
    evenp2 (S n') =
    match n' with
    | 0 =>
      false
    | S n'' =>
      evenp2 n''
    end.
Proof.
  fold_unfold_tactic evenp2.
Qed.

Theorem evenp1_and_evenp2_area_functionally_equal :
  forall n : nat,
    evenp1 n = evenp2 n.
Proof.
  intro n.
  induction n as [ | | n'' IHn'' IHSn''] using nat_ind2.
  - rewrite -> fold_unfold_evenp2_0.
    exact fold_unfold_evenp1_0.
  - rewrite -> fold_unfold_evenp1_S.
    rewrite -> fold_unfold_evenp2_S.
    rewrite -> fold_unfold_evenp1_0.
    unfold negb.
    reflexivity.
  - rewrite -> fold_unfold_evenp1_S.
    rewrite -> fold_unfold_evenp1_S.
    rewrite -> fold_unfold_evenp2_S.
    Search (negb (negb _) = _).
    Check (negb_involutive (evenp1 n'')).
    rewrite -> (negb_involutive (evenp1 n'')).
    exact IHn''.
Qed.

Inductive m22 : Type :=
| M22 : nat -> nat -> nat -> nat -> m22.

Definition m22_add (x y : m22) : m22 :=
  match x with
  | M22 x11 x12
        x21 x22 =>
    match y with
    | M22 y11 y12
          y21 y22 =>
      M22 (x11 + y11) (x12 + y12)
          (x21 + y21) (x22 + y22)
    end
  end.

Definition m22_zero :=
  M22 0 0
      0 0.

Definition m22_one :=
  M22 1 0
      0 1.

Definition m22_mul (x y : m22) : m22 :=
  match x with
  | M22 x11 x12
        x21 x22 =>
    match y with
    | M22 y11 y12
          y21 y22 =>
      M22 (x11 * y11 + x12 * y21) (x11 * y12 + x12 * y22)
          (x21 * y11 + x22 * y21) (x21 * y12 + x22 * y22)
    end
  end.

Lemma aux2 :
  forall (x11 y11 z11 y12 z21 : nat),
  x11 * (y11 * z11 + y12 * z21) =
  z11 * (x11 * y11) + z21 * (x11 * y12).
Proof.
  intros x11 y11 z11 y12 z21.
  Search (_ * (_ + _)).
  rewrite -> (Nat.mul_add_distr_l x11 (y11 * z11) (y12 * z21)).
  Search (_ * (_ * _)).
  rewrite -> (Nat.mul_assoc x11 y11 z11).
  rewrite -> (Nat.mul_assoc x11 y12 z21).
  Search (_ * _ * _).
  rewrite -> (Nat.mul_shuffle0 x11 y11 z11).
  rewrite -> (Nat.mul_shuffle0 x11 y12 z21).
  rewrite <- (Nat.mul_assoc x11 z11 y11).
  rewrite <- (Nat.mul_assoc x11 z21 y12).
  Search (_ * (_ * _)).
  rewrite -> (Nat.mul_shuffle3 x11 z11 y11).
  rewrite -> (Nat.mul_shuffle3 x11 z21 y12).
  reflexivity.
Qed.

Lemma aux :
  forall (x11 y11 z11 y12 z21 x12 y21 y22 : nat),
    (x11 * (y11 * z11 + y12 * z21) + x12 * (y21 * z11 + y22 * z21)) =
    (x11 * y11 + x12 * y21) * z11 + (x11 * y12 + x12 * y22) * z21.
Proof.
  intros x11 y11 z11 y12 z21 x12 y21 y22.
  rewrite -> (aux2 x11 y11 z11 y12 z21).
  rewrite -> (aux2 x12 y21 z11 y22 z21).
  Search (_ + _ + (_ +_)).
  rewrite -> (Nat.add_shuffle1  (z11 * (x11 * y11)) (z21 * (x11 * y12)) (z11 * (x12 * y21)) (z21 * (x12 * y22))).
  rewrite <- (Nat.mul_add_distr_l z11 (x11 * y11) (x12 * y21)).
  rewrite <- (Nat.mul_add_distr_l z21 (x11 * y12) (x12 * y22)).
  Search (_ * _ = _ * _).
  rewrite -> (Nat.mul_comm z11 (x11 * y11 + x12 * y21)).
  rewrite -> (Nat.mul_comm z21 (x11 * y12 + x12 * y22)).
  reflexivity.
Qed.
  
Proposition proposition_10 :
  forall (x y z : m22),
    m22_mul x (m22_mul y z) = m22_mul (m22_mul x y) z.
Proof.
  intros [x11 x12 x21 x22] [y11 y12 y21 y22] [z11 z12 z21 z22].
  unfold m22_mul.
  rewrite -> (aux x11 y11 z11 y12 z21 x12 y21 y22).

  Restart.

  intros [x11 x12 x21 x22] [y11 y12 y21 y22] [z11 z12 z21 z22].
  unfold m22_mul.
  rewrite -> 8 Nat.mul_add_distr_l.
  rewrite -> 16 Nat.mul_assoc.
  rewrite -> 4 (Nat.mul_shuffle0 x11).
  rewrite -> 4 (Nat.mul_shuffle0 x12).
  rewrite -> 4 (Nat.mul_shuffle0 x21).
  rewrite -> 4 (Nat.mul_shuffle0 x22).
  rewrite <- 16 Nat.mul_assoc.
  rewrite -> (Nat.mul_shuffle3 x11).
Admitted. (*
  rewrite -> 4 Nat.add_shuffle1.
  rewrite <- 8 Nat.mul_add_distr_l.
  rewrite -> 8 Nat.mul_comm.
  reflexivity.
Qed. *)

Fixpoint m22_exp (m : m22) (n : nat) : m22 :=
  match n with
  | 0 => m22_one
  | S n' => m22_mul (m22_exp m n') m
  end.


Proposition proposition_14 :
  forall n : nat,
    m22_exp (M22 1 1
                 0 1)
            n =
    M22 1 n
        0 1.
Proof.
Abort.

Proposition exercise_25 :
  forall n : nat,
    m22_exp (M22 1 1
                 1 0)
            n =
    M22 ? ?
        ? ?.
Proof.
Abort.
