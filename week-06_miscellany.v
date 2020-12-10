(* week-06_miscellany.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 19 Sep 2020 *)

(* ********** *)

Require Import Arith Bool.

(* ********** *)

Lemma truism :
  forall P : nat -> Prop,
    (exists n : nat,
        P n) ->
    exists n : nat,
      P n.
Proof.
  intros P H_P.
  exact H_P.

  Restart.

  intros P H_P.
  destruct H_P as [n H_Pn].
  exists n.
  exact H_Pn.

  Restart.

  intros P [n H_Pn].
  exists n.
  exact H_Pn.
Qed.

(* ***** *)

Lemma other_truism :
  forall P Q : nat -> Prop,
    (exists n : nat,
        P n /\ Q n) ->
    exists m : nat,
      P m \/ Q m.
Proof.
  intros P Q [n [H_Pn H_Qn]].
  exists n.
  left.
  exact H_Pn.

  Restart.

  intros P Q [n [H_Pn H_Qn]].
  exists n.
  right.
  exact H_Qn.
Qed.

(* ********** *)

Lemma about_the_existential_quantifier_and_disjunction :
  forall P Q : nat -> Prop,
    (exists n : nat, P n \/ Q n)
    <->
    ((exists n : nat, P n)
     \/
     (exists n : nat, Q n)).
Proof.
  intros P Q.
  split.
  - intros [m [H_m | H_m]].
    + left.
      exists m.
      exact H_m.
    + right.
      exists m.
      exact H_m.
  - intros [[n H_Pn] | [n H_Qn]].
    + exists n.
      left.
      exact H_Pn.
    + exists n.
      right.
      exact H_Qn.
Qed.

(* ********** *)

Lemma about_the_universal_quantifier_and_conjunction :
  forall P Q : nat -> Prop,
    (forall n : nat, P n /\ Q n)
    <->
    ((forall n : nat, P n)
     /\
     (forall n : nat, Q n)).
Proof.
  intros P Q.
  split.
  - intro H_PQ.
    split.
    + intro n.
      destruct (H_PQ n) as [H_Pn _].
      exact H_Pn.
    + intro n.
      destruct (H_PQ n) as [_ H_Qn].
      exact H_Qn.
  - intros [H_P H_Q] n.
    split.
    + exact (H_P n).
    + exact (H_Q n).
Qed.

(* ********** *)

Definition specification_of_addition (add : nat -> nat -> nat) :=
  (forall m : nat,
      add O m = m)
  /\
  (forall n' m : nat,
      add (S n') m = S (add n' m)).

Definition specification_of_addition' (add : nat -> nat -> nat) :=
  forall n' m : nat,
    add O m = m
    /\
    add (S n') m = S (add n' m).

Lemma about_two_universal_quantifiers_and_conjunction :
  forall (P : nat -> Prop)
         (Q : nat -> nat -> Prop),
    ((forall j : nat, P j)
     /\
     (forall i j : nat, Q i j))
    <->
    (forall i j : nat, P j /\ Q i j).
Proof.
  intros P Q.
  split.
  - intros [H_P H_Q] i j.
    split.
    + exact (H_P j).
    + exact (H_Q i j).
  - intro H_PQ.
    split.
    + intro j.
      destruct (H_PQ 0 j) as [H_Pj _].
      exact H_Pj.
    + intros i j.
      destruct (H_PQ i j) as [_ H_Qij].
      exact H_Qij.
Qed.

Proposition the_two_specifications_of_addition_are_equivalent :
  forall add : nat -> nat -> nat,
    specification_of_addition add <-> specification_of_addition' add.
Proof.
  intro add.
  unfold specification_of_addition, specification_of_addition'.
  Check (about_two_universal_quantifiers_and_conjunction
           (fun m : nat => add 0 m = m)
           (fun n' m : nat => add (S n') m = S (add n' m))).
  exact (about_two_universal_quantifiers_and_conjunction
           (fun m : nat => add 0 m = m)
           (fun n' m : nat => add (S n') m = S (add n' m))).
Qed.

(* ********** *)

Lemma even_or_odd_v1 :
  forall n : nat,
    (exists q : nat,
        n = 2 * q)
    \/
    (exists q : nat,
        n = S (2 * q)).
Proof.
Admitted.

Lemma even_or_odd_v2 :
  forall n : nat,
    exists q : nat,
      n = 2 * q
      \/
      n = S (2 * q).
Proof.
Admitted.

(* ********** *)

Lemma O_or_S :
  forall n : nat,
    n = 0 \/ (exists n' : nat, 
                 n = S n').
Proof.
  intro n.
  destruct n as [ | n'] eqn:H_n.

  - left.
    reflexivity.

  - right.
    exists n'.
    reflexivity.
Qed.

Lemma foo :
  forall x y : nat,
    (x, y) = (1, 2) ->
    x = 1 /\ y = 2.
Proof.
  intros x y.
  intro H_xy.
  injection H_xy.
  Abort.

(* ********** *)

Proposition now_what :
  (forall n : nat, n = S n) <-> 0 = 1.
Proof.
  split.

  - intro H_n_Sn.
    Check (H_n_Sn 0).
    exact (H_n_Sn 0).
    
  - intro H_absurd.
    discriminate H_absurd.

  Restart.

  split.

  - intro H_n_Sn.
    Check (H_n_Sn 42).
    discriminate (H_n_Sn 42).

  - intro H_absurd.
    discriminate H_absurd.
Qed.

Proposition what_now :
  forall n : nat,
    n = S n <-> 0 = 1.
Proof.
  intro n.
  split.

  - intro H_n.
    Search (_ <> S _).
    Check (n_Sn n).
    assert (H_tmp := n_Sn n).
    unfold not in H_tmp.
    Check (H_tmp H_n).
    contradiction (H_tmp H_n).

  - intro H_absurd.
    discriminate H_absurd.
Qed.

(* ********** *)

Proposition factoring_and_distributing_a_forall_in_a_conclusion :
  forall (P : nat -> Prop)
         (Q : Prop),
    (Q -> forall n : nat, P n)
    <->
    (forall n : nat,
        Q -> P n).
Proof.
  intros P Q.
  split.
  - intros H_QP n H_Q.
    exact (H_QP H_Q n).
  - intros H_QP H_Q n.
    exact (H_QP n H_Q).
Qed.

(* ********** *)

Proposition interplay_between_quantifiers_and_implication :
  forall (P : nat -> Prop)
         (Q : Prop),
    (exists n : nat, P n -> Q) ->
    (forall n : nat, P n) -> Q.
Proof.
  intros P Q [n H_PnQ] H_P.
  Check (H_PnQ (H_P n)).
  exact (H_PnQ (H_P n)).
Qed.    

(* ********** *)

Proposition interplay_between_implication_and_quantifiers :
  forall (P : nat -> Prop)
         (Q : Prop),
    ((exists n : nat, P n) -> Q) ->
    forall n : nat, P n -> Q.
Proof.
  intros P Q H_PQ n H_Pn.
  apply H_PQ.
  exists n.
  exact H_Pn.
Qed.

(* ********** *)

Proposition strenghtening_X_in_the_conclusion :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> Y) -> A -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
  intro H_A.
  Check (H_AX H_A).
  Check (H_XY (H_AX H_A)).
  exact (H_XY (H_AX H_A)).

  Restart.

  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
  intro H_A.
  apply H_XY.
  apply H_AX.
  apply H_A.
Qed.

Proposition weakening_X_in_the_conclusion :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> Y) -> C -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
Abort.

Proposition strenghtening_Y_in_the_conclusion :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> Y) -> X -> B.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
Abort.

Proposition weakening_Y_in_the_conclusion :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> Y) -> X -> D.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
  intro H_X.
  Check (H_XY H_X).
  Check (H_YD (H_XY H_X)).
  exact (H_YD (H_XY H_X)).

  Restart.

  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
  intro H_X.
  apply H_YD.
  apply H_XY.
  apply H_X.
Qed.

Proposition strenghtening_X_in_a_premise :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (A -> Y) -> X -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD.
Abort.

Proposition weakening_X_in_a_premise :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (C -> Y) -> X -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD.
  intros H_CY H_X.
  Check (H_XC H_X).
  Check (H_CY (H_XC H_X)).
  exact (H_CY (H_XC H_X)).
  
  Restart.

  intros A B C D X Y H_AX H_BY H_XC H_YD.
  intros H_CY H_X.
  apply H_CY.
  apply H_XC.
  apply H_X.
Qed.

Proposition strenghtening_Y_in_a_premise :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> B) -> X -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD.
  intros H_XB H_X.
  Check (H_XB H_X).
  Check (H_BY (H_XB H_X)).
  exact (H_BY (H_XB H_X)).

  Restart.

  intros A B C D X Y H_AX H_BY H_XC H_YD.
  intros H_XB H_X.
  apply H_BY.
  apply H_XB.
  apply H_X.
Qed.

Proposition weakening_Y_in_a_premise :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> D) -> X -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD.
Abort.


Proposition product_of_two_consecutive_nats_is_even :
  forall n: nat,
    (exists q : nat,
        n * (S n) = 2 * q).
Proof.
  intro n.
  induction n as [ | n' [m IHn']].
  - exists 0.
    rewrite -> (Nat.mul_0_r 2).
    exact (Nat.mul_0_l 1).
  - Search (S _ *  _).
    rewrite -> (Nat.mul_succ_l n' (S (S n'))).
    rewrite -> (Nat.mul_succ_r n' (S n')).
    (* rewrite -> (Nat.mul_succ_r n' n'). *)
    case (even_or_odd_v1 n') as [[p H_even] | [p H_odd]].
    * exists (m + p + S p).
      rewrite -> IHn'.
      rewrite -> H_even.
      Search (_ * (_ + _)).
      rewrite -> (Nat.mul_add_distr_l 2 (m + p) (S p)).
      rewrite -> (Nat.mul_add_distr_l 2 m p).
      rewrite -> (Nat.mul_succ_l 1 p) at 2.
      rewrite -> (Nat.mul_1_l p).
      Search (S (_ + _)).
      rewrite <- (Nat.add_succ_l p p).
      rewrite <- (Nat.add_succ_r (S p) p).
      rewrite -> (Nat.mul_succ_l 1 (S p)).
      rewrite -> (Nat.mul_1_l (S p)).
      reflexivity.
    * exists (m + S (S (2 * p))).
      rewrite -> IHn'.
      rewrite -> H_odd.
      rewrite -> (Nat.mul_add_distr_l 2 m (S (S (2 * p)))).
      rewrite -> (Nat.mul_succ_l 1 (S (S (2 * p)))).
      rewrite -> (Nat.mul_1_l (S (S (2 * p)))).
      rewrite -> (Nat.add_succ_l (S (2 * p)) (S (S (2 * p)))).
      rewrite <- (Nat.add_succ_r (S (2 * p)) (S (S (2 * p)))).
      Search (_ + (_ + _)).
      rewrite <- (Nat.add_assoc (2 * m) (S (2 * p)) (S (S (S (2 * p))))).
      reflexivity.

  Restart.

  intro n.
  case (even_or_odd_v1 n) as [[p H_even] | [p H_odd]].
  - exists (p * (S (2 * p))).
    rewrite -> H_even.
    Search (_ * (_ * _)).
    rewrite -> (Nat.mul_assoc 2 p (S (2 * p))).
    reflexivity.
  - exists ((S p) * (S p)).
    rewrite -> H_odd.
    rewrite -> (Nat.mul_succ_l 1 p).
    rewrite -> (Nat.mul_1_l p).
    rewrite -> (Nat.mul_comm (S (p + p)) (S (S (p + p)))).
    rewrite -> (Nat.mul_succ_l (S (p + p)) (S (p + p))).
    rewrite -> (Nat.mul_succ_l 1 (S p * S p)).
    rewrite -> (Nat.mul_1_l (S p * S p)).
    
    
(*
    S (2 * p) * (S (S (2 * p)))
                       (2 * p) * ((2 * p) + 1 + 1) + ((2 * p) + 1 + 1)
*)
Qed.
      
  
(* ********** *)

(* end of week-06_miscellany.v *)
