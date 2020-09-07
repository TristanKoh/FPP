(* week-04_exercises.v *)
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

(* Exercise 9 *)

Proposition foo :
  forall P Q R1 R2 : Prop,
    P -> (P -> Q) -> (Q -> R1) /\ (Q -> R2) -> R1 /\ R2.
Proof.
  (* Backwards proof *)
  intros P Q R1 R2.
  intros H_P H_P_implies_Q H_Q_implies_R1_and_Q_implies_R2.
  destruct H_Q_implies_R1_and_Q_implies_R2 as [H_Q_implies_R1 H_Q_implies_R2].
  split.
  - apply H_Q_implies_R1.
    apply H_P_implies_Q.
    exact H_P.
  - apply H_Q_implies_R2.
    apply H_P_implies_Q.
    exact H_P.

    Restart.
    
  (* Forwards proof *)
  intros P Q R1 R2.
  intros H_P H_P_implies_Q H_Q_implies_R1_and_Q_implies_R2.
  destruct H_Q_implies_R1_and_Q_implies_R2 as [H_Q_implies_R1 H_Q_implies_R2].
  assert (H_Q := H_P_implies_Q H_P).
  assert (H_R1 := H_Q_implies_R1 H_Q).
  assert (H_R2 := H_Q_implies_R2 H_Q).
  exact (conj H_R1 H_R2).
Qed.

(* Exercise 10 *)


Proposition bar :
  forall P1 P2 Q R1 R2 T1 T2 : Prop,
    P1 -> (P1 -> P2) -> (P2 -> Q) -> (Q -> R1) -> (R1 -> T1) -> (Q -> R2) -> (R2 -> T2) -> T1 /\ T2.
Proof.

  (* Split as early as possible *)
  intros P1 P2 Q R1 T1 R2 T2.
  intros H_P1 H_P1_implies_P2 H_P2_implies_Q H_Q_implies_R1 H_R1_implies_R2 H_Q_implies_T1 H_T1_implies_T2.
  split.
  - apply H_R1_implies_R2.
    apply H_Q_implies_R1.
    apply H_P2_implies_Q.
    apply H_P1_implies_P2.
    exact H_P1.
  - apply H_T1_implies_T2.
    apply H_Q_implies_T1.
    apply H_P2_implies_Q.
    apply H_P1_implies_P2.
    exact H_P1.

    Restart.

    (* Split as late as possible *)
    intros P1 P2 Q R1 T1 R2 T2.
    intros H_P1 H_P1_implies_P2 H_P2_implies_Q H_Q_implies_R1 H_R1_implies_R2 H_Q_implies_T1 H_T1_implies_T2.
    assert (H_P2 := H_P1_implies_P2 H_P1).
    assert (H_Q := H_P2_implies_Q H_P2).
    assert (H_R1 := H_Q_implies_R1 H_Q).
    assert (H_R2 := H_R1_implies_R2 H_R1).
    assert (H_T1 := H_Q_implies_T1 H_Q).
    assert (H_T2 := H_T1_implies_T2 H_T1).
    split.
  - exact H_R2.
  - exact H_T2.

    Restart.

    (* Without splitting at all *)
    intros P1 P2 Q R1 T1 R2 T2.
    intros H_P1 H_P1_implies_P2 H_P2_implies_Q H_Q_implies_R1 H_R1_implies_R2 H_Q_implies_T1 H_T1_implies_T2.
    assert (H_P2 := H_P1_implies_P2 H_P1).
    assert (H_Q := H_P2_implies_Q H_P2).
    assert (H_R1 := H_Q_implies_R1 H_Q).
    assert (H_R2 := H_R1_implies_R2 H_R1).
    assert (H_T1 := H_Q_implies_T1 H_Q).
    assert (H_T2 := H_T1_implies_T2 H_T1).
    exact (conj H_R2 H_T2).
Qed.


(* Exercise 11 *)


Proposition baz :
  forall P Q R T U1 U2 : Prop,
    P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> U1) -> (T -> U2) -> U1 /\ U2.
Proof.

  (* Using split as early as possible *)
  
  intros P Q R T U1 U2.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2.
  split.
  - apply H_T_implies_U1.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P_implies_Q.
    exact H_P.
  - apply H_T_implies_U2.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P_implies_Q.
    exact H_P.

    Restart.

    (* Using split as late as possible *)
    
    intros P Q R T U1 U2.
    intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2.
    assert (H_Q := H_P_implies_Q H_P).
    assert (H_R := H_Q_implies_R H_Q).
    assert (H_T := H_R_implies_T H_R).
    assert (H_U1 := H_T_implies_U1 H_T).
    assert (H_U2 := H_T_implies_U2 H_T).
    split.
  - exact H_U1.
  - exact H_U2.
Qed.


(* Exercise 12 *)

(* Part a *)
Proposition baz_dual_early :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros H_P1_or_P2 H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  destruct H_P1_or_P2 as [H_P1 | H_P2].
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P1_implies_Q.
    exact H_P1.
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P2_implies_Q.
    exact H_P2.
Qed.

(* Part b *)

Proposition baz_dual_late :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros H_P1_or_P2 H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  apply H_T_implies_U.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  destruct H_P1_or_P2 as [H_P1 | H_P2].
  - apply (H_P1_implies_Q).
    exact H_P1.
  - apply (H_P2_implies_Q).
    exact H_P2.
Qed.


(* Part d *)
Proposition baz_dual_early_or_late :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros [H_P1 | H_P2] H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P1_implies_Q.
    exact H_P1.
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P2_implies_Q.
    exact H_P2.

    Restart.

    intros P1 P2 Q R T U.
    intros [H_P1 | H_P2] H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  - assert (H_Q := H_P1_implies_Q H_P1).
    assert (H_R := H_Q_implies_R H_Q).
    assert (H_T := H_R_implies_T H_R).
    assert (H_U := H_T_implies_U H_T).
    exact H_U.
  - assert (H_Q := H_P2_implies_Q H_P2).
    assert (H_R := H_Q_implies_R H_Q).
    assert (H_T := H_R_implies_T H_R).
    assert (H_U := H_T_implies_U H_T).
    exact H_U.
Qed.



(* Exercise 13 *)
Proposition ladidah :
  forall P1 P2 P3 P4 Q R T U : Prop,
    (P1 \/ P2) \/ (P3 \/ P4) -> (P1 -> Q) -> (P2 -> Q) -> (P3 -> Q) -> (P4 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
  intros P1 P2 P3 P4 Q R T U.
  intros H_P1_or_P2_or_P3_or_P4 H_P1_implies_Q H_P2_implies_Q H_P3_implies_Q H_P4_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  destruct H_P1_or_P2_or_P3_or_P4 as [[H_P1 | H_P2] | [H_P3 | H_P4]].
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P1_implies_Q.
    exact H_P1.
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P2_implies_Q.
    exact H_P2.
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P3_implies_Q.
    exact H_P3.
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P4_implies_Q.
    exact H_P4.


    Restart.

    intros P1 P2 P3 P4 Q R T U.
    intros H_P1_or_P2_or_P3_or_P4 H_P1_implies_Q H_P2_implies_Q H_P3_implies_Q H_P4_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
    destruct H_P1_or_P2_or_P3_or_P4 as [[H_P1 | H_P2] | [H_P3 | H_P4]].
  - assert (H_Q := H_P1_implies_Q H_P1).
    assert (H_R := H_Q_implies_R H_Q).
    assert (H_T := H_R_implies_T H_R).
    assert (H_U := H_T_implies_U H_T).
    exact H_U.
  -  assert (H_Q := H_P2_implies_Q H_P2).
     assert (H_R := H_Q_implies_R H_Q).
     assert (H_T := H_R_implies_T H_R).
     assert (H_U := H_T_implies_U H_T).
     exact H_U.
  -  assert (H_Q := H_P3_implies_Q H_P3).
     assert (H_R := H_Q_implies_R H_Q).
     assert (H_T := H_R_implies_T H_R).
     assert (H_U := H_T_implies_U H_T).
     exact H_U.
  -  assert (H_Q := H_P4_implies_Q H_P4).
     assert (H_R := H_Q_implies_R H_Q).
     assert (H_T := H_R_implies_T H_R).
     assert (H_U := H_T_implies_U H_T).
     exact H_U.
Qed.


Proposition toodeloo :
  forall P Q R T U1 U2 U3 U4: Prop,
    P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> U1) -> (T -> U2) -> (T -> U3) -> (T -> U4) -> (U1 /\ U2) /\ (U3 /\ U4).
Proof.
  intros P Q R T U1 U2 U3 U4.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2 H_T_implies_U3 H_T_implies_U4.
  split.
  - split.
    -- apply H_T_implies_U1.
       apply H_R_implies_T.
       apply H_Q_implies_R.
       apply H_P_implies_Q.
       exact H_P.
    -- apply H_T_implies_U2.
       apply H_R_implies_T.
       apply H_Q_implies_R.
       apply H_P_implies_Q.
       exact H_P.
  - split.
    -- apply H_T_implies_U3.
       apply H_R_implies_T.
       apply H_Q_implies_R.
       apply H_P_implies_Q.
       exact H_P.
    -- apply H_T_implies_U4.
       apply H_R_implies_T.
       apply H_Q_implies_R.
       apply H_P_implies_Q.
       exact H_P.
Qed.


(* Equational reasoning about arithmetic functions *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Two implementations of the addition function *)

(* ***** *)

(* Unit tests *)

Definition test_add (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 1)
  &&
  (candidate 1 0 =n= 1)
  &&
  (candidate 1 1 =n= 2)
  &&
  (candidate 1 2 =n= 3)
  &&
  (candidate 2 1 =n= 3)
  &&
  (candidate 2 2 =n= 4)
  (* etc. *)
  .

(* ***** *)

(* Recursive implementation of the addition function *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
  | O =>
    j
  | S i' =>
    S (add_v1 i' j)
  end.

Compute (test_add add_v1).

Lemma fold_unfold_add_v1_O :
  forall j : nat,
    add_v1 O j =
    j.
Proof.
  fold_unfold_tactic add_v1.
Qed.

Lemma fold_unfold_add_v1_S :
  forall i' j : nat,
    add_v1 (S i') j =
    S (add_v1 i' j).
Proof.
  fold_unfold_tactic add_v1.
Qed.

(* ***** *)

(* Tail-recursive implementation of the addition function *)

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

Lemma fold_unfold_add_v2_O :
  forall j : nat,
    add_v2 O j =
    j.
Proof.
  fold_unfold_tactic add_v2.
Qed.

Lemma fold_unfold_add_v2_S :
  forall i' j : nat,
    add_v2 (S i') j =
    add_v2 i' (S j).
Proof.
  fold_unfold_tactic add_v2.
Qed.

(* ********** *)

(* Equivalence of add_v1 and add_v2 *)

(* ***** *)

(* The master lemma: *)

Lemma about_add_v2 :
  forall i j : nat,
    add_v2 i (S j) = S (add_v2 i j).
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v2_O (S j)).

  - intro j.
    rewrite -> (fold_unfold_add_v2_S i' (S j)).
    rewrite -> (fold_unfold_add_v2_S i' j).
    Check (IHi' (S j)).
    exact (IHi' (S j)).
Qed.

(* ***** *)

(* The main theorem: *)

Theorem equivalence_of_add_v1_and_add_v2 :
  forall i j : nat,
    add_v1 i j = add_v2 i j.
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v1_O j).

  - intro j.
    rewrite -> (fold_unfold_add_v1_S i' j).
    rewrite -> (fold_unfold_add_v2_S i' j).
    rewrite -> (IHi' j).
    symmetry.
    exact (about_add_v2 i' j).
Qed.

(* ********** *)

(* Neutral (identity) element for addition *)

(* ***** *)

Property O_is_left_neutral_wrt_add_v1 :
  forall y : nat,
    add_v1 0 y = y.
Proof.
Abort.

(* ***** *)

Property O_is_left_neutral_wrt_add_v2 :
  forall y : nat,
    add_v2 0 y = y.
Proof.
Abort.

(* ***** *)

Property O_is_right_neutral_wrt_add_v1 :
  forall x : nat,
    add_v1 x 0 = x.
Proof.
  intro x.
  induction x as [ | x' IHx'].
  - Check (fold_unfold_add_v1_O).
    rewrite -> (fold_unfold_add_v1_O 0).
    reflexivity.
  - Check (fold_unfold_add_v1_S).
    rewrite -> (fold_unfold_add_v1_S x' 0).
    rewrite -> IHx'.
    reflexivity.
Qed.

Property O_is_right_neutral_wrt_add_v2 :
  forall x : nat,
    add_v2 x 0 = x.
Proof.
Abort.

(* ********** *)

(* Associativity of addition *)

(* ***** *)

Property add_v1_is_associative :
  forall x y z : nat,
    add_v1 x (add_v1 y z) = add_v1 (add_v1 x y) z.
Proof.
Abort.

(* ***** *)

Property add_v2_is_associative :
  forall x y z : nat,
    add_v2 x (add_v2 y z) = add_v2 (add_v2 x y) z.
Proof.
Abort.

(* ********** *)

(* Commutativity of addition *)

(* ***** *)

Property add_v1_is_commutative :
  forall x y : nat,
    add_v1 x y = add_v1 y x.
Proof.
Abort.

(* ***** *)

Property add_v2_is_commutative :
  forall x y : nat,
    add_v2 x y = add_v2 y x.
Proof.
Abort.

(* ********** *)

(* Four implementations of the multiplication function *)

(* ***** *)

(* Unit tests *)

Definition test_mul (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 0)
  &&
  (candidate 1 0 =n= 0)
  &&
  (candidate 1 1 =n= 1)
  &&
  (candidate 1 2 =n= 2)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 2 3 =n= 6)
  &&
  (candidate 3 2 =n= 6)
  &&
  (candidate 6 4 =n= 24)
  &&
  (candidate 4 6 =n= 24)
  (* etc. *)
  .

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v1 *)

Fixpoint mul_v11 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v1 (mul_v11 x' y) y
  end.

Compute (test_mul mul_v11).

Lemma fold_unfold_mul_v11_O :
  forall y : nat,
    mul_v11 O y =
    O.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

Lemma fold_unfold_mul_v11_S :
  forall x' y : nat,
    mul_v11 (S x') y =
    add_v1 (mul_v11 x' y) y.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v2 *)

Fixpoint mul_v12 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v2 (mul_v12 x' y) y
  end.

Compute (test_mul mul_v11).

Lemma fold_unfold_mul_v12_O :
  forall y : nat,
    mul_v12 O y =
    O.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

Lemma fold_unfold_mul_v12_S :
  forall x' y : nat,
    mul_v12 (S x') y =
    add_v2 (mul_v12 x' y) y.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

(* ***** *)

(* Exercise 27 *)

(* Tail-recursive implementation of the multiplication function, using add_v1 *)

Fixpoint mul_v21_aux (x y a : nat) : nat :=
  match y with
  | O =>
    a
  | S y' =>
    mul_v21_aux x y' (add_v1 x a)
  end.

Definition mul_v21 (x y : nat) : nat :=
  mul_v21_aux x y 0.

Compute (test_mul mul_v21).

Lemma fold_unfold_mul_v21_aux_0 :
  forall x a : nat,
    mul_v21_aux x 0 a =
    a.
Proof.
  fold_unfold_tactic mul_v21_aux.
Qed.

Lemma fold_unfold_mul_v21_aux_S :
  forall x y' a : nat,
    mul_v21_aux x (S y') a =
    mul_v21_aux x y' (add_v1 x a).
Proof.
  fold_unfold_tactic mul_v21_aux.
Qed.

(* ***** *)

(* Exercise 28 *)

(* Tail-recursive implementation of the multiplication function, using add_v2 *)

Fixpoint mul_v22_aux (x y a : nat) : nat :=
  match y with
  | O =>
    a
  | S y' =>
    mul_v22_aux x y' (add_v2 x a)
  end.

Definition mul_v22 (x y : nat) : nat :=
  mul_v22_aux x y 0.

Compute (test_mul mul_v22).

Lemma fold_unfold_mul_v22_aux_0 :
  forall x a : nat,
    mul_v22_aux x 0 a = a.
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.

Lemma fold_unfold_mul_v22_aux_S :
  forall x y' a : nat,
    mul_v22_aux x (S y') a =
    mul_v22_aux x y' (add_v2 x a).
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.

(* ********** *)

(* Exercise 29 *)

(* Equivalence of mul_v11, mul_v12, mul_v21, and mul_v22 *)

(* ***** *)

Theorem equivalence_of_mul_v11_and_mul_v12 :
  forall i j : nat,
    mul_v11 i j = mul_v12 i j.
Proof.
  intros i j.               
  induction i as [ | i' IHi'].
  - Check (fold_unfold_mul_v11_O).
    rewrite -> (fold_unfold_mul_v11_O j).
    rewrite -> (fold_unfold_mul_v12_O j).
    reflexivity.
  - Check (fold_unfold_mul_v11_S i' j).
    rewrite -> (fold_unfold_mul_v11_S i' j).
    rewrite -> (fold_unfold_mul_v12_S i' j).
    Check (equivalence_of_add_v1_and_add_v2 (mul_v11 i' j) j).
    rewrite -> (equivalence_of_add_v1_and_add_v2 (mul_v11 i' j) j).
    rewrite -> IHi'.
    reflexivity.
Qed.
    
(* ***** *)

(* ... *)

(* ***** *)

(* ... *)

(* ***** *)


Lemma equivalence_of_mul_v21_aux_and_mul_v22_aux :
  forall i j a : nat,
    mul_v21_aux i j a = mul_v22_aux i j a.
Proof.
  intros i j.
  induction j as [ | j' IHj'].
  - intro a.
    Check (fold_unfold_mul_v22_aux_0).
    rewrite -> (fold_unfold_mul_v22_aux_0 i a).
    rewrite -> (fold_unfold_mul_v21_aux_0 i a).
    reflexivity.
  - intro a.
    Check (fold_unfold_mul_v22_aux_S).
    rewrite -> (fold_unfold_mul_v22_aux_S i j' a).
    rewrite -> (fold_unfold_mul_v21_aux_S i j' a).
    Check (equivalence_of_add_v1_and_add_v2).
    rewrite -> (equivalence_of_add_v1_and_add_v2 i a).
    rewrite -> (IHj' (add_v2 i a)).
    reflexivity.
Qed.
    

Theorem equivalence_of_mul_v21_and_mul_v22 :
  forall i j : nat,
    mul_v21 i j = mul_v22 i j.
Proof.
  intros i j.
  unfold mul_v22.
  unfold mul_v21.
  exact (equivalence_of_mul_v21_aux_and_mul_v22_aux i j 0).
Qed.


       
(* end of week-04_exercises.v *)
