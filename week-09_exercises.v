(* week-09_exercises.v *)
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

(* Exercise 1 *)

Inductive m22 : Type :=
| M22 : nat -> nat -> nat -> nat -> m22.


(* Function to add 2x2 matrices *)

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

(* Part a: Definition 9 - Multiplication *)

Definition m22_mul (x y : m22) : m22 :=
  match x with
  | M22 x11 x12
        x21 x22 =>
    match y with
    | M22 y11 y12
          y21 y22 =>
      M22 ((x11 * y11) + (x12 * y21)) ((x11 * y12) + (x12 * y22))
          ((x21 * y11) + (x22 * y21)) ((x21 * y12) + (x22 * y22))
    end
  end.


(* Part b: Proposition 10 - Associativity of matrix multiplication *)

Proposition proposition_10 :
  forall m22_1 m22_2 m22_3 : m22,
    m22_mul m22_1 (m22_mul m22_2 m22_3) = m22_mul (m22_mul m22_1 m22_2) m22_3.
Proof.
  intros [x11 x12 x21 x22]
         [y11 y12 y21 y22]
         [z11 z12 z21 z22].
  unfold m22_mul.  
  Search (_ * (_ + _)).
  rewrite ->8 Nat.mul_add_distr_l.
  rewrite ->8 Nat.mul_add_distr_r.
  Search (_ * (_ * _)).
  rewrite ->16 Nat.mul_assoc.
  Search (_ + (_ + _)).  
  rewrite ->8 Nat.add_assoc.

Admitted.


(* Part c: Proposition 12 - Identity matrix is left and right neutral *)

Proposition proposition_12_left_neutral :
  forall x : m22,
    m22_mul m22_one x = x.
Proof.
  intros [x11 x12 x21 x22].
  unfold m22_one, m22_mul.
  Search (1 * _).
  rewrite ->4 Nat.mul_1_l.
  Search (0 * _).
  rewrite ->4 Nat.mul_0_l.
  Search (_ + 0).
  rewrite ->2 Nat.add_0_r.
  rewrite ->2 Nat.add_0_l.
  reflexivity.
Qed.

Proposition proposition_12_right_neutral :
  forall x : m22,
    m22_mul x m22_one = x.
Proof.
  intros [x11 x12 x21 x22].
  unfold m22_one, m22_mul.
  rewrite ->4 Nat.mul_1_r.
  rewrite -> 4 Nat.mul_0_r.
  rewrite ->2 Nat.add_0_l.
  rewrite ->2 Nat.add_0_r.
  reflexivity.
Qed.

 
(* Part d: Definition 13 - Matrix exponentiation function *)

Fixpoint m22_exp (x : m22) (n : nat) : m22 :=
  match n with
  | 0 =>
    m22_one
  | S n' =>
    m22_mul (m22_exp x n') x
  end.

Lemma fold_unfold_m22_exp_O :
  forall x : m22,
    m22_exp x 0 =
    m22_one.
Proof.
  fold_unfold_tactic m22_exp.
Qed.

Lemma fold_unfold_m22_exp_S :
  forall (x : m22)
         (n' : nat),
    m22_exp x (S n') =
    m22_mul (m22_exp x n') x.
Proof.
  fold_unfold_tactic m22_exp.
Qed.


(* Part e - Proposition 14 *)

Proposition proposition_14 :
  forall n : nat,
    m22_exp (M22 1 1
                 0 1) n =
    M22 1 n
        0 1.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  - rewrite -> (fold_unfold_m22_exp_O (M22 1 1 0 1)).
    unfold m22_one.
    reflexivity.
  - rewrite -> (fold_unfold_m22_exp_S (M22 1 1 0 1) n').
    rewrite -> IHn'.
    unfold m22_mul.
    rewrite -> Nat.mul_0_l.
    rewrite ->2 Nat.mul_0_r.
    Search (_ + 0).
    rewrite ->2 Nat.add_0_r.
    rewrite -> Nat.add_0_l.
    rewrite -> (Nat.mul_1_l 1).
    rewrite -> Nat.mul_1_r.
    Search (1 + _).
    rewrite -> (Nat.add_1_l n').
    reflexivity.
Qed.



(* Part g - Exercise 25 *)

Compute (m22_exp (M22 1 1
                      1 0) 0).

Compute (m22_exp (M22 1 1
                      1 0) 1).

Compute (m22_exp (M22 1 1
                      1 0) 2).

Compute (m22_exp (M22 1 1
                      1 0) 3).

Compute (m22_exp (M22 1 1
                      1 0) 4).

Compute (m22_exp (M22 1 1
                      1 0) 5).

Compute (m22_exp (M22 1 1
                      1 0) 6).

Compute (m22_exp (M22 1 1
                      1 0) 7).


Fixpoint fib_aux (n : nat) : nat :=
  match n with
  | 0 =>
    0
  | S n' =>
    match n' with
    | 0 =>
      1
    | S n'' =>
      fib_aux n' + fib_aux n''
  end
end.

Definition fib (n : nat) : nat :=
  fib_aux n.

Lemma fold_unfold_fib_aux_O :
  fib_aux 0 =
  0.
Proof.
  fold_unfold_tactic fib_aux.
Qed.

Lemma fold_unfold_fib_aux_1 :
  fib_aux 1 =
  1.
Proof.
  fold_unfold_tactic fib_aux.
Qed.


Lemma fold_unfold_fib_aux_S :
  forall n' : nat,
    fib_aux (S (S n')) =
    fib_aux (S n') + fib_aux n'.
Proof.
  fold_unfold_tactic fib_aux.
Qed.


Proposition exercise_25 :
  forall n : nat,
    m22_exp (M22 1 1
                 1 0) (S n) =
    M22 (fib (S (S n))) (fib (S n))
        (fib (S n)) (fib n).
Proof.
  intro n.
  unfold fib.
  induction n as [ | n' IHn'].
  - rewrite -> fold_unfold_fib_aux_O.
    rewrite -> fold_unfold_fib_aux_1.
    rewrite -> (fold_unfold_fib_aux_S 0).
    rewrite -> fold_unfold_fib_aux_O.
    rewrite -> fold_unfold_fib_aux_1.
    rewrite -> (Nat.add_0_r 1).
    unfold m22_exp.
    Check proposition_12_left_neutral. 
    rewrite -> (proposition_12_left_neutral (M22 1 1 1 0)).
    reflexivity.
  - Check (fold_unfold_m22_exp_S).
    rewrite -> (fold_unfold_m22_exp_S (M22 1 1 1 0) (S n')).
    rewrite -> IHn'.
    unfold m22_mul.
    rewrite ->3 Nat.mul_1_r.
    rewrite ->2 Nat.mul_0_r.
    rewrite ->2 Nat.add_0_r.
    Check (fold_unfold_fib_aux_S).
    rewrite <- (fold_unfold_fib_aux_S (S n')).
    rewrite <- (fold_unfold_fib_aux_S n').
    reflexivity.
Qed.

    
(* Part h - Definition 27 *)

Fixpoint m22_exp' (x : m22) (n : nat) : m22 :=
  match n with
  | 0 =>
    m22_one
  | S n' =>
    m22_mul x (m22_exp' x n')
  end.

Lemma fold_unfold_m22_exp'_O :
  forall x : m22,
  m22_exp' x 0 =
  m22_one.
Proof.
  fold_unfold_tactic m22_exp'.
Qed.

Lemma fold_unfold_m22_exp'_S :
  forall (x : m22)
         (n' : nat),
    m22_exp' x (S n') =
    m22_mul x (m22_exp' x n').
Proof.
  fold_unfold_tactic m22_exp'.
Qed.


(* Part i - Equivalence of m22_exp and m22_exp' *)

Proposition definition_13_and_27_are_equivalent :
  forall (x : m22)
         (n : nat),
    m22_exp x n = m22_exp' x n.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - rewrite -> fold_unfold_m22_exp_O.
    rewrite -> fold_unfold_m22_exp'_O.
    reflexivity.
  - rewrite -> fold_unfold_m22_exp_S.
    rewrite -> fold_unfold_m22_exp'_S.
    rewrite -> IHn'.

   
Abort.


(* Part j - Definition 35, Transposition of matrix *)

Definition m22_transpose (x : m22) : m22 :=
  match x with
  | M22 x11 x12
        x21 x22 =>
    M22 x11 x21
        x12 x22
  end.


(* Part k - Property 36, Transposition is involutive *)

Proposition property_36 :
  forall x : m22,
    m22_transpose (m22_transpose x) = x.
Proof.
  intros [x11 x12 x21 x22].
  unfold m22_transpose.
  reflexivity.
Qed.


(* Part l - Proposition 38, Transposition and exponentiation commute with each other *)


Lemma lemma_37 :
  forall x y : m22,
    m22_transpose (m22_mul x y) = m22_mul (m22_transpose y) (m22_transpose x).
Proof.
  intros [x11 x12 x21 x22]
         [y11 y12 y21 y22].
  unfold m22_transpose.
  unfold m22_mul.
  rewrite -> (Nat.mul_comm x11 y11).
  rewrite -> (Nat.mul_comm x12 y21).
  rewrite -> (Nat.mul_comm x21 y11).
  rewrite -> (Nat.mul_comm x22 y21).
  rewrite -> (Nat.mul_comm x11 y12).
  rewrite -> (Nat.mul_comm x12 y22).
  rewrite -> (Nat.mul_comm x21 y12).
  rewrite -> (Nat.mul_comm x22 y22).
  reflexivity.
Qed.


Proposition proposition_29 :
  forall (x : m22)
         (n : nat),
    m22_mul x (m22_exp x n) = m22_mul (m22_exp x n) x.
Proof.
  intros [x11 x12 x21 x22] n.
  induction n as [ | n' IHn'].
  - rewrite -> (fold_unfold_m22_exp_O (M22 x11 x12 x21 x22)).
    unfold m22_mul.
    unfold m22_one.
    rewrite ->4 Nat.mul_1_r.
    rewrite ->4 Nat.mul_0_r.
    rewrite ->2 Nat.add_0_r.
    rewrite ->2 Nat.add_0_l.
    rewrite ->4 Nat.mul_1_l.
    rewrite ->4 Nat.mul_0_l.
    rewrite ->2 Nat.add_0_r.
    rewrite ->2 Nat.add_0_l.
    reflexivity.    
  - rewrite -> (fold_unfold_m22_exp_S (M22 x11 x12 x21 x22)).
    Check (proposition_10).
    rewrite -> (proposition_10 (M22 x11 x12 x21 x22) (m22_exp (M22 x11 x12 x21 x22) n') (M22 x11 x12 x21 x22)).
    rewrite -> IHn'.
    reflexivity.
Qed.

    
Proposition proposition_38 :
  forall (x : m22)
         (n : nat),
    m22_transpose (m22_exp x n) = m22_exp (m22_transpose x) n.
Proof.
  intros [x11 x12 x21 x22] n.
  induction n as [ | n' IHn'].
  - Check (fold_unfold_m22_exp_O).
    rewrite -> (fold_unfold_m22_exp_O (M22 x11 x12 x21 x22)).
    rewrite -> (fold_unfold_m22_exp_O (m22_transpose (M22 x11 x12 x21 x22))).
    unfold m22_transpose.
    unfold m22_one.
    reflexivity.
  - Check (fold_unfold_m22_exp_S).
    rewrite -> (fold_unfold_m22_exp_S (M22 x11 x12 x21 x22)).
    Check (lemma_37).
    rewrite -> (lemma_37 (m22_exp (M22 x11 x12 x21 x22) n') (M22 x11 x12 x21 x22)).
    rewrite -> IHn'.
    Check (proposition_29).
    rewrite -> (proposition_29 (m22_transpose (M22 x11 x12 x21 x22)) n').
    rewrite -> (fold_unfold_m22_exp_S (m22_transpose (M22 x11 x12 x21 x22))).
    reflexivity.
Qed.    


(* Part m - Exericse 40*)






(* Week 7 Exercise 2 *)

(* ********** *)

Definition is_a_sound_and_complete_equality_predicate (V : Type) (V_eqb : V -> V -> bool) :=
  forall v1 v2 : V,
    V_eqb v1 v2 = true <-> v1 = v2.

(* ********** *)

Check Bool.eqb.
(* eqb : bool -> bool -> bool *)

Definition bool_eqb (b1 b2 : bool) : bool :=
  match b1 with
  | true =>
    match b2 with
    | true =>
      true
    | false =>
      false
    end
  | false =>
    match b2 with
    | true =>
      false
    | false =>
      true
    end
  end.

Lemma bool_eqb_is_reflexive :
  forall b : bool,
    bool_eqb b b = true.
Proof.
  intros [ | ]; unfold bool_eqb; reflexivity.
Qed.

Search (eqb _ _ = _ -> _ = _).
(* eqb_prop: forall a b : bool, eqb a b = true -> a = b *)

Proposition soundness_and_completeness_of_bool_eqb :
  is_a_sound_and_complete_equality_predicate bool bool_eqb.
Proof.
  unfold is_a_sound_and_complete_equality_predicate.
  intros [ | ] [ | ].
  - split; unfold bool_eqb; intros _; reflexivity.
  - split.
    * intro H_absurd.
      unfold bool_eqb in H_absurd.
      discriminate H_absurd.
    * intro H_absurd.
      discriminate H_absurd.
  - split.
    * intro H_absurd.
      unfold bool_eqb in H_absurd.
      discriminate H_absurd.
    * intro H_absurd.
      discriminate H_absurd.
  - split; unfold bool_eqb; intros _; reflexivity.
Qed.    

(* ***** *)

Proposition soundness_and_completeness_of_Bool_eqb :
  is_a_sound_and_complete_equality_predicate bool eqb.
Proof.
  unfold is_a_sound_and_complete_equality_predicate.
  intros v1 v2.
  Search (eqb _ _ = _ <-> _ = _).
  exact (eqb_true_iff v1 v2).
Qed.
    
(* ********** *)

Check Nat.eqb.
(* Nat.eqb : nat -> nat -> bool *)

Fixpoint nat_eqb (n1 n2 : nat) : bool :=
  match n1 with
  | O =>
    match n2 with
    | O =>
      true
    | S n2' =>
      false
    end
  | S n1' =>
    match n2 with
    | O =>
      false
    | S n2' =>
      nat_eqb n1' n2'
    end
  end.

Lemma fold_unfold_nat_eqb_O :
  forall n2 : nat,
    nat_eqb 0 n2 =
    match n2 with
    | O =>
      true
    | S _ =>
      false
    end.
Proof.
  fold_unfold_tactic nat_eqb.
Qed.

Lemma fold_unfold_nat_eqb_S :
  forall n1' n2 : nat,
    nat_eqb (S n1') n2 =
    match n2 with
    | O =>
      false
    | S n2' =>
      nat_eqb n1' n2'
    end.
Proof.
  fold_unfold_tactic nat_eqb.
Qed.

Search (Nat.eqb _ _ = true -> _ = _).
(* beq_nat_true: forall n m : nat, (n =? m) = true -> n = m *)

Proposition soundness_and_completeness_of_nat_eqb :
  is_a_sound_and_complete_equality_predicate nat nat_eqb.
Proof.
  unfold is_a_sound_and_complete_equality_predicate.
  intros v1.
  induction v1 as [ | v1' IHv1'].
  - intros [ | v2'].
    * split; unfold nat_eqb; intros _; reflexivity.
    * rewrite -> (fold_unfold_nat_eqb_O (S v2')).
      split; intro H_absurd; discriminate H_absurd.
  - intros [ | v2'].
    * rewrite -> (fold_unfold_nat_eqb_S v1' 0).
      split; intro H_absurd; discriminate H_absurd.
    * rewrite -> (fold_unfold_nat_eqb_S v1' (S v2')).
      assert (IHv1' := IHv1' v2').
      destruct IHv1' as [H_nat_eqb_implies_equality H_v1_equals_v2_implies_nat_eqb].
      split.
      + intro H_nat_eqb.        
        rewrite -> (H_nat_eqb_implies_equality H_nat_eqb).
        reflexivity.
      + intro H_S_v1_equals_S_v2.
        Search (S _ = S _ -> _ = _).
        assert (H_v1_equals_v2 := eq_add_S v1' v2' H_S_v1_equals_S_v2).
        rewrite -> (H_v1_equals_v2_implies_nat_eqb H_v1_equals_v2).
        reflexivity.
Qed.
        
(* ***** *)

Lemma fold_unfold_Nat_eqb_O :
  forall n2 : nat,
    0 =? n2 =
    match n2 with
    | O =>
      true
    | S _ =>
      false
    end.
Proof.
  fold_unfold_tactic Nat.eqb.
Qed.

Lemma fold_unfold_Nat_eqb_S :
  forall n1' n2 : nat,
    S n1' =? n2 =
    match n2 with
    | O =>
      false
    | S n2' =>
      n1' =? n2'
    end.
Proof.
  fold_unfold_tactic Nat.eqb.
Qed.

Proposition soundness_and_completeness_of_Nat_eqb :
  is_a_sound_and_complete_equality_predicate nat Nat.eqb.
Proof.
  unfold is_a_sound_and_complete_equality_predicate.
  intros v1 v2.
  Search (Nat.eqb _ _ = true <-> _ = _).
  exact (Nat.eqb_eq v1 v2).
Qed.

(* ********** *)

Definition pair_eqb (V W : Type) (V_eqb : V -> V -> bool) (W_eqb : W -> W -> bool) (p1 p2 : V * W) : bool :=
  match p1 with
  | (v1, w1) =>
    match p2 with
    | (v2, w2) =>
      V_eqb v1 v2 && W_eqb w1 w2
    end
  end.

Proposition soundness_and_completeness_of_pair_eqb :
  forall (V W : Type)
         (V_eqb : V -> V -> bool)
         (W_eqb : W -> W -> bool),
    is_a_sound_and_complete_equality_predicate V V_eqb ->
    is_a_sound_and_complete_equality_predicate W W_eqb ->
    forall p1 p2 : V * W,
      pair_eqb V W V_eqb W_eqb p1 p2 = true <-> p1 = p2.
Proof.
  intros V W V_eqb W_eqb.
  unfold is_a_sound_and_complete_equality_predicate.
  intros H_soundness_and_completeness_of_V_eqb H_soundness_and_completeness_of_W_eqb.
  intros [v1 w1] [v2 w2].
  unfold pair_eqb.
  assert (H_soundness_and_completeness_of_V_eqb' := H_soundness_and_completeness_of_V_eqb v1 v2).
  assert (H_soundness_and_completeness_of_W_eqb' := H_soundness_and_completeness_of_W_eqb w1 w2).
  destruct H_soundness_and_completeness_of_V_eqb' as [H_V_eqb_implies_equality H_v1_equals_v2_implies_eqb].
  destruct H_soundness_and_completeness_of_W_eqb' as [H_W_eqb_implies_equality H_w1_equals_w2_implies_eqb].
  split.
  - Search (_ && _ = true).
    intros H_V_eqb_and_W_eqb.
    assert (H_V_eqb_and_W_eqb' := andb_prop (V_eqb v1 v2) (W_eqb w1 w2)  H_V_eqb_and_W_eqb).
    destruct H_V_eqb_and_W_eqb' as [H_V_eqb H_W_eqb].
    assert (H_v1_equals_v2 := H_V_eqb_implies_equality H_V_eqb).
    assert (H_w1_equals_w2 := H_W_eqb_implies_equality H_W_eqb).
    rewrite -> H_v1_equals_v2.
    rewrite -> H_w1_equals_w2.
    reflexivity.
  - intro H_equality_of_pair.
    injection H_equality_of_pair as H_v1_equals_v2 H_w1_equals_w2.
    assert (H_V_eqb := H_v1_equals_v2_implies_eqb H_v1_equals_v2).
    assert (H_W_eqb := H_w1_equals_w2_implies_eqb H_w1_equals_w2).
    Search (_ && _ = true).
    assert (H_V_eqb_and_W_eqb := conj H_V_eqb H_W_eqb).
    exact (andb_true_intro H_V_eqb_and_W_eqb).
Qed.    
  

(* ********** *)


Definition pair_nat_bool_eqb (p1 p2: nat * bool) : bool :=
  pair_eqb nat bool nat_eqb bool_eqb p1 p2.

Proposition soundness_and_completeness_of_pair_nat_bool_eqb :
  is_a_sound_and_complete_equality_predicate (nat * bool) pair_nat_bool_eqb.
Proof.
  unfold is_a_sound_and_complete_equality_predicate.
  Check (soundness_and_completeness_of_pair_eqb nat bool nat_eqb bool_eqb soundness_and_completeness_of_nat_eqb soundness_and_completeness_of_bool_eqb).
  exact (soundness_and_completeness_of_pair_eqb nat bool nat_eqb bool_eqb soundness_and_completeness_of_nat_eqb soundness_and_completeness_of_bool_eqb).
Qed.


(* ********** *)

(* Week 9 Exercise 2 *)

Inductive mm22 : Type :=
| MM22 : m22 -> m22 -> m22 -> m22 -> mm22.


(* Part a *)

Definition mm22_add (x y : mm22) : mm22 :=
  match x with
  | MM22 m22_x11 m22_x21
         m22_x12 m22_x22 =>
    match y with
    | MM22 m22_y11 m22_y21
           m22_y12 m22_y22 =>
      MM22 (m22_add m22_x11 m22_y11) (m22_add m22_x21 m22_y21)
           (m22_add m22_x12 m22_y12) (m22_add m22_x22 m22_y22)
    end
  end.


Definition mm22_mul (x y : mm22) : mm22 :=
  match x with
  | MM22 m22_x11 m22_x21
         m22_x12 m22_x22 =>
    match y with
    | MM22 m22_y11 m22_y21
           m22_y12 m22_y22 =>
      MM22 (m22_add (m22_mul m22_x11 m22_y11) (m22_mul m22_x12 m22_y21)) (m22_add (m22_mul m22_x11 m22_y12) (m22_mul m22_x12 m22_y22))
           (m22_add (m22_mul m22_x21 m22_y11) (m22_mul m22_x22 m22_y21)) (m22_add (m22_mul m22_x21 m22_y12) (m22_mul m22_x22 m22_y22))
    end
  end.

Definition mm22_one :=
  MM22 m22_one m22_one
       m22_one m22_one.

Fixpoint mm22_exp (x : mm22) (n : nat) : mm22 :=
  match n with
  | 0 =>
    mm22_one
  | S n' =>
    mm22_mul (mm22_exp x n') x
  end.

(* ********** *)

(* end of week-09_exercises.v *)
