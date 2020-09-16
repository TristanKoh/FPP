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

(* Exercise 2 *)

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

Definition mul_v0_alt (i j : nat) : nat :=
  nat_fold_right nat 0 (fun ih => j + ih) i.

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


(* Exercise 3 *)

Definition specification_of_evenp (evenp : nat -> bool) :=
  (evenp O = true)
  /\
  (forall n' : nat,
      evenp (S n') = negb (evenp n')).

Proposition there_is_at_most_one_function_satisfying_the_specification_of_evenp :
  forall evenp1 evenp2 : nat -> bool,
    specification_of_evenp evenp1 ->
    specification_of_evenp evenp2 ->
    forall n : nat,
      evenp1 n = evenp2 n.
Proof.
  unfold specification_of_evenp.
  intros evenp1 evenp2 [S1_O S1_S] [S2_O S2_S] n.
  induction n as [ | n' IHn'].
  - rewrite -> (S2_O).
    exact S1_O.
  - rewrite -> (S1_S n').
    rewrite -> (S2_S n').
    rewrite -> IHn'.
    reflexivity.
Qed.

Fixpoint evenp_v0_aux (n : nat) : bool :=
  match n with
  | O => true
  | S n' => negb (evenp_v0_aux n')
  end.

Lemma fold_unfold_evenp_v0_aux_O :
  evenp_v0_aux O = true.
Proof.
  fold_unfold_tactic evenp_v0_aux.
Qed.

Lemma fold_unfold_evenp_v0_aux_S :
  forall n' : nat,
  evenp_v0_aux (S n') = negb (evenp_v0_aux n').
Proof.
  fold_unfold_tactic evenp_v0_aux.
Qed.

Definition evenp_v0 (n : nat) : bool :=
  evenp_v0_aux n.

Proposition evenp_v0_satisfies_the_specification_of_evenp :
  specification_of_evenp evenp_v0.
Proof.
  unfold specification_of_evenp, evenp_v0.
  split.
  - exact (fold_unfold_evenp_v0_aux_O).
  - intro n'.
    exact (fold_unfold_evenp_v0_aux_S n').
Qed.

Fixpoint evenp_v1_aux (n : nat) (a : bool) : bool :=
  match n with
  | O => a
  | S n' => evenp_v1_aux n' (negb a)
  end.

Lemma fold_unfold_evenp_v1_aux_O :
  forall a : bool,
  evenp_v1_aux O a = a.
Proof.
  fold_unfold_tactic evenp_v1_aux.
Qed.

Lemma fold_unfold_evenp_v1_aux_S :
  forall (n' : nat) (a : bool),
  evenp_v1_aux (S n') a = evenp_v1_aux n' (negb a).
Proof.
  fold_unfold_tactic evenp_v1_aux.
Qed.

Definition evenp_v1 (n : nat) : bool :=
  evenp_v1_aux n true.

Lemma about_evenp_v1 :
  forall (n' : nat) (a : bool),
    evenp_v1_aux n' (negb a) = negb (evenp_v1_aux n' a).
Proof.
  intro n'.
  induction n' as [ | n'' IHn''].
  - intro a.
    rewrite -> (fold_unfold_evenp_v1_aux_O a).
    exact (fold_unfold_evenp_v1_aux_O (negb a)).
  - intro a.
    rewrite -> (fold_unfold_evenp_v1_aux_S n'' a).
    rewrite -> (fold_unfold_evenp_v1_aux_S n'' (negb a)).
    exact (IHn'' (negb a)).
Qed.

Proposition evenp_v1_satisfies_the_specification_of_evenp :
  specification_of_evenp evenp_v1.
Proof.
  unfold specification_of_evenp, evenp_v1.
  split.
  - exact (fold_unfold_evenp_v1_aux_O true).
  - intro n'.
    rewrite -> (fold_unfold_evenp_v1_aux_S n' true).
    exact (about_evenp_v1 n' true).
Qed.

Proposition evenp_v0_and_evenp_v1_are_equivalent :
  forall n : nat,
    evenp_v0 n = evenp_v1 n.
Proof.
  intro n.
  unfold evenp_v0, evenp_v1.
  induction n as [ | n' IHn''].
  - rewrite -> (fold_unfold_evenp_v1_aux_O true).
    exact (fold_unfold_evenp_v0_aux_O).
  - rewrite -> (fold_unfold_evenp_v0_aux_S n').
    rewrite -> (fold_unfold_evenp_v1_aux_S n' true).
    rewrite -> IHn''.
    symmetry.
    exact (about_evenp_v1 n' true).
Qed.

Definition evenp_v0_alt (n : nat) : bool :=
  nat_fold_right bool true negb n.

Proposition evenp_v0_alt_satisfies_the_specification_of_evenp :
  specification_of_evenp evenp_v0_alt.
Proof.
  unfold specification_of_evenp, evenp_v0_alt.
  split.
  - exact (fold_unfold_nat_fold_right_O bool true negb).
  - intro n'.
    exact (fold_unfold_nat_fold_right_S bool true negb n').
Qed.

Proposition evenp_v0_and_evenp_v0_alt_are_equivalent :
  forall n : nat,
    evenp_v0 n = evenp_v0_alt n.
Proof.
  intro n.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_evenp
           evenp_v0
           evenp_v0_alt
           evenp_v0_satisfies_the_specification_of_evenp
           evenp_v0_alt_satisfies_the_specification_of_evenp
           n).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_evenp
           evenp_v0
           evenp_v0_alt
           evenp_v0_satisfies_the_specification_of_evenp
           evenp_v0_alt_satisfies_the_specification_of_evenp
           n).
Qed.
  
Definition evenp_v1_alt (n : nat) : bool :=
  nat_fold_left bool true negb n.


Proposition evenp_v1_alt_satisfies_the_specification_of_evenp :
  specification_of_evenp evenp_v1_alt.
Proof.
  unfold specification_of_evenp, evenp_v1_alt.
  split.
  - exact (fold_unfold_nat_fold_left_O bool true negb).
  - intro n'.
    rewrite -> (fold_unfold_nat_fold_left_S bool true negb n').
    rewrite -> (about_nat_fold_left bool true negb n').
    reflexivity.
Qed.

Proposition evenp_v1_and_evenp_v1_alt_are_equivalent :
  forall n : nat,
    evenp_v1 n = evenp_v1_alt n.
Proof.
  intro n.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_evenp
           evenp_v1
           evenp_v1_alt
           evenp_v1_satisfies_the_specification_of_evenp
           evenp_v1_alt_satisfies_the_specification_of_evenp
           n).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_evenp
           evenp_v1
           evenp_v1_alt
           evenp_v1_satisfies_the_specification_of_evenp
           evenp_v1_alt_satisfies_the_specification_of_evenp
           n).
Qed.

Corollary evenp_v0_and_evep_v1_are_equivalent_alt :
  forall n : nat,
    evenp_v0 n = evenp_v1 n.
Proof.
  intro n.
  rewrite -> (evenp_v0_and_evenp_v0_alt_are_equivalent).
  rewrite -> (evenp_v1_and_evenp_v1_alt_are_equivalent).
  unfold evenp_v0_alt, evenp_v1_alt.
  rewrite -> (folding_left_and_right bool true negb n).
  reflexivity.
Qed.


(* Mystery Functions *)

(* Paraphernalia: *)


Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* ********** *)

Definition specification_of_mystery_function_11 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i j : nat,
    mf (i + j) = mf i + 2 * i * j + mf j.

Definition unit_test_for_mystery_function_11 (mf : nat -> nat) :=
  (mf 1 =n= 1)
  &&
  (mf 2 =n= 4)
  &&
  (mf 3 =n= 9).

Definition mystery_function_11 (n : nat) :=
  n * n.

Fixpoint mystery_function_11_v2_alt (n : nat) :=
  match n with
  | 0 => 1
  | S _ => n * n
  end.

Definition mystery_function_11_v2 (n : nat) :=
  mystery_function_11_v2_alt n.

Lemma fold_unfold_mystery_function_11_v2_alt_O :
    mystery_function_11_v2_alt 1 = 1.
Proof.
  fold_unfold_tactic mystery_function_11_v2_alt.
Qed.


Lemma fold_unfold_mystery_function_11_v2_alt_S :
  forall n' : nat,
    let n := (S n') in
    mystery_function_11_v2_alt (S n') = n * n.
Proof.
  fold_unfold_tactic mystery_function_11_v2_alt.
Qed.


Compute (unit_test_for_mystery_function_11 mystery_function_11).

Compute (unit_test_for_mystery_function_11 mystery_function_11_v2).

Theorem there_is_at_least_one_mystery_function_11 :
  specification_of_mystery_function_11 mystery_function_11.
Proof.
  unfold specification_of_mystery_function_11, mystery_function_11.
  split.
  - Search (_ * _ = _).
    exact (Nat.mul_1_r 1).
  - intros i j.
    Search ((_ + _) * _ = _*_ + _*_).
    Check (Nat.mul_add_distr_r).
    rewrite -> (Nat.mul_add_distr_r i j (i + j)).
    Search ( _ * (_ + _) = _ * _ + _ * _).
    rewrite -> (Nat.mul_add_distr_l i i j).
    rewrite -> (Nat.mul_add_distr_l j i j).
    Search (S _ = _ + 1).
    rewrite -> (BinInt.ZL0). 
    Check (Nat.mul_add_distr_r).
    rewrite -> (Nat.mul_add_distr_r 1 1 i).
    Search (1 * _ = _).
    Check (Nat.mul_1_l i).
    rewrite -> (Nat.mul_1_l i).
    Check (Nat.mul_add_distr_r i i j).
    rewrite -> (Nat.mul_add_distr_r i i j).
    Search (_ + (_ + _) = (_ + _) + _).
    Check (Nat.mul_comm j i).
    rewrite -> (Nat.mul_comm j i).
    (* Since we have three expressions with addition, we need to check whether addition associates to the left or right *)
    Check (Nat.add_assoc).
    (* It associates left *)
    rewrite <- (Nat.add_assoc (i * i) (i * j) (i * j + j * j)).
    rewrite -> (Nat.add_assoc (i * j) (i * j) (j * j)).
    rewrite <- (Nat.add_assoc (i * i) (i * j + i * j) (j * j)).
    reflexivity.
Qed.


(* ********** *)

Definition specification_of_mystery_function_04 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  forall n' : nat,
    mf (S n') = mf n' + S (2 * n').


Theorem there_is_at_most_one_mystery_function_04 :
  forall f g : nat -> nat,
    specification_of_mystery_function_04 f ->
    specification_of_mystery_function_04 g ->
    forall n : nat,
      f n = g n.
Proof.
  unfold specification_of_mystery_function_04.
  intros f g [H_f_O H_f_S] [H_g_O H_g_S] n.
  induction n as [ | n' IHn'].
  - rewrite -> H_f_O.
    rewrite -> H_g_O.
    reflexivity.
  - rewrite -> (H_f_S n').
    rewrite -> (H_g_S n').
    rewrite -> IHn'.
    reflexivity.
Qed.

Definition unit_test_for_mystery_function_04 (mf : nat -> nat) :=
  let b0 := (mf 0 =n= 0) in
  let b1 := (mf 1 =n= 1) in
  let b2 := (mf 2 =n= 4) in
  let b3 := (mf 3 =n= 9) in
  let b4 := (mf 4 =n= 16) in
  let b5 := (mf 5 =n= 25) in
  b0 && b1 && b2 && b3 && b4 && b5.

Definition mystery_function_04 := fun (n : nat) => n * n.

Compute unit_test_for_mystery_function_04 mystery_function_04.

Theorem there_is_at_least_one_mystery_function_04 :
  specification_of_mystery_function_04 mystery_function_04.
Proof.
  unfold specification_of_mystery_function_04, mystery_function_04.
  split.
  - Search (_ * 0 = 0).
    rewrite -> (Nat.mul_0_r 0).
    reflexivity.
  - intros n'.
    Search (S _ * _ = _ * _ + _).
    rewrite -> (Nat.mul_succ_l n' (S n')).
    rewrite -> (Nat.mul_succ_r n' n').
    Search (_ + _).
    rewrite -> (Nat.add_succ_r (n' * n' + n') n').
    Search (S _ * _).
    rewrite -> (Nat.mul_succ_l 1 n').
    Search (1 * _).
    rewrite -> (Nat.mul_1_l n').
    Search (_ + S _).
    rewrite -> (Nat.add_succ_r (n' * n') (n' + n')).
    Search (_ + (_ + _)).
    rewrite -> (Nat.add_assoc (n' * n') n' n').
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_mystery_function_15 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (S x, y * S x).


Theorem there_is_at_most_one_mystery_function_15 :
  forall f g : nat -> nat * nat,
    specification_of_mystery_function_15 f ->
    specification_of_mystery_function_15 g ->
    forall n : nat,
      f n = g n.
Proof.
  unfold specification_of_mystery_function_15.
  intros f g [H_f_O H_f_S] [H_g_O H_g_S] n.
  induction n as [ | n' IHn'].
  - rewrite -> H_f_O.
    rewrite -> H_g_O.
    reflexivity.
  - rewrite -> (H_f_S n').
    rewrite -> (H_g_S n').
    rewrite -> IHn'.
    reflexivity.
Qed.

Definition beq_pair (V1 : Type) (eqb_V1 : V1 -> V1 -> bool) (V2 : Type) (eqb_V2 : V2 -> V2 -> bool) (p1 p2 : V1 * V2) : bool :=
  let (v11, v12) := p1 in
  let (v21, v22) := p2 in
  eqb_V1 v11 v21 && eqb_V2 v12 v22.

Definition beq_pair_nat_nat (p1 p2 : (nat * nat)) : bool :=
  beq_pair nat beq_nat nat beq_nat p1 p2.

Notation "A =pnn= B" :=
  (beq_pair_nat_nat A B) (at level 70, right associativity).


Definition unit_test_for_mystery_function_15 (mf : nat -> nat * nat) :=
  ((mf 0) =pnn= (0, 1)) &&
  ((mf 1) =pnn= (1, 1)) &&
  ((mf 2) =pnn= (2, 2)) &&
  ((mf 3) =pnn= (3, 6)) &&
  ((mf 4) =pnn= (4, 24)) &&
  ((mf 5) =pnn= (5, 120)).


Fixpoint fac (n : nat) : nat :=
  match n with
  | 0 =>  1
  | S n' => n * fac n'
  end.

Definition mystery_function_15 (n : nat) : nat * nat :=
  (n, fac n).

Compute (unit_test_for_mystery_function_15 mystery_function_15).

Lemma fold_unfold_fac_O:
  fac 0 = 1.
Proof.
  fold_unfold_tactic fac.
Qed.

Lemma fold_unfold_fac_S:
  forall n': nat,
    fac (S n') = (S n') * fac n'.
Proof.
  fold_unfold_tactic fac.
Qed.

Theorem there_is_at_least_one_mystery_function_15 :
  specification_of_mystery_function_15 mystery_function_15.
Proof.
  unfold specification_of_mystery_function_15, mystery_function_15.
  split.
  - rewrite -> fold_unfold_fac_O.
    reflexivity.
  - intro n'.
    rewrite -> fold_unfold_fac_S.
    rewrite -> (Nat.mul_comm (S n') (fac n')).
    reflexivity.
Qed.



(* ********** *)

Definition specification_of_mystery_function_16 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (y, x + y).

Theorem there_is_at_most_one_mystery_function_16 :
  forall f g : nat -> (nat * nat),
    specification_of_mystery_function_16 f ->
    specification_of_mystery_function_16 g ->
    forall n : nat,
      f n = g n.
Proof.
  unfold specification_of_mystery_function_16.
  intros f g [H_f_O H_f_S] [H_g_O H_g_S] n.
  induction n as [ | n' IHn'].
  - rewrite -> (H_f_O).
    rewrite -> (H_g_O).
    reflexivity.
  - rewrite -> (H_f_S n').
    rewrite -> (H_g_S n').
    rewrite -> IHn'.
    reflexivity.
Qed.
    
Definition unit_test_for_mystery_function_16 (mf : nat -> nat * nat) :=
  (mf 0 =pnn= (0, 1))
  &&
  (mf 1 =pnn= (1, 1))
  &&
  (mf 2 =pnn= (1, 2))
  &&
  (mf 3 =pnn= (2, 3)).


Fixpoint mystery_function_16_aux (n : nat) : (nat * nat) :=
  match n with
  | 0 => (0 , 1)
  | S n' =>
    let (fib_n' , fib_n) := (mystery_function_16_aux n')
    in (fib_n, fib_n' + fib_n)
  end.

Definition mystery_function_16 (n : nat) :=
  mystery_function_16_aux n.

Compute (unit_test_for_mystery_function_16 mystery_function_16).

Lemma fold_unfold_mystery_function_16_aux_O :
    mystery_function_16_aux O =
    (0 , 1).
Proof.
  fold_unfold_tactic mystery_function_16_aux.
Qed.

Lemma fold_unfold_mystery_function_16_aux_S :
  forall n' : nat,
    mystery_function_16_aux (S n') =
    let (fib_n', fib_n) := (mystery_function_16_aux n')
    in (fib_n, fib_n' + fib_n).
Proof.
  fold_unfold_tactic mystery_function_16_aux.
Qed.  

Theorem there_is_at_least_one_mystery_function_16 :
  specification_of_mystery_function_16 mystery_function_16.
Proof.
  unfold specification_of_mystery_function_16, mystery_function_16.
  - split.
    -- rewrite -> fold_unfold_mystery_function_16_aux_O.
       reflexivity.
    -- intro n'.
       Check (fold_unfold_mystery_function_16_aux_S).
       rewrite -> (fold_unfold_mystery_function_16_aux_S n').
       reflexivity.
Qed.       
       

(* ********** *)

Definition specification_of_mystery_function_17 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall p q : nat,
    mf (S (p + q)) = mf (S p) * mf (S q) + mf p * mf q.


Theorem there_is_at_most_one_mystery_function_17 :
  forall f g : nat -> nat,
    specification_of_mystery_function_17 f ->
    specification_of_mystery_function_17 g ->
    forall n : nat,
      f n = g n.
Proof.
  unfold specification_of_mystery_function_17.
  intros f g [H_f_0 H_f_S] [H_g_0 H_g_S] n.
  destruct H_f_S as [H_f_1 H_f_S].
  destruct H_f_S as [H_f_2 H_f_S].
  destruct H_g_S as [H_g_1 H_g_S].
  destruct H_g_S as [H_g_2 H_g_S].
  assert (IHn'_and_IHSn' : (f n) = (g n) /\ (f (S n)) = (g (S n))).
  induction n as [ | n' IHn'].
  - split.
    * rewrite -> H_f_0.
      rewrite -> H_g_0.
      reflexivity.
    * rewrite -> H_f_1.
      rewrite -> H_g_1.
      reflexivity.
  - destruct IHn' as [IHn' IHSn'].
    split.
    * exact IHSn'.
    * rewrite <- (Nat.add_0_r (S n')).
      rewrite -> (Nat.add_succ_comm n' 0).
      rewrite -> (H_f_S n' 1).
      rewrite -> (H_g_S n' 1).
      rewrite -> H_f_1.
      rewrite -> H_g_1.
      rewrite -> H_f_2.
      rewrite -> H_g_2.
      rewrite -> (IHn').
      rewrite -> (IHSn').
      reflexivity.
  - destruct IHn'_and_IHSn' as [IHn' IHSn'].
    exact IHn'.
Qed.

Definition unit_test_for_mystery_function_17 (mf : nat -> nat) :=
  (mf 0 =n= 0)
  &&
  (mf 1 =n= 1)
  &&
  (mf 2 =n= 1)
  &&
  (mf 3 =n= 2)
  &&
  (mf 4 =n= 3)
  &&
  (mf 5 =n= 5)
  &&
  (mf 6 =n= 8).


Fixpoint mystery_function_17_aux (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' =>
      mystery_function_17_aux n' + mystery_function_17_aux n''
    end
  end.

Definition mystery_function_17 (n : nat) : nat :=
  mystery_function_17_aux n.

Compute (unit_test_for_mystery_function_17 mystery_function_17).

Lemma fold_unfold_mystery_function_17_aux_O :
    mystery_function_17_aux O =
    0.
Proof.
  fold_unfold_tactic mystery_function_17_aux.
Qed.

Lemma fold_unfold_mystery_function_17_aux_1 :
    mystery_function_17_aux 1 =
    1.
Proof.
  fold_unfold_tactic mystery_function_17_aux.
Qed.

Lemma fold_unfold_mystery_function_17_aux_S :
  forall n'' : nat,
    mystery_function_17_aux (S (S n'')) =  mystery_function_17_aux (S n'') + mystery_function_17_aux n''.
Proof.
  fold_unfold_tactic mystery_function_17_aux.
Qed.


Theorem there_is_at_least_one_mystery_functions_17 :
  specification_of_mystery_function_17 mystery_function_17.
Proof.
  unfold specification_of_mystery_function_17, mystery_function_17.
  split.
  - rewrite -> (fold_unfold_mystery_function_17_aux_O).
    reflexivity.
  - split.
    -- Check (fold_unfold_mystery_function_17_aux_1).
       rewrite -> (fold_unfold_mystery_function_17_aux_1).
       reflexivity.
    -- split.
       --- rewrite -> (fold_unfold_mystery_function_17_aux_S 0).
           rewrite -> (fold_unfold_mystery_function_17_aux_O).
           rewrite -> (fold_unfold_mystery_function_17_aux_1).
           Search (_ + 0 = _).
           exact (Nat.add_0_r 1).
    --- intro p.
        induction p as [ | p' IHp'].
        ---- intro q.
             rewrite -> (Nat.add_0_l q).
             rewrite -> (fold_unfold_mystery_function_17_aux_O).
             rewrite -> (fold_unfold_mystery_function_17_aux_1).
             Search (0 * _ = _).
             rewrite -> (Nat.mul_0_l (mystery_function_17_aux q)).
             Search (1 * _ = _).
             rewrite -> (Nat.mul_1_l (mystery_function_17_aux (S q))).
             Search (_ + 0 = _).
             rewrite -> (Nat.add_0_r (mystery_function_17_aux (S q))).
             reflexivity.
        ---- intro q.
             Search ( _  = S _).
             rewrite <- (Nat.add_succ_r (S p') (q)).
             Check (Nat.add_succ_l).
             rewrite -> (Nat.add_succ_l (p') (S q)).
             rewrite -> (IHp' (S q)).
             Check (fold_unfold_mystery_function_17_aux_S p').
             rewrite -> (fold_unfold_mystery_function_17_aux_S p').
             rewrite -> (fold_unfold_mystery_function_17_aux_S q).
             Search (_ * ( _ + _)).
             rewrite -> (Nat.mul_add_distr_l
                           (mystery_function_17_aux (S p'))
                           (mystery_function_17_aux (S q))
                           (mystery_function_17_aux q)).
             Check (Nat.mul_add_distr_r).
             rewrite -> (Nat.mul_add_distr_r
                           (mystery_function_17_aux (S p'))
                           (mystery_function_17_aux p')
                           (mystery_function_17_aux (S q))).
             Search (_ + _ + _).
             rewrite -> (Nat.add_shuffle0
                           ((mystery_function_17_aux (S p')) *
                            (mystery_function_17_aux (S q)))
                           ((mystery_function_17_aux (S p') *
                             (mystery_function_17_aux q)))
                           ((mystery_function_17_aux p') *
                            (mystery_function_17_aux (S q)))).
             reflexivity.
Qed.


                         
(* ********** *)

Definition specification_of_mystery_function_18 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall n''' : nat,
    mf n''' + mf (S (S (S n'''))) = 2 * mf (S (S n''')).

Definition unit_test_for_mystery_function_18 (mf : nat -> nat) :=
  (mf 0 =n= 0)
  &&
  (mf 1 =n= 1)
  &&
  (mf 2 =n= 1)
  &&
  (mf 3 =n= 2)
  &&
  (mf 4 =n= 3)
  &&
  (mf 5 =n= 5)
  &&
  (mf 6 =n= 8).


Fixpoint mystery_function_18_aux (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' =>
      mystery_function_18_aux n' + mystery_function_18_aux n''
    end
  end.

Definition mystery_function_18 (n : nat) : nat :=
  mystery_function_18_aux n.
  
Compute (unit_test_for_mystery_function_18 mystery_function_18).

Lemma fold_unfold_mystery_function_18_aux_O :
    mystery_function_18_aux O =
    0.
Proof.
  fold_unfold_tactic mystery_function_18_aux.
Qed.

Lemma fold_unfold_mystery_function_18_aux_S :
  forall n' : nat,
    mystery_function_18_aux (S n') =
    match n' with
    | 0 => 1
    | S n'' => mystery_function_18_aux n' + mystery_function_18_aux n''
    end.
Proof.
  fold_unfold_tactic mystery_function_18_aux.
Qed.

Theorem there_is_at_least_one_mystery_function_18 :
  specification_of_mystery_function_18 mystery_function_18.
Proof.
  unfold specification_of_mystery_function_18, mystery_function_18.
  - split.
    -- rewrite -> fold_unfold_mystery_function_18_aux_O.
       reflexivity.
    -- split.
       --- Check (fold_unfold_mystery_function_18_aux_S 0).
           exact (fold_unfold_mystery_function_18_aux_S 0).
       --- split.
           ---- Check (fold_unfold_mystery_function_18_aux_S 1).
                rewrite -> (fold_unfold_mystery_function_18_aux_S 1).
                rewrite -> (fold_unfold_mystery_function_18_aux_O).
                rewrite -> (fold_unfold_mystery_function_18_aux_S 0).
                Search (_ + 0 = _).
                exact (Nat.add_0_r 1).
           ---- intro n'''.
                Check (fold_unfold_mystery_function_18_aux_S (S (S n'''))).
                rewrite -> (fold_unfold_mystery_function_18_aux_S (S (S n'''))).
                Search (_ + _ = _ + _).
                Check (Nat.add_comm).
                rewrite -> (Nat.add_comm
                              (mystery_function_18_aux n''')
                              (mystery_function_18_aux (S (S n''')) +
                               mystery_function_18_aux (S n'''))).                                   rewrite <- (Nat.add_assoc
                                                                                                                   (mystery_function_18_aux (S (S n''')))
                                                                                                                   (mystery_function_18_aux (S n'''))
                                                                                                                   (mystery_function_18_aux n''')).            
                rewrite <- (fold_unfold_mystery_function_18_aux_S (S n''')).
                Search (1 + 1).
                rewrite -> (BinInt.ZL0).
                Search ( (_ + _) * _).
                rewrite -> (Nat.mul_add_distr_r 1 1 (mystery_function_18_aux (S (S n''')))).
                Search (1 * _ = _).
                rewrite -> (Nat.mul_1_l (mystery_function_18_aux (S (S n''')))).
                reflexivity.
Qed.
                

                
(* ********** *)

Definition specification_of_mystery_function_42 (mf : nat -> nat) :=
  mf 1 = 42
  /\
  forall i j : nat,
    mf (i + j) = mf i + mf j.


Definition mystery_function_42_v1 (n : nat) : nat := 42 * n.
Definition mystery_function_42_v2 (n : nat) : nat := 42 + (42 * (n - 1)).

Theorem there_is_at_least_one_mystery_function_42 :
  specification_of_mystery_function_42 mystery_function_42_v1.
Proof.
  unfold specification_of_mystery_function_42, mystery_function_42_v1.
  split.
  - exact (Nat.mul_1_r 42).
  - intros i j.
    Search (_ * (_ + _)).
    exact (Nat.mul_add_distr_l 42 i j).
Qed.

Theorem there_is_another_mystery_function_42 :
  specification_of_mystery_function_42 mystery_function_42_v2.
Proof.
  unfold specification_of_mystery_function_42, mystery_function_42_v2.
  split.
  - Search (_ - _ = _).
    rewrite -> (Nat.sub_diag 1).
    rewrite -> (Nat.mul_0_r 42).
    exact (Nat.add_0_r 42).
  - intros i j.
    Search (_ * (_  - _)).
    rewrite -> (Nat.mul_sub_distr_l (i + j) 1 42).
    rewrite -> (Nat.mul_1_r 42).
    rewrite -> (Nat.mul_add_distr_l 42 i j).
    Search (_ + (_ - _)).
    rewrite -> (Nat.add_sub_assoc 42 (42 * i + 42 * j) 42).
    Search (_ + _ - _).
    rewrite -> (minus_plus 42 (42 * i + 42 * j)).

    rewrite -> (Nat.mul_sub_distr_l i 1 42).
    rewrite -> (Nat.mul_1_r 42).
    rewrite -> (Nat.add_sub_assoc 42 (42 * i) 42).
    rewrite -> (minus_plus 42 (42 * i)).
     
    rewrite -> (Nat.mul_sub_distr_l j 1 42).
    rewrite -> (Nat.mul_1_r 42).
    rewrite -> (Nat.add_sub_assoc 42 (42 * j) 42).
    rewrite -> (minus_plus 42 (42 * j)).
    reflexivity.

    * Abort.
Qed.


(* ********** *)

Definition specification_of_mystery_function_10 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = (mf i =b= mf j).


Lemma negb_true_is_false :
  negb true = false.
Proof.
  reflexivity.
Qed.

Theorem there_are_zero_mystery_functions_10 :
  forall mf : nat -> bool,
    specification_of_mystery_function_10 mf ->
    exists x : nat,
      mf x <> mf x.
Proof.
  intro mf.
  unfold specification_of_mystery_function_10.
  intros [H_S_0 H_S_S].
  destruct H_S_S as [H_S_1 H_S_S].
  exists 2.
  rewrite <- (Nat.add_0_r 2) at 2.
  rewrite -> (H_S_S 2 0).
  rewrite <- (Nat.add_0_r 2).
  Search (_ = _ + _).
  rewrite -> (Nat.add_succ_comm 1 0).
  rewrite -> (H_S_S 1 1).
  rewrite -> H_S_0.
  rewrite -> H_S_1.
  Search (_ =b= _).
  rewrite -> (eqb_reflx true).
  rewrite <- (negb_true_is_false).
  rewrite -> (eqb_negb2 true).
  exact diff_true_false.
Qed.


(* ********** *)

(* end of week-05_exercises.v *)
