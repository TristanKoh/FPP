(* week-05_mystery-functions.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 12 Sep 2020 *)

(* ********** *)

(* 
Your name:
Tristan Koh
Bernard Boey

Your student ID number:
A0191234L
A0191222R


Your e-mail address: 
bernard@u.yale-nus.edu.sg
tristan.koh@u.yale-nus.edu.sg
 
*)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* ********** *)

Definition specification_of_mystery_function_00 (mf : nat -> nat) :=
  mf 0 = 1 /\ forall i j : nat, mf (S (i + j)) = mf i + mf j.

(* ***** *)

Proposition there_is_at_most_one_mystery_function_00 :
  forall f g : nat -> nat,
    specification_of_mystery_function_00 f ->
    specification_of_mystery_function_00 g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.

(* ***** *)

Definition unit_test_for_mystery_function_00a (mf : nat -> nat) :=
  (mf 0 =n= 1) (* etc. *).

Definition unit_test_for_mystery_function_00b (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) (* etc. *).

Definition unit_test_for_mystery_function_00c (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) (* etc. *).

Definition unit_test_for_mystery_function_00d (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) && (mf 3 =n= 4)
  (* etc. *).

(* ***** *)

Definition mystery_function_00 := S.

Definition less_succinct_mystery_function_00 (n : nat) : nat :=
  S n.

Compute (unit_test_for_mystery_function_00d mystery_function_00).

Theorem there_is_at_least_one_mystery_function_00 :
  specification_of_mystery_function_00 mystery_function_00.
Proof.
  unfold specification_of_mystery_function_00, mystery_function_00.
  split.
  - reflexivity.
  - intros i j.
    rewrite -> (plus_Sn_m i (S j)).
    rewrite <- (plus_n_Sm i j).
    reflexivity.
Qed.

(* ***** *)

Definition mystery_function_00_alt := fun (n : nat) => n + 1.

Theorem there_is_at_least_one_mystery_function_00_alt :
  specification_of_mystery_function_00 mystery_function_00_alt.
Proof.
Abort.
  

(* ***** *)

Theorem soundness_of_the_unit_test_function_for_mystery_function_00 :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00c mf = true.
Proof.
  unfold specification_of_mystery_function_00.
  unfold unit_test_for_mystery_function_00c.
  intros mf [H_O H_S].
  (* Goal: (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> H_O.
  (* Goal: (1 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> (Nat.eqb_refl 1).
  (* Goal: true && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> (andb_true_l (mf 1 =n= 2)).
  (* Goal: (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  (* etc. *)
  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  rewrite -> (Nat.add_1_l 1).
  Check (Nat.eqb_refl 2).
  rewrite -> (Nat.eqb_refl 2).
  rewrite -> (andb_true_l (mf 2 =n= 3)).
  Check (Nat.add_1_l 1).
  rewrite <- (Nat.add_1_l 1) at 1.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  rewrite -> (H_S 0 1).
  rewrite -> H_O.
  rewrite <- (Nat.add_1_l 0) at 2.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  rewrite -> (Nat.add_1_l 1).
  rewrite -> (Nat.add_1_l 2).
  exact (Nat.eqb_refl 3).
Qed.

Theorem soundness_of_the_unit_test_function_for_mystery_function_00b :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00b mf = true.
Proof.
  unfold specification_of_mystery_function_00,
         unit_test_for_mystery_function_00b.
  intros mf [H_O H_S].
  (* Goal: (mf 0 =n= 1) && (mf 1 =n= 2) = true *)
  rewrite -> H_O.
  (* Goal: (1 =n= 1) && (mf 1 =n= 2) = true *)
  rewrite -> (Nat.eqb_refl 1).
  (* Goal: true && (mf 1 =n= 2) = true *)
  rewrite -> (andb_true_l (mf 1 =n= 2)).
  (* Goal: (mf 1 =n= 2) = true *)
  (* etc. *)
  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  Check (Nat.add_1_r 0).
  rewrite -> (Nat.add_1_r 0).
  Check (Nat.eqb_refl 2).
  exact (Nat.eqb_refl 2).
Qed.

Theorem soundness_of_the_unit_test_function_for_mystery_function_00_with_Search :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00b mf = true.
Proof.
  unfold specification_of_mystery_function_00,
         unit_test_for_mystery_function_00b.
  intros mf [H_O H_S].

  rewrite -> H_O.
  Search (beq_nat _  _ = true).
  Check (Nat.eqb_refl 1).
  rewrite -> (Nat.eqb_refl 1).
  Search (true && _ = _).
  Check (andb_true_l (mf 1 =n= 2)).
  rewrite -> (andb_true_l (mf 1 =n= 2)).

  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  Check (Nat.add_1_r 0).
  rewrite -> (Nat.add_1_r 0).
  Check (Nat.eqb_refl 2).
  exact (Nat.eqb_refl 2).
Qed.

(* ********** *)

Definition specification_of_mystery_function_11 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i j : nat,
    mf (i + j) = mf i + 2 * i * j + mf j.
  

Theorem there_is_at_most_one_mystery_function_11 :
  forall f g : nat -> nat,
    specification_of_mystery_function_11 f ->
    specification_of_mystery_function_11 g ->
    forall n : nat,
      f n = g n.
Proof.
  unfold specification_of_mystery_function_11.
  intros f g [H_f_O H_f_S] [H_g_O H_g_S] n.
  induction n as [ | n' IHn'].
  -
Abort.

Definition unit_test_for_mystery_function_11 (mf : nat -> nat) :=
  (mf 1 =n= 1)
  &&
  (mf 2 =n= 4)
  &&
  (mf 3 =n= 9).

Definition mystery_function_11 (n : nat) :=
  n * n.

Definition mystery_function_11_alt (n : nat) :=
  match n with
  | 0 => 1
  | _ => n * n
  end.

Compute (unit_test_for_mystery_function_11 mystery_function_11).

Compute (unit_test_for_mystery_function_11 mystery_function_11_alt).

Theorem there_are_at_least_two_mystery_functions_11 :
  exists f g : nat -> nat,
    specification_of_mystery_function_11 f /\
    specification_of_mystery_function_11 g /\
    exists n : nat,
      f n <> g n.
Proof.
  exists mystery_function_11, mystery_function_11_alt.
  split.
  - unfold specification_of_mystery_function_11, mystery_function_11.
    split.
    * Search (_ * 1 = _).
      exact (Nat.mul_1_r 1).
    * intros i j.
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
      Check (Nat.add_assoc).
      (* It associates left *)
      rewrite <- (Nat.add_assoc (i * i) (i * j) (i * j + j * j)).
      rewrite -> (Nat.add_assoc (i * j) (i * j) (j * j)).
      rewrite <- (Nat.add_assoc (i * i) (i * j + i * j) (j * j)).
      reflexivity.
  - split.
    * unfold specification_of_mystery_function_11, mystery_function_11_alt.
      split.
      ** Search (_ * 1 = _).
         exact (Nat.mul_1_r 1).
      ** intros i j.
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
         Check (Nat.add_assoc).
         (* It associates left *)
         rewrite <- (Nat.add_assoc (i * i) (i * j) (i * j + j * j)).
         rewrite -> (Nat.add_assoc (i * j) (i * j) (j * j)).
         rewrite <- (Nat.add_assoc (i * i) (i * j + i * j) (j * j)).
         
         

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

Definition unit_test_for_mystery_function_17 (mf : nat -> nat) :=
  (mf 0 =n= 0)
  &&
  (mf 1 =n= 1)
  &&
  (mf 2 =n= 1)
  &&
  (mf (S (0 + 0)) =n= (mf (S 0)) * (mf (S 0)) + mf 0 * mf 0)
  &&
  (mf (S (0 + 1)) =n= (mf (S 0)) * (mf (S 1)) + mf 0 * mf 1).

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
  assert ((f n) = (g n) /\ (f (S n)) = (g (S n))).
  induction n as [ | n' IHn'].
  - split.
    * rewrite -> H_f_0.
      rewrite -> H_g_0.
      reflexivity.
    * rewrite -> H_f_1.
      rewrite -> H_g_1.
      reflexivity.
  - split.
    * destruct IHn' as [H_fn' H_fSn'].
      rewrite -> H_fSn'.
      reflexivity.
    * destruct IHn' as [H_fn' H_fSn'].
      
Abort.

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
  (mf 0 + mf 3 =n= 2 * mf 2)
  &&
  (mf 1 + mf 4 =n= 2 * mf 3)
  &&
  (mf 2 + mf 5 =n= 2 * mf 4).


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

Definition specification_of_mystery_function_03 (mf : nat -> nat -> nat) :=
  mf 0 0 = 0
  /\
  (forall i j: nat, mf (S i) j = S (mf i j))
  /\
  (forall i j: nat, S (mf i j) = mf i (S j)).

(* ********** *)

Definition specification_of_mystery_function_42 (mf : nat -> nat) :=
  mf 1 = 42
  /\
  forall i j : nat,
    mf (i + j) = mf i + mf j.

(* ********** *)

Definition specification_of_mystery_function_07 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf 0 j = j)
  /\
  (forall i : nat, mf i 0 = i)
  /\
  (forall i j k : nat, mf (i + k) (j + k) = (mf i j) + k).

(* ********** *)

Definition specification_of_mystery_function_08 (mf : nat -> nat -> bool) :=
  (forall j : nat, mf 0 j = true)
  /\
  (forall i : nat, mf (S i) 0 = false)
  /\
  (forall i j : nat, mf (S i) (S j) = mf i j).

(* ********** *)

Definition specification_of_mystery_function_23 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 0
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

(* ********** *)

Definition specification_of_mystery_function_24 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

(* ********** *)

Definition specification_of_mystery_function_13 (mf : nat -> nat) :=
  (forall q : nat, mf (2 * q) = q)
  /\
  (forall q : nat, mf (S (2 * q)) = q).

(* ********** *)

Definition specification_of_mystery_function_25 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  (forall q : nat,
      mf (2 * (S q)) = S (mf (S q)))
  /\
  mf 1 = 0
  /\
  (forall q : nat,
      mf (S (2 * (S q))) = S (mf (S q))).

(* ****** *)

Definition specification_of_mystery_function_20 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = S (mf i j)).

(* ****** *)

Definition specification_of_mystery_function_21 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = mf i (S j)).

(* ****** *)

Definition specification_of_mystery_function_22 (mf : nat -> nat -> nat) :=
  forall i j : nat,
    mf O j = j
    /\
    mf (S i) j = mf i (S j).

(* ********** *)

(* Binary trees of natural numbers: *)

Inductive tree : Type :=
  | Leaf : nat -> tree
  | Node : tree -> tree -> tree.

Definition specification_of_mystery_function_19 (mf : tree -> tree) :=
  (forall n : nat,
     mf (Leaf n) = Leaf n)
  /\
  (forall (n : nat) (t : tree),
     mf (Node (Leaf n) t) = Node (Leaf n) (mf t))
  /\
  (forall t11 t12 t2 : tree,
     mf (Node (Node t11 t12) t2) = mf (Node t11 (Node t12 t2))).

(* You might not manage to prove
   that at most one function satisfies this specification (why?),
   but consider whether the following function does.
   Assuming it does, what does this function do?
   And what is the issue here?
*)

Fixpoint mystery_function_19_aux (t a : tree) : tree :=
  match t with
  | Leaf n =>
     Node (Leaf n) a
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19_aux t2 a)
  end.

Fixpoint mystery_function_19 (t : tree) : tree :=
  match t with
  | Leaf n =>
     Leaf n
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19 t2)
  end.

(* ********** *)

Definition specification_of_mystery_function_05 (mf : nat -> nat) :=
  mf 0 = 1
  /\
  forall i j : nat,
    mf (S (i + j)) = 2 * mf i * mf j.

(* ********** *)

Definition specification_of_mystery_function_06 (mf : nat -> nat) :=
  mf 0 = 2
  /\
  forall i j : nat,
    mf (S (i + j)) = mf i * mf j.

(* ********** *)

Definition specification_of_mystery_function_09 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = xorb (mf i) (mf j).

(* ********** *)

Definition specification_of_mystery_function_10 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = (mf i =b= mf j).

(* ********** *)

Definition specification_of_mystery_function_12 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i : nat,
    mf (S (S i)) = (S (S i)) * mf (S i).

(* ********** *)

Definition specification_of_mystery_function_14 (mf : nat -> bool) :=
  (forall q : nat, mf (2 * q) = true)
  /\
  (forall q : nat, mf (S (2 * q)) = false).

(* ********** *)

(* Simple examples of specifications: *)

(* ***** *)

Definition specification_of_the_factorial_function (fac : nat -> nat) :=
  fac 0 = 1
  /\
  forall n' : nat, fac (S n') = S n' * fac n'.

(* ***** *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib n'' + fib (S n'').

(* ********** *)

(* end of week-05_mystery-functions.v *)
