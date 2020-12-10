(* week-03_specifications.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 30 Aug 2020 *)

(* ********** *)

(* Paraphernalia: *)

Require Import Arith.

(* ********** *)

Definition recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = S (add x' y)).

Proposition there_is_at_most_one_recursive_addition :
  forall add1 add2 : nat -> nat -> nat,
    recursive_specification_of_addition add1 ->
    recursive_specification_of_addition add2 ->
    forall x y : nat,
      add1 x y = add2 x y.
Proof.
  intros add1 add2.
  unfold recursive_specification_of_addition.
  intros [H_add1_O H_add1_S] [H_add2_O H_add2_S].
  intro x.
  induction x as [ | x' IHx'].

  - intro y.
    rewrite -> (H_add2_O y).
    exact (H_add1_O y).

  - intro y.
    rewrite -> (H_add1_S x' y).
    rewrite -> (H_add2_S x' y).
    Check (IHx' y).
    rewrite -> (IHx' y).
    reflexivity.
Qed.

(* ********** *)

Definition tail_recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = add x' (S y)).

Proposition there_is_at_most_one_tail_recursive_addition :
  forall add1 add2 : nat -> nat -> nat,
    tail_recursive_specification_of_addition add1 ->
    tail_recursive_specification_of_addition add2 ->
    forall x y : nat,
      add1 x y = add2 x y.
Proof.
Abort.

(* ********** *)

Definition specification_of_the_predecessor_function (pred : nat -> nat) :=
  forall n : nat,
    pred (S n) = n.

Proposition there_is_at_most_one_predecessor_function :
  forall pred1 pred2 : nat -> nat,
    specification_of_the_predecessor_function pred1 ->
    specification_of_the_predecessor_function pred2 ->
    forall n : nat,
      pred1 n = pred2 n.
Proof.
  intros pred1 pred2.
  unfold specification_of_the_predecessor_function.
  intros H_pred1_S H_pred2_S.
  intro n.
  induction n as [ | n' IHn'].

  - 
Abort.

Definition make_predecessor_function (zero n : nat) :=
  match n with
  | 0 => zero
  | S n' => n'
  end.

Lemma about_make_predecessor_function :
  forall zero : nat,
    specification_of_the_predecessor_function (make_predecessor_function zero).
Proof.
  intro zero.
  unfold specification_of_the_predecessor_function.
  intros [ | n'].

  - unfold make_predecessor_function.
    reflexivity.

  - unfold make_predecessor_function.
    reflexivity.
Qed.  

Theorem there_are_at_least_two_predecessor_functions :
  exists pred1 pred2 : nat -> nat,
    specification_of_the_predecessor_function pred1 /\
    specification_of_the_predecessor_function pred2 /\
    exists n : nat,
      pred1 n <> pred2 n.
Proof.
  exists (make_predecessor_function 0).
  exists (make_predecessor_function 1).
  split.

  - exact (about_make_predecessor_function 0).

  - split.

    -- exact (about_make_predecessor_function 0).

    -- exists 0.
       unfold make_predecessor_function.
       Search (_ <> S _).
       Check (n_Sn 0).
       exact (n_Sn 0).
Qed.

(* ********** *)

Definition specification_of_the_total_predecessor_function (pred : nat -> option nat) :=
  (pred 0 = None)
  /\
  (forall n : nat,
      pred (S n) = Some n).

Proposition there_is_at_most_one_total_predecessor_function :
  forall pred1 pred2 : nat -> option nat,
    specification_of_the_total_predecessor_function pred1 ->
    specification_of_the_total_predecessor_function pred2 ->
    forall n : nat,
      pred1 n = pred2 n.
Proof.
  intros pred1 pred2.
  unfold specification_of_the_total_predecessor_function.
  intros [H_pred1_O H_pred1_S] [H_pred2_O H_pred2_S].
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> H_pred2_O.
    exact H_pred1_O.

  - rewrite -> (H_pred2_S n').
    exact (H_pred1_S n').

  Restart.

  intros pred1 pred2.
  unfold specification_of_the_total_predecessor_function.
  intros [H_pred1_O H_pred1_S] [H_pred2_O H_pred2_S].
  intros [ | n'].

  - rewrite -> H_pred2_O.
    exact H_pred1_O.

  - rewrite -> (H_pred2_S n').
    exact (H_pred1_S n').  
Qed.

(* ********** *)

Definition specification_of_the_predecessor_and_successor_function (ps : nat -> nat) :=
  (forall n : nat,
      ps (S n) = n)
  /\
  (forall n : nat,
      ps n = (S n)).

Theorem there_is_at_most_one_predecessor_and_successor_function :
  forall ps1 ps2 : nat -> nat,
    specification_of_the_predecessor_and_successor_function ps1 ->
    specification_of_the_predecessor_and_successor_function ps2 ->
    forall n : nat,
      ps1 n = ps2 n.
Proof.
Abort.

Lemma a_contradictory_aspect_of_the_predecessor_and_successor_function :
  forall ps : nat -> nat,
    specification_of_the_predecessor_and_successor_function ps ->
    ps 1 = 0 /\ ps 1 = 2.
Proof.
  intro ps.
  unfold specification_of_the_predecessor_and_successor_function.
  intros [H_ps_S H_ps].
  split.

  - rewrite -> (H_ps_S 0).
    reflexivity.

  - rewrite -> (H_ps 1).
    reflexivity.
Qed.

Theorem there_are_zero_predecessor_and_successor_functions :
  forall ps : nat -> nat,
    specification_of_the_predecessor_and_successor_function ps ->
    exists n : nat,
      ps n <> ps n.
Proof.
  intros ps S_ps.
  Check (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps).
  destruct (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps) as [H_ps_0 H_ps_2].
  exists 1.
  rewrite -> H_ps_0.

  Restart.

  intros ps S_ps.
  Check (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps).
  destruct (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps) as [H_ps_0 H_ps_2].
  exists 1.
  rewrite -> H_ps_0 at 1.
  rewrite -> H_ps_2.
  Search (0 <> S _).
  Check (O_S 1).
  exact (O_S 1).
Qed.

(* ********** *)

Theorem the_resident_addition_function_satisfies_the_recursive_specification_of_addition :
  recursive_specification_of_addition Nat.add.
Proof.
  unfold recursive_specification_of_addition.
  split.
  - intro y.
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  - intros x' y.
    Search (S _ + _ = S (_ + _)).
    exact (Nat.add_succ_l x' y).
Qed.

Theorem the_resident_addition_function_satisfies_the_tail_recursive_specification_of_addition :
  tail_recursive_specification_of_addition Nat.add.
Proof.
Abort.

(* ********** *)

Theorem the_two_specifications_of_addition_are_equivalent :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add <-> tail_recursive_specification_of_addition add.
Proof.
Abort.

(* ********** *)

Theorem associativity_of_recursive_addition_ :
  forall add : nat -> add -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 n3 : nat,
      add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
Abort.

(* ********** *)

Theorem commutativity_of_recursive_addition :
  forall add : nat -> add -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 : nat,
      add n1 n2 = add n2 n1.
Proof.
Abort.

(* ********** *)

Theorem O_is_left_neutral_for_recursive_addition :
  forall add : nat -> add -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add 0 n = n.
Proof.
Abort.

(* ********** *)

Theorem O_is_right_neutral_for_recursive_addition :
  forall add : nat -> add -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add n 0 = n.
Proof.
Abort.

(* ********** *)

(* end of week-03_specifications.v *)
