(* week-04_equational-reasoning-about-arithmetical-functions.v *)
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
Abort.

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

(* Tail-recursive implementation of the multiplication function, using add_v1 *)

(*
Definition mul_v21 (x y : nat) : nat :=
*)

(* ***** *)

(* Tail-recursive implementation of the multiplication function, using add_v2 *)

(*
Definition mul_v22 (x y : nat) : nat :=
*)

(* ********** *)

(* Equivalence of mul_v11, mul_v12, mul_v21, and mul_v22 *)

(* ***** *)

Theorem equivalence_of_mul_v11_and_mul_v12 :
  forall i j : nat,
    mul_v11 i j = mul_v12 i j.
Proof.
Abort.

(* ***** *)

(* ... *)

(* ***** *)

(* ... *)

(* ***** *)

(*
Theorem equivalence_of_mul_v21_and_mul_v22 :
  forall i j : nat,
    mul_v21 i j = mul_v22 i j.
Proof.
Abort.
*)

(* ********** *)

(* 0 is left absorbing with respect to multiplication *)

(* ***** *)

Property O_is_left_absorbing_wrt_mul_v11 :
  forall y : nat,
    mul_v11 0 y = 0.
Proof.
Abort.

(* ***** *)

Property O_is_left_absorbing_wrt_mul_v12 :
  forall y : nat,
    mul_v12 0 y = 0.
Proof.
Abort.

(* ***** *)

(*
Property O_is_left_absorbing_wrt_mul_v21 :
  forall y : nat,
    mul_v21 0 y = 0.
Proof.
Abort.
*)

(* ***** *)

(*
Property O_is_left_absorbing_wrt_mul_v22 :
  forall y : nat,
    mul_v22 0 y = 0.
Proof.
Abort.
*)

(* ********** *)

(* 1 is left neutral with respect to multiplication *)

(* ***** *)

Property SO_is_left_neutral_wrt_mul_v11 :
  forall y : nat,
    mul_v11 1 y = y.
Proof.
Abort.

(* ***** *)

Property SO_is_left_neutral_wrt_mul_v12 :
  forall y : nat,
    mul_v12 1 y = y.
Proof.
Abort.

(* ***** *)

(*
Property SO_is_left_neutral_wrt_mul_v21 :
  forall y : nat,
    mul_v21 1 y = y.
Proof.
Abort.
*)

(* ***** *)

(*
Property SO_is_left_neutral_wrt_mul_v22 :
  forall y : nat,
    mul_v22 1 y = y.
Proof.
Abort.
*)

(* ********** *)

(* 0 is right absorbing with respect to multiplication *)

(* ***** *)

Property O_is_right_absorbing_wrt_mul_v11 :
  forall x : nat,
    mul_v11 x 0 = 0.
Proof.
Abort.

(* ***** *)

Property O_is_right_absorbing_wrt_mul_v12 :
  forall x : nat,
    mul_v12 x 0 = 0.
Proof.
Abort.

(* ***** *)

(*
Property O_is_right_absorbing_wrt_mul_v21 :
  forall x : nat,
    mul_v21 x 0 = 0.
Proof.
Abort.
*)

(* ***** *)

(*
Property O_is_right_absorbing_wrt_mul_v22 :
  forall x : nat,
    mul_v22 x 0 = 0.
Proof.
Abort.
*)

(* ********** *)

(* 1 is right neutral with respect to multiplication *)

(* ***** *)

Property SO_is_right_neutral_wrt_mul_v11 :
  forall x : nat,
    mul_v11 x 1 = x.
Proof.
Abort.

(* ***** *)

Property SO_is_right_neutral_wrt_mul_v12 :
  forall x : nat,
    mul_v12 x 1 = x.
Proof.
Abort.

(* ***** *)

(*
Property SO_is_right_neutral_wrt_mul_v21 :
  forall x : nat,
    mul_v21 x 1 = x.
Proof.
Abort.
*)

(* ***** *)

(*
Property SO_is_right_neutral_wrt_mul_v22 :
  forall x : nat,
    mul_v22 x 1 = x.
Proof.
Abort.
*)

(* ********** *)

(* Multiplication is right-distributive over addition *)

(* ***** *)

(* ... *)

(* ********** *)

(* Multiplication is associative *)

(* ***** *)

Property mul_v11_is_associative :
  forall x y z : nat,
    mul_v11 x (mul_v11 y z) = mul_v11 (mul_v11 x y) z.
Proof.
Abort.

(* ***** *)

Property mul_v12_is_associative :
  forall x y z : nat,
    mul_v12 x (mul_v12 y z) = mul_v12 (mul_v12 x y) z.
Proof.
Abort.

(* ***** *)

(*
Property mul_v21_is_associative :
  forall x y z : nat,
    mul_v21 x (mul_v21 y z) = mul_v21 (mul_v21 x y) z.
Proof.
Abort.
*)

(* ***** *)

(*
Property mul_v22_is_associative :
  forall x y z : nat,
    mul_v22 x (mul_v22 y z) = mul_v22 (mul_v22 x y) z.
Proof.
Abort.
*)

(* ********** *)

(* Multiplication is left-distributive over addition *)

(* ***** *)

(* ... *)

(* ********** *)

(* end of week-04_equational-reasoning-about-arithmetical-functions.v *)
