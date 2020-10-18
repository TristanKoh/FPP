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
      M22 ((x11 * y11) + (x12 * y21)) ((x11 * y12) + (x12 + y22))
          ((x21 * y11) + (x22 + y21)) ((x21 * y12) + (x22 + y22))
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
Abort.


(* Part c: Proposition 12 - Identity matrix is left and right neutral *)

Proposition proposition_12 :
  forall m22_1 : m22,
    m22_mul m22_one m22_1 = m22_mul m22_1 m22_one.
Proof.
Abort.



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
Abort.



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
Abort.


(* Part l - Proposition 38, Transposition and exponentiation commute with each other *)


Proposition proposition_38 :
  forall (x : m22)
         (n : nat),
    m22_transpose (m22_exp x n) = m22_exp (m22_transpose x) n.
Proof.
Abort.


(* Part m - Exericse 40*)

  



(* Exercise 2 *)

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


(* Part b *)




(* ********** *)

(* end of week-09_exercises.v *)
