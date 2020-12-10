(* week-10_how-to-phrase-logical-statements.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 24 Oct 2020 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Fixpoint length_v0_aux (V : Type) (vs : list V) : nat :=
  match vs with
    | nil =>
      0
    | v :: vs' =>
      S (length_v0_aux V vs')
  end.

Lemma fold_unfold_length_v0_aux_nil :
  forall V : Type,
    length_v0_aux V nil =
    0.
Proof.
  fold_unfold_tactic length_v0_aux.
Qed.

Lemma fold_unfold_length_v0_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    length_v0_aux V (v :: vs') =
    S (length_v0_aux V vs').
Proof.
  fold_unfold_tactic length_v0_aux.
Qed.

Definition length_v0 (V : Type) (vs : list V) : nat :=
  length_v0_aux V vs.

(* ********** *)

Fixpoint copy_v0_aux (V : Type) (vs : list V) : list V :=
  match vs with 
    | nil =>
      nil
    | v :: vs' =>
      v :: (copy_v0_aux V vs')
end.

Lemma fold_unfold_copy_v0_aux_nil :
  forall V : Type,
    copy_v0_aux V nil = nil.
Proof.
  fold_unfold_tactic copy_v0_aux.
Qed.

Lemma fold_unfold_copy_v0_aux_cons :
  forall (V : Type)
         (v : V)
         (vs : list V),
    copy_v0_aux V (v :: vs) =
    v :: (copy_v0_aux V vs).
Proof.
  fold_unfold_tactic copy_v0_aux.
Qed.

Definition copy_v0 (V : Type) (vs : list V) : list V :=
  copy_v0_aux V vs.

(* ********** *)

Lemma copy_v0_aux_preserves_length_v0_aux :
  forall (V : Type)
         (vs : list V),
    length_v0_aux V (copy_v0_aux V vs) = length_v0_aux V vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].

  - rewrite -> (fold_unfold_copy_v0_aux_nil V).
    reflexivity.

  - rewrite -> (fold_unfold_copy_v0_aux_cons V v vs').
    rewrite -> (fold_unfold_length_v0_aux_cons V v (copy_v0_aux V vs')).
    rewrite -> (fold_unfold_length_v0_aux_cons V v vs').
    apply (eq_S (length_v0_aux V (copy_v0_aux V vs')) (length_v0_aux V vs')).
    exact IHvs'.
Qed.

Theorem copy_v0_preserves_length_v0 :
  forall (V : Type)
         (vs : list V),
    length_v0 V (copy_v0 V vs) = length_v0 V vs.
Proof.
  unfold length_v0, copy_v0.
  exact copy_v0_aux_preserves_length_v0_aux.
Qed.

(* ********** *)

Lemma copy_v0_aux_preserves_length_v0_aux' :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0_aux V vs = n ->
    length_v0_aux V (copy_v0_aux V vs) = n.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs']; intro n.

  - rewrite -> (fold_unfold_copy_v0_aux_nil V).
    intro ly.
    exact ly. (* to be read aloud: "exactly", aha *)

  - rewrite -> (fold_unfold_length_v0_aux_cons V v vs').
    destruct n as [ | n'].

    -- intro H_absurd.
       discriminate H_absurd.

    -- intro H_vs'_n'.
       injection H_vs'_n' as H_vs'_n'.
       rewrite -> (fold_unfold_copy_v0_aux_cons V v vs').
       rewrite -> (fold_unfold_length_v0_aux_cons V v (copy_v0_aux V vs')).
       Search (_ = _ -> S _ = S _).
       apply eq_S.
       Check (IHvs' n').
       Check (IHvs' n' H_vs'_n').
       exact (IHvs' n' H_vs'_n').
Qed.

Theorem copy_v0_preserves_length_v0' :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 V (copy_v0 V vs) = n.
Proof.
  unfold length_v0, copy_v0.
  exact copy_v0_aux_preserves_length_v0_aux'.
Qed.

(* ********** *)

(* Question:
   are the two statements of
     Theorem copy_v0_preserves_length_v0
   and
     Theorem copy_v0_preserves_length_v0'
   equivalent? *)

(* ********** *)

(* Non-answers: *)

(*
Proposition equivalence_of_the_two_theorems :
  forall (V : Type)
         (vs : list V),
    copy_v0_preserves_length_v0 V vs
    <->
    copy_v0_preserves_length_v0' V vs.
*)

(*
Proposition equivalence_of_the_two_theorems_alt :
  copy_v0_preserves_length_v0 <-> copy_v0_preserves_length_v0'.
*)

(* ********** *)

(* Answers: *)

Proposition equivalence_of_the_two_theorems :
  forall (V : Type)
         (vs : list V),
    length_v0 V (copy_v0 V vs) = length_v0 V vs
    <->
    (forall n : nat,
        length_v0 V vs = n ->
        length_v0 V (copy_v0 V vs) = n).
Proof.
  (* brute force: *)
  intros V vs.
  split.
  - intros S n H_n.
    rewrite <- H_n.
    exact S.
  - intro S'.
    Check (S' (length_v0 V vs)).
    Check (eq_refl (length_v0 V vs)).
    exact (S' (length_v0 V vs) (eq_refl (length_v0 V vs))).

  Restart.

  (* symmetrically: *)
  intros V vs.
  split.
  - intros S n H_n.
    rewrite <- H_n.
    exact S.
  - intro S'.
    remember (length_v0 V vs) as n eqn:H_n.
    rewrite -> H_n in S'.
    symmetry in H_n.
    revert n H_n.
    exact S'.
Qed.

(* ********** *)

Proposition equivalence_of_the_two_theorems_alt :
  (forall (V : Type)
          (vs : list V),
      length_v0 V (copy_v0 V vs) = length_v0 V vs)
  <->
  (forall (V : Type)
          (vs : list V)
          (n : nat),
      length_v0 V vs = n ->
      length_v0 V (copy_v0 V vs) = n).
Proof.
  (* brute force: *)
  split.
  - intros S V vs n H_n.
    rewrite <- H_n.
    Check (S V vs).
    exact (S V vs).
  - intros S' V vs.
    Check (S' V vs (length_v0 V vs) (eq_refl (length_v0 V vs))).
    exact (S' V vs (length_v0 V vs) (eq_refl (length_v0 V vs))).

  Restart.

  (* symmetrically: *)
  split.
  - intros S V vs n H_n.
    rewrite <- H_n.
    clear n H_n.
    revert V vs.
    exact S.
  - intros S' V vs.
    remember (length_v0 V vs) as n eqn:H_n.
    symmetry in H_n.
    revert V vs n H_n.
    exact S'.
Qed.

(* ********** *)

(* end of week-10_how-to-phrase-logical-statements.v *)
