(* week-10_induction-principles-continued.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 24 Oct 2020 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  assert (H_both : P n /\ P (S n)).
  { induction n as [ | n' [IHn' IHSn']].

    - Check (conj H_P0 H_P1).
      exact (conj H_P0 H_P1).

    - Check (H_PSS n' IHn' IHSn').
      Check (conj IHSn' (H_PSS n' IHn' IHSn')).
      exact (conj IHSn' (H_PSS n' IHn' IHSn')).
  } 
  destruct H_both as [ly _].
  exact ly.
Qed.

(* ********** *)

Fixpoint evenp1 (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | S n' =>
    negb (evenp1 n')
  end.

Lemma fold_unfold_evenp1_O :
  evenp1 0 =
  true.
Proof.
  fold_unfold_tactic evenp1.
Qed.

Lemma fold_unfold_evenp1_S :
  forall n' : nat,
    evenp1 (S n') =
    negb (evenp1 n').
Proof.
  fold_unfold_tactic evenp1.
Qed.

(* The evenness predicate is often programmed tail-recursively
   and with no accumulator, by peeling two layers of S at a time.
   Its equivalence with evenp1 messy to prove by mathematical induction
   but effortless using nat_ind2:
*)

Fixpoint evenp2 (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | S n' =>
    match n' with
    | 0 =>
      false
    | S n'' =>
      evenp2 n''
    end
  end.

Lemma fold_unfold_evenp2_O :
  evenp2 0 =
  true.
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

Lemma fold_unfold_evenp2_1 :
  evenp2 1 =
  false.
Proof.
  rewrite -> fold_unfold_evenp2_S.
  reflexivity.
Qed.

Lemma fold_unfold_evenp2_SS :
  forall n'' : nat,
    evenp2 (S (S n'')) =
    evenp2 n''.
Proof.
  intro n''.
  rewrite -> fold_unfold_evenp2_S.
  reflexivity.
Qed.

Theorem evenp1_and_evenp2_are_functionally_equal :
  forall n : nat,
    evenp1 n = evenp2 n.
Proof.
  intro n.
  induction n as [ | | n'' IHn''] using nat_ind2.
  - rewrite -> fold_unfold_evenp1_O.
    rewrite -> fold_unfold_evenp2_O.
    reflexivity.
  - rewrite -> fold_unfold_evenp1_S.
    rewrite -> fold_unfold_evenp2_S.
    rewrite -> fold_unfold_evenp1_O.
    unfold negb.
    reflexivity.
  - rewrite -> fold_unfold_evenp1_S.
    rewrite -> fold_unfold_evenp2_S.
    rewrite -> fold_unfold_evenp1_S.
    Search (negb (negb _) = _).
    rewrite -> negb_involutive.
    exact IHn''.
(*
  Restart.

  intro n.
  induction n as [ | n' IHn'].
  (* why don't you give it a try? *)
*)
Qed.

Lemma twice_succ :
  forall n : nat,
    S (S (2 * n)) = 2 * S n.
Proof.
Admitted.

Theorem soundness_and_completeness_of_evenp :
  forall n : nat,
    evenp2 n = true <-> exists m : nat, n = 2 * m.
Proof.
  intro n.
  induction n as [ | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete]] using nat_ind2.

  - rewrite -> fold_unfold_evenp2_O.
    split.
    + intros _.
      exists 0.
      symmetry.
      exact (Nat.mul_0_r 2).
    + intros _.
      reflexivity.

  - rewrite -> fold_unfold_evenp2_1.
    split.
    + intros H_absurd.
      discriminate H_absurd.
    + intros [[ | m'] H_m'].
      * rewrite -> Nat.mul_0_r in H_m'.
        discriminate H_m'.
      * rewrite <- twice_succ in H_m'.
        discriminate H_m'.

  - rewrite -> fold_unfold_evenp2_SS.
    split.
    + intro H_n'.
      destruct (IHn'_sound H_n') as [m H_m].
      rewrite -> H_m.
      exists (S m).
      exact (twice_succ m).

    + intros [[ | m'] H_m'].
      * rewrite -> Nat.mul_0_r in H_m'.
        discriminate H_m'.
      * apply IHn'_complete.
        rewrite <- twice_succ in H_m'.
        rewrite -> Nat.mul_comm in H_m'.
        injection H_m' as H_m'.
        rewrite -> Nat.mul_comm in H_m'.
        exists m'.
        exact H_m'.
Qed.

(* ********** *)

Fixpoint ternaryp (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | 1 =>
    false
  | 2 =>
    false
  | S (S (S n')) =>
    ternaryp n'
  end.

Lemma fold_unfold_ternaryp_O :
  ternaryp 0 =
  true.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Lemma fold_unfold_ternaryp_1 :
  ternaryp 1 =
  false.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Lemma fold_unfold_ternaryp_2 :
  ternaryp 2 =
  false.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Lemma fold_unfold_ternaryp_SSS :
  forall n' : nat,
    ternaryp (S (S (S n'))) =
    ternaryp n'.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Theorem soundness_and_completeness_of_ternaryp :
  forall n : nat,
    ternaryp n = true <-> exists m : nat, n = 3 * m.
Proof.
Abort.

(* ********** *)

(* Let us turn to course-of-value induction: *)

Fixpoint and_until (P : nat -> Prop) (n : nat) : Prop :=
  match n with
  | 0 =>
    P 0
  | S n' =>
    P (S n') /\ and_until P n'
end.

Lemma fold_unfold_and_until_O :
  forall P : nat -> Prop,
    and_until P 0 =
    P 0.
Proof.
  fold_unfold_tactic and_until.
Qed.

Lemma fold_unfold_and_until_S :
  forall (P : nat -> Prop)
         (n' : nat),
    and_until P (S n') =
    (P (S n') /\ and_until P n').
Proof.
  fold_unfold_tactic and_until.
Qed.

Lemma nat_ind_course_of_values :
  forall P : nat -> Prop,
    P 0 ->
    (forall k : nat,
        and_until P k -> P (S k)) ->
    forall n : nat,
      P n.
Proof.
  intros P H_O H_S.
  assert (Helpful :
            forall x : nat,
              and_until P x).
  { intro x.
    induction x as [ | x' IHx'].

    - rewrite -> fold_unfold_and_until_O.
      exact H_O.

    - rewrite -> fold_unfold_and_until_S.
      Check (H_S x').
      Check (H_S x' IHx').
      exact (conj (H_S x' IHx') IHx'). }
  intros [ | n'].

  - exact H_O.

  - Check (H_S n').
    Check (H_S n' (Helpful n')).
    exact (H_S n' (Helpful n')).
Qed.

(* ***** *)

Lemma and_until_implies_the_last :
  forall (P : nat -> Prop)
         (x : nat),
    and_until P x -> P x.
Proof.
  intros P [ | x'] H_Px.

  - rewrite -> fold_unfold_and_until_O in H_Px.
    exact H_Px.

  - rewrite -> fold_unfold_and_until_S in H_Px.
    destruct H_Px as [ly _].
    exact ly.
Qed.

Theorem soundness_and_completeness_of_evenp_using_course_of_value_induction :
  forall n : nat,
    evenp2 n = true <-> exists m : nat, n = 2 * m.
Proof.
  intro n.
  induction n as [ | [ | n'] IHn'] using nat_ind_course_of_values.

  - rewrite -> fold_unfold_evenp2_O.
    split.
    + intros _.
      exists 0.
      symmetry.
      exact (Nat.mul_0_r 2).
    + intros _.
      reflexivity.

  - rewrite -> fold_unfold_evenp2_1.
    split.
    + intros H_absurd.
      discriminate H_absurd.
    + intros [[ | m'] H_m'].
      * rewrite -> Nat.mul_0_r in H_m'.
        discriminate H_m'.
      * rewrite <- twice_succ in H_m'.
        discriminate H_m'.

  - rewrite -> fold_unfold_evenp2_SS.
    rewrite -> fold_unfold_and_until_S in IHn'.
    destruct IHn' as [[IHSn'_sound IHSn'_complete] IHn'].
    apply and_until_implies_the_last in IHn'.
    destruct IHn' as [IHn'_sound IHn'_complete].
    (* and we are back on tracks *)
    split.
    + intro H_n'.
      destruct (IHn'_sound H_n') as [m H_m].
      rewrite -> H_m.
      exists (S m).
      exact (twice_succ m).

    + intros [[ | m'] H_m'].
      * rewrite -> Nat.mul_0_r in H_m'.
        discriminate H_m'.
      * apply IHn'_complete.
        rewrite <- twice_succ in H_m'.
        rewrite -> Nat.mul_comm in H_m'.
        injection H_m' as H_m'.
        rewrite -> Nat.mul_comm in H_m'.
        exists m'.
        exact H_m'.
Qed.

(* ********** *)

(* Let us turn to strong induction: *)

Lemma and_until_implies_any_one_of_them :
  forall (P : nat -> Prop)
         (y : nat),
    and_until P y ->
    forall x : nat,
      x <= y ->
      P x.
Proof.
  intros P y.
  induction y as [ | y' IHy']; intros P_y x H_x.

  - rewrite -> fold_unfold_and_until_O in P_y.
    Search (_ <= 0).
    Check (le_n_0_eq x H_x).
    rewrite <- (le_n_0_eq x H_x).
    exact P_y.

  - rewrite -> fold_unfold_and_until_S in P_y.
    destruct P_y as [P_Sy' P_y'].
    Search (_ <= _ -> _ \/ _).
    Check (le_lt_or_eq x (S y') H_x).
    destruct (le_lt_or_eq x (S y') H_x) as [H_y' | H_y'].
    + Search (_ < S _ -> _ <= _).
      Check (lt_n_Sm_le x y').
      apply (lt_n_Sm_le x y') in H_y'.
      Check (IHy' P_y' x H_y').
      exact (IHy' P_y' x H_y').
    + rewrite -> H_y'.
      exact P_Sy'.
Qed.

Lemma any_one_of_them_implies_and_until :
  forall (P : nat -> Prop)
         (y : nat),
    (forall x : nat,
      x <= y ->
      P x) ->
    and_until P y.
Proof.
  intros P y.
  induction y as [ | y' IHy']; intro H_y.

  - rewrite -> fold_unfold_and_until_O.
    Search (0 <= _).
    Check (Peano.le_0_n 0).
    Check (H_y 0 (Peano.le_0_n 0)).
    exact (H_y 0 (Peano.le_0_n 0)).

  - rewrite -> fold_unfold_and_until_S.
    split.

    + Check (H_y (S y')).
      Search (_ <= _).
      Check (Nat.le_refl (S y')).
      Check (H_y (S y') (Nat.le_refl (S y'))).
      exact (H_y (S y') (Nat.le_refl (S y'))).

    + apply IHy'.
      intros x H_x.
      Search (_ <= _ -> _ <= S _).
      Check (le_S x y' H_x).
      Check (H_y x (le_S x y' H_x)).
      exact (H_y x (le_S x y' H_x)).
Qed.

Lemma la_meme_chose :
  forall P : nat -> Prop,
    (forall m : nat,
        (forall k : nat,
            k <= m -> P k) ->
        P (S m))
    <->
    (forall i : nat,
        and_until P i -> P (S i)).
Proof.
  intro P.
  split.

  - intros H_S i H_Pi.
    Check (H_S i).
    apply (H_S i).
    intros k H_k.
    Check (and_until_implies_any_one_of_them P i H_Pi k H_k).
    exact (and_until_implies_any_one_of_them P i H_Pi k H_k).

  - intros H_and_until m H_m.
    Check (H_and_until m).
    apply (H_and_until m).
    Check (any_one_of_them_implies_and_until P m H_m).
    exact (any_one_of_them_implies_and_until P m H_m).
Qed.

Lemma nat_ind_strong :
  forall P : nat -> Prop,
    P 0 ->
    (forall k : nat,
        (forall i : nat,
            i <= k -> P i) ->
        P (S k)) ->
    forall n : nat,
      P n.
Proof.
  intros P P_O P_S.
  destruct (la_meme_chose P) as [H_strong_implies_course_of_values H_course_of_values_implies_strong].
  Check (H_strong_implies_course_of_values P_S).
  Check (nat_ind_course_of_values P P_O (H_strong_implies_course_of_values P_S)).
  exact (nat_ind_course_of_values P P_O (H_strong_implies_course_of_values P_S)).
Qed.

(* ***** *)

Theorem soundness_and_completeness_of_evenp2_using_strong_induction :
  forall n : nat,
    evenp2 n = true <-> exists m : nat, n = 2 * m.
Proof.
  intro n.
  induction n as [ | [ | n'] IHn'] using nat_ind_strong.

  - rewrite -> fold_unfold_evenp2_O.
    split.
    + intros _.
      exists 0.
      symmetry.
      exact (Nat.mul_0_r 2).
    + intros _.
      reflexivity.

  - rewrite -> fold_unfold_evenp2_1.
    split.
    + intros H_absurd.
      discriminate H_absurd.
    + intros [[ | m'] H_m'].
      * rewrite -> Nat.mul_0_r in H_m'.
        discriminate H_m'.
      * rewrite <- twice_succ in H_m'.
        discriminate H_m'.

  - rewrite -> fold_unfold_evenp2_SS.
    Search (_ <= S _).
    Check (Nat.le_succ_diag_r n').
    Check (IHn' n' (Nat.le_succ_diag_r n')).
    destruct (IHn' n' (Nat.le_succ_diag_r n')) as [IHn'_sound IHn'_complete].
    (* and we are back on tracks *)
    split.
    + intro H_n'.
      destruct (IHn'_sound H_n') as [m H_m].
      rewrite -> H_m.
      exists (S m).
      exact (twice_succ m).

    + intros [[ | m'] H_m'].
      * rewrite -> Nat.mul_0_r in H_m'.
        discriminate H_m'.
      * apply IHn'_complete.
        rewrite <- twice_succ in H_m'.
        rewrite -> Nat.mul_comm in H_m'.
        injection H_m' as H_m'.
        rewrite -> Nat.mul_comm in H_m'.
        exists m'.
        exact H_m'.
Qed.

(* ********** *)

(* end of week-10_induction-principles-continued.v *)
