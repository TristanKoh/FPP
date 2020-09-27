(* midterm-project.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 20 Sep 2020 *)

(* ********** *)

(* A study of polymorphic lists. *)

(* Tristan Koh
   tristan.koh@u.yale-nus.edu.sg
   21/9/20

   please upload one .v file and one .pdf file containing a project report

   desiderata:
   - the file should be readable, i.e., properly indented and using items or {...} for subgoals
   - each use of a tactic should achieve one proof step
   - all lemmas should be applied to all their arguments
   - there should be no occurrences of admit, admitted, and abort
*)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* ********** *)

Definition eqb_option (V : Type) (eqb_V : V -> V -> bool) (ov1 ov2 : option V) : bool :=
  match ov1 with
  | Some v1 =>
    match ov2 with
    | Some v2 =>
      eqb_V v1 v2
    | None =>
      false
    end
  | None =>
    match ov2 with
    | Some v2 =>
      false
    | None =>
      true
    end
  end.

Notation "A =on= B" :=
  (eqb_option nat beq_nat A B) (at level 70, right associativity).

(* ********** *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
  end.

Lemma fold_unfold_eqb_list_nil :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v2s : list V),
    eqb_list V eqb_V nil v2s =
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

Lemma fold_unfold_eqb_list_cons :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v1 : V)
         (v1s' v2s : list V),
    eqb_list V eqb_V (v1 :: v1s') v2s =
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

(* Exercise 0: *)

Theorem soundness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall v1s v2s : list V,
      eqb_list V eqb_V v1s v2s = true ->
      v1s = v2s.
Proof.
  intros V eqb_v H_eqb_v v1s v2s.
  intro H_eqb_list.
  induction v1s as [ | v  v1s' IHv1s'].
  - destruct v2s as [ | v v2s'].
    + reflexivity. 
    + discriminate.
  - induction v2s as [ | v2  v2s' IHv2s'].
    + discriminate.
    + rewrite -> (fold_unfold_eqb_list_cons V eqb_v v v1s' (v2 :: v2s')) in H_eqb_list.
      Search (_ && _ = true -> _ /\_).
      assert (H_and_v_vs' :=  (andb_prop (eqb_v v v2)(eqb_list V eqb_v v1s' v2s'))).
      assert (H_and_v_vs' := H_and_v_vs' H_eqb_list).
      destruct H_and_v_vs' as [H_v H_vs'].
      rewrite -> (H_eqb_v v v2 H_v).
      rewrite -> (fold_unfold_eqb_list_cons V eqb_v v v1s' v2s') in IHv2s'.
Abort.

Theorem completeness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall v1s v2s : list V,
      v1s = v2s ->
      eqb_list V eqb_V v1s v2s = true.
Proof.
  intros V eqb_v H_v v1s v2s.
  intro H_v1s_v2s.
  induction v1s as [ | v1s' IHv1s'].
  - Check (fold_unfold_eqb_list_nil V eqb_v v2s).
    rewrite -> (fold_unfold_eqb_list_nil V eqb_v v2s).
  
Abort.

(* ********** *)

(* A study of the polymorphic length function: *)

Definition specification_of_length (length : forall V : Type, list V -> nat) :=
  (forall V : Type,
      length V nil = 0)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
     length V (v :: vs') = S (length V vs')).

(* Unit-test function: *)

Definition test_length (candidate : forall V : Type, list V -> nat) :=
  (candidate nat nil =n= 0) &&
  (candidate bool nil =n= 0) &&
  (candidate nat (1 :: nil) =n= 1) &&
  (candidate bool (true :: nil) =n= 1) &&
  (candidate nat (2 :: 1 :: nil) =n= 2) &&
  (candidate bool (false :: true :: nil) =n= 2) &&
  (candidate nat (3 :: 2 :: 1 :: nil) =n= 3) &&
  (candidate bool (false :: false :: true :: nil) =n= 3).

(* The specification specifies at most one length function: *)

Theorem there_is_at_most_one_length_function :
  forall (V : Type)
         (length_1 length_2 : forall V : Type, list V -> nat),
    specification_of_length length_1 ->
    specification_of_length length_2 ->
    forall vs : list V,
      length_1 V vs = length_2 V vs.
Proof.
  intros V length_1 length_2.
  unfold specification_of_length.
  intros [S_length_1_nil S_length_1_cons]
         [S_length_2_nil S_length_2_cons]
         vs.
  induction vs as [ | v vs' IHvs'].

  - Check (S_length_2_nil V).
    rewrite -> (S_length_2_nil V).
    Check (S_length_1_nil V).
    exact (S_length_1_nil V).

  - Check (S_length_1_cons V v vs').
    rewrite -> (S_length_1_cons V v vs').
    rewrite -> (S_length_2_cons V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(* The length function in direct style: *)

Fixpoint length_v0_aux (V : Type) (vs : list V) : nat :=
  match vs with
    | nil =>
      0
    | v :: vs' =>
      S (length_v0_aux V vs')
  end.

Definition length_v0 (V : Type) (vs : list V) : nat :=
  length_v0_aux V vs.

Compute (test_length length_v0).

(* Associated fold-unfold lemmas: *)

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

(* The specification specifies at least one length function: *)

Theorem length_v0_satisfies_the_specification_of_length :
  specification_of_length length_v0.
Proof.
  unfold specification_of_length, length_v0.
  split.
  - exact fold_unfold_length_v0_aux_nil.
  - exact fold_unfold_length_v0_aux_cons.
Qed.

(* ***** *)

(* Exercise 1: *)

(* Implement the length function using an accumulator. *)


Fixpoint length_v1_aux (V : Type) (vs : list V) (a : nat) : nat :=
  match vs with
  | nil =>
    a
  | v :: vs' =>
    length_v1_aux V vs' (S a)
  end.

    
Definition length_v1 (V : Type) (vs : list V) : nat :=
  length_v1_aux V vs 0.

Compute (test_length length_v1).

Lemma fold_unfold_length_v1_aux_nil :
  forall (V : Type) (a : nat),
    length_v1_aux V nil a =
    a.
Proof.
  fold_unfold_tactic length_v1_aux.
Qed.

Lemma fold_unfold_length_v1_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (a : nat),
    length_v1_aux V (v::vs') a =
    length_v1_aux V vs' (S a).
Proof.
  fold_unfold_tactic length_v1_aux.
Qed.
    

Lemma eureka_lemma_length_v1_aux :
  forall (V : Type)
         (vs' : list V)
         (a : nat),
    length_v1_aux V vs' (S a) = S (length_v1_aux V vs' a).
Proof.
  intros V vs'.
  induction vs' as [ | v vs'' IHvs''].
  - intro a.
    Check (fold_unfold_length_v1_aux_nil V (S a)).
    rewrite -> (fold_unfold_length_v1_aux_nil V (S a)).
    rewrite -> (fold_unfold_length_v1_aux_nil V a).
    reflexivity.
  - intro a.
    Check (fold_unfold_length_v1_aux_cons).
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs'' (S a)).
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs'' a).
    rewrite -> (IHvs'' (S a)).
    reflexivity.
Qed.    


Theorem length_v1_satisfies_the_specification_of_length :
  specification_of_length length_v1.
Proof.
  unfold specification_of_length, length_v1.
  split.
  - intro V.
    rewrite -> (fold_unfold_length_v1_aux_nil V 0).
    reflexivity.
  - intros V v vs'.
    Check (fold_unfold_length_v1_aux_cons V v (vs') 0).
    rewrite -> (fold_unfold_length_v1_aux_cons V v (vs') 0).
    Check (eureka_lemma_length_v1_aux).
    rewrite -> (eureka_lemma_length_v1_aux V).
    reflexivity.
Qed.

    

(* ********** *)

(* A study of the polymorphic, left-to-right indexing function: *)

(* ***** *)

(* The indexing function can be specified by induction over the given list: *)

Definition test_list_nth (candidate : forall V : Type, list V -> nat -> option V) :=
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 0) =on= (Some 0)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 1) =on= (Some 1)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 2) =on= (Some 2)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 3) =on= (Some 3)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 4) =on= None) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 5) =on= None).

Fixpoint list_nth (V : Type) (vs : list V) (n : nat) : option V :=
  match vs with
  | nil =>
    None
  | v :: vs' =>
    match n with
    | O =>
      Some v
    | S n' =>
      list_nth V vs' n'
    end
  end.

Compute (test_list_nth list_nth).

Lemma fold_unfold_list_nth_nil :
  forall (V : Type)
         (n : nat),
    list_nth V nil n =
    None.
Proof.
  fold_unfold_tactic list_nth.
Qed.

Lemma fold_unfold_list_nth_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (n : nat),
    list_nth V (v :: vs') n =
    match n with
    | O =>
      Some v
    | S n' =>
      list_nth V vs' n'
    end.
Proof.
  fold_unfold_tactic list_nth.
Qed.

(* ***** *)

(* The indexing function can be specified by induction over the given index: *)

Definition test_nat_nth (candidate : forall V : Type, nat -> list V -> option V) :=
  ((candidate nat 0 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 0)) &&
  ((candidate nat 1 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 1)) &&
  ((candidate nat 2 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 2)) &&
  ((candidate nat 3 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 3)) &&
  ((candidate nat 4 (0 :: 1 :: 2 :: 3 :: nil)) =on= None) &&
  ((candidate nat 5 (0 :: 1 :: 2 :: 3 :: nil)) =on= None).

Fixpoint nat_nth (V : Type) (n : nat) (vs : list V) : option V :=
  match n with
  | O =>
    match vs with
    | nil =>
      None
    | v :: vs' =>
      Some v
    end
  | S n' =>
    match vs with
    | nil =>
      None
    | v :: vs' =>
      nat_nth V n' vs'
    end
  end.

Compute (test_nat_nth nat_nth).

Lemma fold_unfold_nat_nth_O :
  forall (V : Type)
         (vs : list V),
    nat_nth V O vs =
    match vs with
    | nil =>
      None
    | v :: vs' =>
      Some v
    end.
Proof.
  fold_unfold_tactic nat_nth.
Qed.

Lemma fold_unfold_nat_nth_S :
  forall (V : Type)
         (n' : nat)
         (vs : list V),
    nat_nth V (S n') vs =
    match vs with
    | nil =>
      None
    | v :: vs' =>
      nat_nth V n' vs'
    end.
Proof.
  fold_unfold_tactic nat_nth.
Qed.

(* ***** *)

(* Exercise 2: *)

(* 
   a. Both list-indexing functions come with their own unit-test function.
      Test each implementation with the unit-test function of the other implementation,
      and verify that it passes this other test.
*)

Compute (test_list_nth (fun V vs' n => nat_nth V n vs')).

Compute (test_nat_nth (fun V n vs' => list_nth V vs' n)).


(*
   b. prove that if, given a list and an index, list_nth yields a result,
      then given this index and this list, nat_nth yields the same result
*)


Proposition list_nth_implies_nat_nth :
  forall (V : Type)
         (vs : list V)
         (n : nat)
         (ov : option V),
    list_nth V vs n = ov ->
    nat_nth V n vs = ov.
Proof.
  intros V vs n ov.
  revert n.
  induction vs as [ | v vs' IHvs'].
  - intros [ | n'].
    + intro H_list_nth.
      rewrite -> (fold_unfold_nat_nth_O V nil).
      rewrite -> (fold_unfold_list_nth_nil V 0) in H_list_nth.
      exact H_list_nth.
    + intro H_list_nth.
      rewrite -> (fold_unfold_nat_nth_S V).
      rewrite -> (fold_unfold_list_nth_nil V (S n')) in H_list_nth.
      exact H_list_nth.
  - intros [ | n'].
    + intro H_list_nth.
      rewrite -> (fold_unfold_nat_nth_O V (v :: vs')).
      rewrite -> (fold_unfold_list_nth_cons V v vs' 0) in H_list_nth.
      exact H_list_nth.
    + intro H_list_nth.
      rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')).
      rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')) in H_list_nth.
      exact (IHvs' n' H_list_nth).

  Restart.

  intros V vs n ov.
  revert vs.
  induction n as [ | n' IHn' ].
  - intros [ | v vs'].
    + intro H_list_nth.
      rewrite -> (fold_unfold_nat_nth_O V nil).
      rewrite -> (fold_unfold_list_nth_nil V 0) in H_list_nth.
      exact H_list_nth.
    + intro H_list_nth.
      rewrite -> (fold_unfold_nat_nth_O V (v :: vs')).
      rewrite -> (fold_unfold_list_nth_cons V v vs' 0) in H_list_nth.
      exact H_list_nth.
  - intros [ | v vs'].
    + intro H_list_nth.
      rewrite -> (fold_unfold_nat_nth_S V n' nil).
      rewrite -> (fold_unfold_list_nth_nil V (S n')) in H_list_nth.
      exact H_list_nth.
    + intro H_list_nth.
      rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')).
      rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')) in H_list_nth.
      exact (IHn' vs' H_list_nth).      
Qed.
    
    
(*
   c. prove that if, given an index and a list, nat_nth yields a result,
      then given this list and this index, list_nth yields the same result
*)

Proposition nat_nth_implies_list_nth :
  forall (V : Type)
         (n : nat)
         (vs : list V)
         (ov : option V),
    nat_nth V n vs = ov ->
    list_nth V vs n = ov.
Proof.
    intros V n vs ov.
  revert vs.
  induction n as [ | n' IHn' ].
  - intros [ | v vs'].
    + intro H_nat_nth.
      rewrite -> (fold_unfold_nat_nth_O V nil) in H_nat_nth.
      rewrite -> (fold_unfold_list_nth_nil V 0).
      exact H_nat_nth.
    + intro H_nat_nth.
      rewrite -> (fold_unfold_nat_nth_O V (v :: vs')) in H_nat_nth.
      rewrite -> (fold_unfold_list_nth_cons V v vs' 0).
      exact H_nat_nth.
  - intros [ | v vs'].
    + intro H_nat_nth.
      rewrite -> (fold_unfold_nat_nth_S V n' nil) in H_nat_nth.
      rewrite -> (fold_unfold_list_nth_nil V (S n')).
      exact H_nat_nth.
    + intro H_nat_nth.
      rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')) in H_nat_nth.
      rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')).
      exact (IHn' vs' H_nat_nth).

  Restart.

  intros V n vs ov.
  revert n.
  induction vs as [ | v vs' IHvs'].
  - intros [ | n'].
    + intro H_nat_nth.
      rewrite -> (fold_unfold_nat_nth_O V nil) in H_nat_nth.
      rewrite -> (fold_unfold_list_nth_nil V 0).
      exact H_nat_nth.
    + intro H_nat_nth.
      rewrite -> (fold_unfold_nat_nth_S V) in H_nat_nth.
      rewrite -> (fold_unfold_list_nth_nil V (S n')).
      exact H_nat_nth.
  - intros [ | n'].
    + intro H_nat_nth.
      rewrite -> (fold_unfold_nat_nth_O V (v :: vs')) in H_nat_nth.
      rewrite -> (fold_unfold_list_nth_cons V v vs' 0).
      exact H_nat_nth.
    + intro H_nat_nth.
      rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')) in H_nat_nth.
      rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')).
      exact (IHvs' n' H_nat_nth).
Qed.    



(*
   d. What do you conclude?
*)

(* ********** *)

(* A study of the polymorphic copy function: *)

Definition specification_of_copy (copy : forall V : Type, list V -> list V) :=
  (forall V : Type,
      copy V nil = nil)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
     copy V (v :: vs') = v :: (copy V vs')).

Definition test_copy (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat nil) nil) &&
  (eqb_list bool eqb (candidate bool nil) nil) &&
  (eqb_list nat beq_nat (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (2 :: 1 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (false :: true :: nil)) (false :: true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (3 :: 2 :: 1 :: nil)) (3 :: 2 :: 1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: false :: true :: nil)) (true :: false :: true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (4 :: 3 :: 2 :: 1 :: nil)) (4 :: 3 :: 2 :: 1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (false :: true :: false :: true :: nil)) (false :: true :: false :: true :: nil)).

(* Exercise 3:

   a. expand the unit-test function for copy with a few more tests

   b. implement the copy function in direct style
*)

Fixpoint copy_v0_aux (V : Type) (vs : list V) : list V :=
    match vs with
  | nil =>
    nil
  | v :: vs' =>
    v :: (copy_v0_aux V vs')
  end.
  
Definition copy_v0 (V : Type) (vs : list V) : list V :=
  copy_v0_aux V vs.

Compute (test_copy copy_v0).

(*
   c. state its associated fold-unfold lemmas

 *)


Lemma fold_unfold_copy_v0_aux_nil :
  forall V : Type,
    copy_v0_aux V nil =
    nil.
Proof.
  fold_unfold_tactic copy_v0_aux.
Qed.


Lemma fold_unfold_copy_v0_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    copy_v0_aux V (v :: vs') =
    v :: (copy_v0_aux V vs').
Proof.
  fold_unfold_tactic copy_v0_aux.
Qed.


(*
   d. prove whether your implementation satisfies the specification.

 *)

Theorem copy_v0_satisfies_the_specification_of_copy :
  specification_of_copy copy_v0.
Proof.
  unfold specification_of_copy, copy_v0.
  split.
  - exact fold_unfold_copy_v0_aux_nil.
  - exact fold_unfold_copy_v0_aux_cons.
Qed.

      
(*
   e. prove whether copy is idempotent
*)

Proposition copy_is_idempotent :
  forall (V : Type)
         (vs : list V),
    copy_v0 V (copy_v0 V vs) = copy_v0 V vs.
Proof.
  intros V vs.
  unfold copy_v0.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_copy_v0_aux_nil V).
    rewrite -> (fold_unfold_copy_v0_aux_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_copy_v0_aux_cons V v (vs')).
    rewrite -> (fold_unfold_copy_v0_aux_cons V v (copy_v0_aux V vs')).
    rewrite -> IHvs'.
    reflexivity.
Qed. 
 

(*
   f. prove whether copying a list preserves its length
*)


Lemma eureka_lemma_copy_v0_aux_preserves_length :
  forall (V : Type)
         (vs' : list V),
    copy_v0_aux V vs' = vs'.
Proof.
  intro V.  
  induction vs' as [ | v' vs'' IHvs''].
  - exact (fold_unfold_copy_v0_aux_nil V).
  - Check (fold_unfold_copy_v0_aux_cons).
    rewrite -> (fold_unfold_copy_v0_aux_cons V v' vs'').
    rewrite -> IHvs''.
    reflexivity.
Qed.    

Proposition copy_preserves_length :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 V (copy_v0 V vs) = n.
Proof.
  intros V.
  unfold length_v0, copy_v0.
  intros [ | v' vs'].
  - intro n.
    intro H_length_v0_aux.
    rewrite -> (fold_unfold_length_v0_aux_nil V) in H_length_v0_aux.
    rewrite -> (fold_unfold_copy_v0_aux_nil V).
    rewrite -> (fold_unfold_length_v0_aux_nil V).
    exact H_length_v0_aux.
  - intro n.
    intro H_length_v0_aux.
    Check (fold_unfold_length_v0_aux_cons).
    rewrite -> (fold_unfold_length_v0_aux_cons V v' vs') in H_length_v0_aux.
    Check (fold_unfold_copy_v0_aux_cons).
    rewrite -> (fold_unfold_copy_v0_aux_cons V v' vs').
    rewrite -> (fold_unfold_length_v0_aux_cons V v' (copy_v0_aux V vs')).
    Check (eureka_lemma_copy_v0_aux_preserves_length).
    rewrite -> (eureka_lemma_copy_v0_aux_preserves_length V vs').
    exact H_length_v0_aux.
Qed.

 


(*
   g. subsidiary question: can you think of a strikingly simple implementation of the copy function?
      if so, pray show that it satisfies the specification of copy
 *)

Definition copy_v1 (V : Type) (vs : list V) : list V :=
  vs.

Compute (test_copy copy_v1).

Theorem copy_v1_satisfies_the_specification_of_copy :
  specification_of_copy copy_v1.
Proof.
  unfold specification_of_copy, copy_v1.
  split.
  - intro V.
    reflexivity.
  - intros V v vs'.
    reflexivity.
Qed.  

(* ********** *)

(* A study of the polymorphic append function: *)

Definition specification_of_append (append : forall V : Type, list V -> list V -> list V) :=
  (forall (V : Type)
          (v2s : list V),
      append V nil v2s = v2s)
  /\
  (forall (V : Type)
          (v1 : V)
          (v1s' v2s : list V),
      append V (v1 :: v1s') v2s = v1 :: append V v1s' v2s).

(* Exercise 4:

   a. define a unit-test function for append

*)

Definition test_append (candidate : forall V : Type, list V -> list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat
                                   nil
                                   nil)
            nil)
  &&
  (eqb_list bool eqb (candidate bool
                                nil
                                nil)
            nil)
  &&
  (eqb_list nat beq_nat (candidate nat
                                   (1 :: nil)
                                   (1 :: nil))
            (1 :: 1 :: nil))
  &&
  (eqb_list bool eqb (candidate bool
                                (true :: nil)
                                (true :: nil))
            (true :: true :: nil))
  &&
  (eqb_list nat beq_nat (candidate nat
                                   (3 :: 2 :: nil)
                                   (1 :: nil))
            (3 :: 2 :: 1 :: nil))
  &&
  (eqb_list bool eqb (candidate bool
                                (false :: true :: nil)
                                (false :: true :: nil))
            (false :: true :: false :: true :: nil))
  &&
  (eqb_list nat beq_nat (candidate nat
                                   (6 :: 5 :: 4 :: nil)
                                   (3 :: 2 :: 1 :: nil))
            (6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil))
  &&
  (eqb_list bool eqb (candidate bool
                                (true :: false :: true :: nil)
                                (true :: false :: true :: nil))
            (true :: false :: true :: true :: false :: true :: nil))
  &&
  (eqb_list nat beq_nat (candidate nat
                                   (8 :: 7 :: 6 :: 5 :: nil)
                                   (4 :: 3 :: 2 :: 1 :: nil))
            (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil))
  &&
  (eqb_list bool eqb (candidate bool
                                (false :: true :: false :: true :: nil)
                                (false :: true :: false :: true :: nil))
            (false :: true :: false :: true :: false :: true :: false :: true :: nil)).


(*
   b. implement the append function in direct style
*)

Fixpoint append_v0_aux (V : Type) (v1s v2s : list V) : list V :=
  match v1s with
  | nil =>
    v2s
  | v1 :: v1s' =>
      v1 :: (append_v0_aux V v1s' v2s)
    end.


Definition append_v0 (V : Type) (v1s v2s : list V) : list V :=
  append_v0_aux V v1s v2s.


Compute (test_append append_v0).

(*
   c. state its associated fold-unfold lemmas

 *)

Lemma fold_unfold_append_v0_aux_nil :
  forall (V : Type)
         (v2s : list V),
    append_v0_aux V nil v2s =
    v2s.
Proof.
  fold_unfold_tactic append_v0_aux.
Qed.


Lemma fold_unfold_append_v0_aux_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    append_v0_aux V (v1 :: v1s') v2s =
      v1 :: (append_v0_aux V v1s' v2s).
Proof.
  fold_unfold_tactic append_v0_aux.
Qed.

(*

   d. prove that your implementation satisfies the specification
 *)


Theorem append_v0_satisfies_the_specification_of_append :
  specification_of_append append_v0.
Proof.
  unfold specification_of_append, append_v0.
  split.
  - intros V v2s.
    rewrite -> (fold_unfold_append_v0_aux_nil V).
    reflexivity.
  - intros V v1 v1s' v2s.
    exact (fold_unfold_append_v0_aux_cons V v1 v1s' v2s).
Qed.
    
(*
   e. prove whether nil is neutral on the left of append

 *)

Proposition nil_is_left_neutral_of_append_v0 :
  forall (V : Type)
         (vs : list V),
    append_v0 V nil vs = vs.
Proof.
  unfold append_v0.
  exact fold_unfold_append_v0_aux_nil.
Qed.

  
(*
   f. prove whether nil is neutral on the right of append
*)

Proposition nil_is_right_neutral_of_append_v0 :
  forall (V : Type)
         (vs : list V),
    append_v0 V vs nil = vs.
Proof.
  intros V vs.
  unfold append_v0.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_append_v0_aux_nil V nil).
    reflexivity.
  - Check (fold_unfold_append_v0_aux_cons).
    rewrite -> (fold_unfold_append_v0_aux_cons V v vs' nil).
    rewrite -> IHvs'.
    reflexivity.
Qed.
    
   
(*
   g. prove whether append is commutative
*)
Theorem append_v0_is_not_commutative :
  exists (V : Type),
  exists (v1s v2s : list V),
    append_v0 V v1s v2s <> append_v0 V v2s v1s.
Proof.
  exists nat.
  exists (1 :: nil).
  exists (2 :: nil).
  unfold append_v0.
  rewrite -> (fold_unfold_append_v0_aux_cons nat 1 nil (2 :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_nil nat (2 :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_cons nat 2 nil (1 :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_nil nat (1 :: nil)).
  unfold not.
  intro H_absurd.
  discriminate H_absurd.
Qed.
 
Theorem append_v0_is_not_commutative_more_generally :
  forall (V : Type),
  exists (v1s v2s : list V),
    append_v0 V v1s v2s <> append_v0 V v2s v1s.
Proof.
  intro V.
Abort.


(*
   h. prove whether append is associative
*)

Lemma append_v0_aux_is_associative : 
  forall (V : Type)
         (v1s v2s v3s : list V),
    append_v0_aux V v1s (append_v0_aux V v2s v3s) = append_v0_aux V (append_v0_aux V v1s v2s) v3s.
Proof.
  intros V v1s v2s v3s.
  induction v1s as [ | v' v1s' IHv1s'].
  - rewrite -> (fold_unfold_append_v0_aux_nil V (append_v0_aux V v2s v3s)).
    rewrite -> (fold_unfold_append_v0_aux_nil V v2s).
    reflexivity.
  - Check (fold_unfold_append_v0_aux_cons).
    rewrite -> (fold_unfold_append_v0_aux_cons V v' v1s' (append_v0_aux V v2s v3s)).
    rewrite -> (fold_unfold_append_v0_aux_cons V v' v1s' v2s).
    rewrite -> (fold_unfold_append_v0_aux_cons V v' (append_v0_aux V v1s' v2s) v3s).
    rewrite -> IHv1s'.
    reflexivity.
Qed.

Proposition append_v0_is_associative :
  forall (V : Type)
         (v1s v2s v3s : list V),
    append_v0 V v1s (append_v0 V v2s v3s) = append_v0 V (append_v0 V v1s v2s) v3s.
Proof.
  unfold append_v0.
  exact append_v0_aux_is_associative.
Qed.


(*
   i. prove whether appending two lists preserves their length
*)


Lemma eureka_lemma_append_preserves_length_aux :
  forall (V : Type)
         (v1s v2s : list V),
    length_v0_aux V (append_v0_aux V v1s v2s) = length_v0_aux V v1s + length_v0_aux V v2s.
Proof.
  intros V v1s v2s.
  induction v1s as [ | v' v1s' IHv1s'].
  - Check (fold_unfold_length_v0_aux_nil).
    rewrite -> (fold_unfold_length_v0_aux_nil V).
    rewrite -> (fold_unfold_append_v0_aux_nil V).
    rewrite -> (Nat.add_0_l (length_v0_aux V v2s)).
    reflexivity.
  - Check (fold_unfold_append_v0_aux_cons).
    rewrite -> (fold_unfold_append_v0_aux_cons V v' v1s' v2s).
    rewrite -> (fold_unfold_length_v0_aux_cons V v' v1s').
    rewrite -> (fold_unfold_length_v0_aux_cons V v' (append_v0_aux V v1s' v2s)).
    rewrite -> IHv1s'.
    Search ( S(_ + _)).
    rewrite -> (Nat.add_succ_l (length_v0_aux V v1s') (length_v0_aux V v2s)).
    reflexivity.
Qed.

Corollary eureka_lemma_append_preserves_length :
  forall (V : Type)
         (v1s v2s : list V),
    length_v0 V (append_v0 V v1s v2s) = length_v0 V v1s + length_v0 V v2s.
Proof.
  unfold append_v0, length_v0.
  exact eureka_lemma_append_preserves_length_aux.
Qed.
    

Proposition append_preserves_length :
  forall (V : Type)
         (v1s v2s : list V)
         (n1 n2 : nat),
    length_v0 V v1s = n1 ->
    length_v0 V v2s = n2 ->
    length_v0 V (append_v0 V v1s v2s) = length_v0 V v1s + length_v0 V v2s.
Proof.
  intros V.
  unfold length_v0, append_v0.
  intros v1s v2s n1 n2.
  intros H_length_v0_n1 H_length_v0_n2.
  exact (eureka_lemma_append_preserves_length V v1s v2s).
Qed. 

(*
   j. prove whether append and copy commute with each other
*)


Proposition append_and_copy_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    copy_v0 V (append_v0 V v1s v2s) = append_v0 V (copy_v0 V v1s) (copy_v0 V v2s).
Proof.
  intros V v1s v2s.
  unfold copy_v0, append_v0.
  induction v1s as [ | v v1s' IHv1s'].
  - rewrite -> (fold_unfold_append_v0_aux_nil V).
    rewrite -> (fold_unfold_copy_v0_aux_nil V).
    rewrite -> (fold_unfold_append_v0_aux_nil V).
    reflexivity.
  - Check (fold_unfold_append_v0_aux_cons).
    rewrite -> (fold_unfold_append_v0_aux_cons V v v1s' v2s).
    Check fold_unfold_copy_v0_aux_cons.
    rewrite -> (fold_unfold_copy_v0_aux_cons V v (append_v0_aux V v1s' v2s)).
    rewrite -> (fold_unfold_copy_v0_aux_cons V v v1s').
    rewrite -> (fold_unfold_append_v0_aux_cons V v (copy_v0_aux V v1s') (copy_v0_aux V v2s)).
    rewrite -> IHv1s'.
    reflexivity.
Qed.
    


(* ********** *)

(* A study of the polymorphic reverse function: *)

Definition specification_of_reverse (reverse : forall V : Type, list V -> list V) :=
  forall append : forall W : Type, list W -> list W -> list W,
    specification_of_append append ->
    (forall V : Type,
        reverse V nil = nil)
    /\
    (forall (V : Type)
            (v : V)
            (vs' : list V),
        reverse V (v :: vs') = append V (reverse V vs') (v :: nil)).

(* Exercise 5:

   a. define a unit-test function for reverse

 *)


Definition test_reverse (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat
                                   nil)
            nil)
  &&
  (eqb_list bool eqb (candidate bool
                                nil)
            nil)
  &&
  (eqb_list nat beq_nat (candidate nat
                                   (1 :: nil))
            (1 :: nil))
  &&
  (eqb_list bool eqb (candidate bool
                                (true :: nil))
            (true :: nil))
  &&
  (eqb_list nat beq_nat (candidate nat
                                   (2 :: 1 :: nil))
            (1 :: 2 ::  nil))
  &&
  (eqb_list bool eqb (candidate bool
                                (false :: true :: nil))
            (true :: false :: nil))
  &&
  (eqb_list nat beq_nat (candidate nat
                                   (3 :: 2 :: 1 :: nil))
            (1 :: 2 :: 3 :: nil))
  &&
  (eqb_list bool eqb (candidate bool
                                (true :: false :: true :: nil))
            (true :: false :: true :: nil))
  &&
  (eqb_list nat beq_nat (candidate nat
                                   (4 :: 3 :: 2 :: 1 :: nil))
            (1 :: 2 :: 3 :: 4 :: nil))
  &&
  (eqb_list bool eqb (candidate bool
                                (false :: true :: false :: true :: nil))
            (true :: false :: true :: false :: nil)).


(*
   b. implement the reverse function in direct style, using append

 *)

Fixpoint reverse_v0_aux (V : Type) (vs : list V) : list V :=
  match vs with
  | nil =>
    nil
  | v :: vs' =>
    append_v0 V (reverse_v0_aux V vs') (v :: nil)
  end.

Definition reverse_v0 (V : Type) (vs : list V) : list V :=
  reverse_v0_aux V vs.

Compute (test_reverse reverse_v0).

(*
   c. state the associated fold-unfold lemmas
*)


Lemma fold_unfold_reverse_v0_aux_nil :
  forall V : Type,
    reverse_v0_aux V nil =
    nil.
Proof.
  fold_unfold_tactic reverse_v0_aux.
Qed.

Lemma fold_unfold_reverse_v0_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    reverse_v0_aux V (v :: vs') =
    append_v0_aux V (reverse_v0_aux V vs') (v :: nil).
Proof.
  fold_unfold_tactic reverse_v0_aux.
Qed.
  
(*
   d. prove whether your implementation satisfies the specification.

 *)

Proposition there_is_at_most_one_append_function :
  forall (V : Type)
         (append1 append2 : forall V : Type, list V -> list V -> list V),
    specification_of_append append1 ->
    specification_of_append append2 ->
    forall (v1s v2s : list V),
      append1 V v1s v2s = append2 V v1s v2s.
Proof.
  intros V append1 append2.
  unfold specification_of_append.
  intros [H_append1_nil H_append1_cons] [H_append2_nil H_append2_cons] v1s v2s.
  induction v1s as [ | v v1s' IHv1s'].
  - rewrite -> (H_append1_nil V v2s).
    rewrite -> (H_append2_nil V v2s).
    reflexivity.
  - rewrite -> (H_append1_cons V v v1s' v2s).
    rewrite -> (H_append2_cons V v v1s' v2s).
    rewrite -> IHv1s'.
    reflexivity.
Qed.
    
Theorem reverse_v0_satisfies_the_specification_of_reverse :
  specification_of_reverse reverse_v0.
Proof.
  unfold specification_of_reverse, reverse_v0.
  intros append H_append.
  split.
  - intro V.
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    reflexivity.
  - intros V v vs'.
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v vs').
    fold (append_v0 V (reverse_v0_aux V vs') (v :: nil)).
    Check (there_is_at_most_one_append_function V append_v0 append append_v0_satisfies_the_specification_of_append H_append (reverse_v0_aux V vs')(v :: nil)).
    rewrite -> (there_is_at_most_one_append_function V append_v0 append append_v0_satisfies_the_specification_of_append H_append (reverse_v0_aux V vs')(v :: nil)).
    reflexivity.
Qed.
    
(*
   e. prove whether reverse is involutory.
*)


Proposition append_aux_and_reverse_aux_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    reverse_v0_aux V (append_v0_aux V v1s v2s) = append_v0_aux V (reverse_v0_aux V v2s) (reverse_v0_aux V v1s).
Proof.
  intros V v1s v2s.
  induction v1s as [ | v1 v1s' IHv1s' ].
  - rewrite -> (fold_unfold_append_v0_aux_nil V v2s).
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    fold (append_v0 V (reverse_v0_aux V v2s) nil).
    rewrite -> (nil_is_right_neutral_of_append_v0 V (reverse_v0_aux V v2s)).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v0_aux_cons V v1 v1s').
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s').
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v1 (append_v0_aux V v1s' v2s)).
    rewrite -> IHv1s'.
    rewrite <- (append_v0_aux_is_associative V (reverse_v0_aux V v2s) (reverse_v0_aux V v1s') (v1 :: nil)).
    unfold append_v0.
    reflexivity.
Qed.
    

Proposition reverse_is_involutary :
  forall (V : Type)
         (vs : list V),
    reverse_v0 V (reverse_v0 V vs) = vs.
Proof.
  intros V vs.
  unfold reverse_v0.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v0_aux_cons V v vs').
    Check (append_aux_and_reverse_aux_commute_with_each_other V (reverse_v0_aux V vs') (v :: nil)).
    rewrite -> (append_aux_and_reverse_aux_commute_with_each_other V (reverse_v0_aux V vs') (v :: nil)).
    rewrite -> IHvs'.
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v nil).
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_append_v0_aux_nil V (v :: nil)).
    rewrite -> (fold_unfold_append_v0_aux_cons V v nil vs').
    rewrite -> (fold_unfold_append_v0_aux_nil V vs').
    reflexivity.
Qed.


(*
   f. prove whether reversing a list preserves its length

 *)

Proposition reverse_preserves_length :
  forall (V : Type)
         (vs : list V),
    length_v0 V vs = length_v0 V (reverse_v0 V vs).
Proof.
  intros V vs.
  unfold length_v0, reverse_v0.
  induction vs as [ | v' vs' IHvs'].
  - rewrite -> (fold_unfold_length_v0_aux_nil V).
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_length_v0_aux_nil V).
    reflexivity.
  - Check (fold_unfold_length_v0_aux_cons).
    rewrite -> (fold_unfold_length_v0_aux_cons V v' vs').
    rewrite -> IHvs'.
    Check (fold_unfold_reverse_v0_aux_cons).
    rewrite -> (fold_unfold_reverse_v0_aux_cons).
    Check (eureka_lemma_append_preserves_length_aux).
    rewrite -> (eureka_lemma_append_preserves_length_aux V (reverse_v0_aux V vs') (v' :: nil)).
    Check (fold_unfold_length_v0_aux_cons).
    rewrite -> (fold_unfold_length_v0_aux_cons V v' nil).
    rewrite -> (fold_unfold_length_v0_aux_nil V).
    rewrite <- IHvs'.
    Search (_ + 1).
    rewrite -> (Nat.add_1_r (length_v0_aux V vs')).
    reflexivity.
Qed.
    
(*
   g. do append and reverse commute with each other (hint: yes they do) and if so how?
*)

Proposition append_and_reverse_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    reverse_v0 V (append_v0 V v1s v2s) = append_v0 V (reverse_v0 V v2s) (reverse_v0 V v1s).
Proof.
  unfold append_v0, reverse_v0.
  exact append_aux_and_reverse_aux_commute_with_each_other.
Qed.

(*
   h. implement the reverse function using an accumulator instead of using append

*)

Fixpoint reverse_v1_aux (V : Type) (vs a : list V) : list V :=
  match vs with
  | nil =>
    a
  | v :: vs' =>
    reverse_v1_aux V vs' (v :: a)
  end.

Definition reverse_v1 (V : Type) (vs : list V) : list V :=
  reverse_v1_aux V vs nil.

Compute (test_reverse reverse_v1).

Lemma fold_unfold_reverse_v1_aux_nil :
  forall (V : Type),
    reverse_v1_aux V nil nil =
    nil.
Proof.
  fold_unfold_tactic reverse_v1_aux.
Qed.


Lemma fold_unfold_reverse_v1_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' a : list V),
    reverse_v1_aux V (v :: vs') a =
    reverse_v1_aux V vs' (v :: a).
Proof.
  fold_unfold_tactic reverse_v1_aux.
Qed.

Lemma about_reverse_v1 :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    reverse_v1_aux V vs' (v :: nil) = append_v0 V (reverse_v1_aux V vs' nil) (v :: nil).
Proof.
  intros V v vs'.
  induction vs' as [ | v' vs'' IHvs''].
  rewrite -> fold_unfold_reverse_v1_aux_nil.
Abort.

Theorem reverse_v1_satisfies_the_specification_of_reverse :
  specification_of_reverse reverse_v1.
Proof.
  unfold specification_of_reverse, reverse_v1.
  split.
  - intro V.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V).
    reflexivity.
  - intros V v vs'.
    Check (fold_unfold_reverse_v1_aux_cons).    
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' nil).
    Check (there_is_at_most_one_append_function V append_v0 append append_v0_satisfies_the_specification_of_append H (reverse_v1_aux V vs' nil)(v :: nil)).
    rewrite <- (there_is_at_most_one_append_function V append_v0 append append_v0_satisfies_the_specification_of_append H (reverse_v1_aux V vs' nil)(v :: nil)).
    
Abort.


(*
   i. revisit the propositions above (involution, preservation of length, commutation with append)
      and prove whether your implementation using an accumulator satisfies them
 *)


Proposition reverse_v1_is_involutary :
  forall (V : Type)
         (vs : list V),
    reverse_v1 V (reverse_v1 V vs) = vs.
Proof.
Abort.



Proposition reverse_v1_preserves_length :
  forall (V : Type)
         (vs : list V),
    length_v1 V vs = length_v1 V (reverse_v1 V vs).
Proof.
Abort.



Proposition append_and_reverse_v1_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    append_v0 V (reverse_v1 V v1s) (reverse_v1 V v2s) = reverse_v1 V (append_v0 V v2s v1s).
Proof.
Abort.



(* ********** *)

(* A study of the polymorphic map function: *)

Definition specification_of_map (map : forall V W : Type, (V -> W) -> list V -> list W) :=
  (forall (V W : Type)
          (f : V -> W),
      map V W f nil = nil)
  /\
  (forall (V W : Type)
          (f : V -> W)
          (v : V)
          (vs' : list V),
      map V W f (v :: vs') = f v :: map V W f vs').

(* Exercise 6:

   a. prove whether the specification specifies at most one map function *)

Proposition there_is_at_most_one_map_function :
  forall (V W : Type)
         (map1 map2 : forall V W : Type, (V -> W) -> list V -> list W),
    specification_of_map map1 ->
    specification_of_map map2 ->
    forall (vs : list V)
           (f : V -> W),
      map1 V W f vs = map2 V W f vs.
Proof.
  intros V W map1 map2.
  unfold specification_of_map.
  intros [H_map1_nil H_map1_cons] [H_map2_nil H_map2_cons] vs f.
  induction vs as [ | v vs' IHvs' ].
  - rewrite -> (H_map2_nil V W f).
    exact (H_map1_nil V W f).
  - rewrite -> (H_map1_cons V W f v vs').
    rewrite -> (H_map2_cons V W f v vs').
    rewrite -> IHvs'.
    reflexivity.    
Qed.

(*
   b. implement the map function in direct style
 *)

Fixpoint map_v0_aux (V W : Type) (f : V -> W) (vs : list V) : list W :=
  match vs with
  | nil =>
    nil
  | v :: vs' =>
    f v :: map_v0_aux V W f vs'
  end.

Definition map_v0 (V W : Type) (f : V -> W) (vs : list V) : list W :=
  map_v0_aux V W f vs.

(*
   c. state its associated fold-unfold lemmas
 *)

Lemma fold_unfold_map_v0_aux_nil :
  forall (V W : Type)
         (f : V -> W),
    map_v0_aux V W f nil =
    nil.
Proof.
  fold_unfold_tactic map_v0_aux.
Qed.

Lemma fold_unfold_map_v0_aux_cons :
  forall (V W : Type)
         (f : V -> W)
         (v : V)
         (vs' : list V),
    map_v0_aux V W f (v :: vs') =
    f v :: map_v0_aux V W f vs'.
Proof.
  fold_unfold_tactic map_v0_aux.
Qed.

(*
   d. prove whether your implementation satisfies the specification
 *)

Theorem map_v0_satisfies_the_specification_of_map :
  specification_of_map map_v0.
Proof.
  unfold specification_of_map, map_v0.
  split.
  - exact fold_unfold_map_v0_aux_nil.
  - exact fold_unfold_map_v0_aux_cons.
Qed.
(*
   e. implement the copy function using map
 *)

Definition copy_v2 (V : Type) (vs : list V) : list V :=
  map_v0 V V (fun v => v) vs.

Compute (test_copy copy_v2).

Theorem copy_v2_satisfies_the_specification_of_copy :
  specification_of_copy copy_v2.
Proof.
  unfold specification_of_copy, copy_v2.
  unfold map_v0.
  split.
  - intro V.
    exact (fold_unfold_map_v0_aux_nil V V (fun v : V => v)).
  - intros V v vs'.
    exact (fold_unfold_map_v0_aux_cons V V (fun v0 : V => v0) v vs').
Qed.


(*
   f. prove whether mapping a function over a list preserves the length of this list
 *)



Proposition map_preserves_length :
  forall (V W : Type)
         (f : V -> W)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 W (map_v0 V W f vs) = n.
Proof.
  intros V W f vs n.
  unfold length_v0, map_v0.
  revert n.
  induction vs as [ | v vs' IHvs'].
  - intros n H_length_v0_aux.
    rewrite -> (fold_unfold_map_v0_aux_nil V W f).
    rewrite -> (fold_unfold_length_v0_aux_nil W).
    rewrite -> (fold_unfold_length_v0_aux_nil V) in H_length_v0_aux.
    exact (H_length_v0_aux).
  - intro n.
    rewrite -> (fold_unfold_map_v0_aux_cons V W f v vs').
    rewrite -> (fold_unfold_length_v0_aux_cons V v vs').
    rewrite -> (fold_unfold_length_v0_aux_cons W (f v) (map_v0_aux V W f vs')).
    Search (S _ = _).
Abort.
    
    
(*
   g. do map and append commute with each other and if so how?
 *)

Lemma append_aux_and_map_aux_commute_with_each_other :
  forall (V W : Type)
         (f : V -> W)
         (v1s v2s : list V),
    map_v0_aux V W f (append_v0_aux V v1s v2s) = append_v0_aux W (map_v0_aux V W f v1s) (map_v0_aux V W f v2s).
Proof.
  intros V W f v1s v2s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - rewrite -> (fold_unfold_append_v0_aux_nil V v2s).
    rewrite -> (fold_unfold_map_v0_aux_nil V W f).
    rewrite -> (fold_unfold_append_v0_aux_nil W (map_v0_aux V W f v2s)).
    reflexivity.
  -  rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s' v2s).
     rewrite -> (fold_unfold_map_v0_aux_cons V W f v1 v1s').
     rewrite -> (fold_unfold_map_v0_aux_cons V W f v1 (append_v0_aux V v1s' v2s)).
     rewrite -> (fold_unfold_append_v0_aux_cons W (f v1) (map_v0_aux V W f v1s') (map_v0_aux V W f v2s)).
     rewrite -> IHv1s'.
     reflexivity.
Qed.

Proposition append_and_map_commute_with_each_other :
  forall (V W : Type)
         (f : V -> W)
         (v1s v2s : list V),
    map_v0 V W f (append_v0 V v1s v2s) = append_v0 W (map_v0 V W f v1s) (map_v0 V W f v2s).
Proof.
  unfold map_v0, append_v0.
  exact append_aux_and_map_aux_commute_with_each_other.
Qed.


(*
   h. do map and reverse commute with each other and if so how?
 *)

Proposition reverse_and_map_commute_with_each_other :
  forall (V W : Type)
         (f : V -> W)
         (vs : list V),
    map_v0 V W f (reverse_v0 V vs) = reverse_v0 W (map_v0 V W f vs).
Proof.
  intros V W f vs.
  unfold map_v0, reverse_v0.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_map_v0_aux_nil V W f).
    rewrite -> (fold_unfold_reverse_v0_aux_nil W).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v0_aux_cons V v vs').
    rewrite -> (fold_unfold_map_v0_aux_cons V W f v vs').
    rewrite -> (fold_unfold_reverse_v0_aux_cons W (f v) (map_v0_aux V W f vs')).
    rewrite -> (append_aux_and_map_aux_commute_with_each_other V W f (reverse_v0_aux V vs') (v :: nil)).
    rewrite -> IHvs'.
    rewrite -> (fold_unfold_map_v0_aux_cons V W f v nil).
    rewrite -> (fold_unfold_map_v0_aux_nil V W f).
    reflexivity.
Qed.

(*
   i. define a unit-test function for map and verify that your implementation satisfies it
*)


Definition test_map (candidate : forall V W : Type, (V -> W) -> (list V) -> list W) :=
  (eqb_list nat beq_nat (candidate nat nat (fun v => v)
                                   nil)
            nil)
  &&
  (eqb_list bool eqb (candidate bool bool (fun v => v)
                                nil)
            nil)
  &&
  (eqb_list nat beq_nat (candidate nat nat (fun v => v)
                                   (1 :: 2 :: nil))
            (1 :: 2 :: nil))
  &&
  (eqb_list bool eqb (candidate bool bool (fun v => v)
                                (true :: false :: nil))
            (true :: false :: nil))
  &&
  (eqb_list nat beq_nat (candidate nat nat (fun v => S v)
                                   (0 :: 1 :: 2 :: nil))
            (1 :: 2 :: 3 :: nil))
  &&
  (eqb_list bool eqb (candidate bool bool (fun v => negb v)
                                (true :: false :: nil))
            (false :: true :: nil))
  &&
  (eqb_list nat beq_nat (candidate nat nat (fun v => v * 3)
                                   (0 :: 1 :: 2 :: nil))
            (0 :: 3 :: 6 :: nil))
  &&
  (eqb_list nat beq_nat (candidate nat nat (fun v => v * v)
                                   (5 :: 4 :: 3 :: nil))
            (25 :: 16 :: 9 :: nil))
  &&
  (eqb_list nat beq_nat (candidate (list nat) nat (fun vs => length_v0 nat vs)
                                   (nil :: (1 :: nil) :: (2 :: 1 :: nil) :: (3 :: 2 :: 1 :: nil) :: nil))
            (0 :: 1 :: 2 :: 3 :: nil))
  &&
  (eqb_list (list nat) (eqb_list nat beq_nat) (candidate (list nat) (list nat) (fun vs => 4 :: vs)
                                   (nil :: (1 :: nil) :: (2 :: 1 :: nil) :: (3 :: 2 :: 1 :: nil) :: nil))
            ((4 :: nil) :: (4 :: 1 :: nil) :: (4 :: 2 :: 1 :: nil) :: (4 :: 3 :: 2 :: 1 :: nil) :: nil)).
  
Compute (test_map map_v0).


(* ********** *)

(* A study of the polymorphic fold-right and fold-left functions: *)

Definition specification_of_list_fold_right (list_fold_right : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     list_fold_right V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     list_fold_right V W nil_case cons_case (v :: vs') =
     cons_case v (list_fold_right V W nil_case cons_case vs')).

Definition specification_of_list_fold_left (list_fold_left : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     list_fold_left V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     list_fold_left V W nil_case cons_case (v :: vs') =
     list_fold_left V W (cons_case v nil_case) cons_case vs').

(* Exercise 7:

   a. implement the fold-right function in direct style
*)

Fixpoint list_fold_right_aux (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    cons_case v (list_fold_right_aux V W nil_case cons_case vs')
  end.

Definition list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  list_fold_right_aux V W nil_case cons_case vs.

(*
   b. implement the fold-left function in direct style
*)

Fixpoint list_fold_left_aux (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    list_fold_left_aux V W (cons_case v nil_case) cons_case vs'
  end.

Definition list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  list_fold_left_aux V W nil_case cons_case vs.

(*
   c. state the fold-unfold lemmas associated to list_fold_right and to list_fold_left
 *)

Lemma fold_unfold_list_fold_right_aux_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_right_aux V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_right_aux.
Qed.

Lemma fold_unfold_list_fold_right_aux_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_right_aux V W nil_case cons_case (v :: vs') =
    cons_case v (list_fold_right_aux V W nil_case cons_case vs').
Proof.
  fold_unfold_tactic list_fold_right_aux.
Qed.

Lemma fold_unfold_list_fold_left_aux_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_left_aux V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_left_aux.
Qed.

Lemma fold_unfold_list_fold_left_aux_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_left_aux V W nil_case cons_case (v :: vs') =
    list_fold_left_aux V W (cons_case v nil_case) cons_case vs'.
Proof.
  fold_unfold_tactic list_fold_left_aux.
Qed.


(*
   d. prove that each of your implementations satisfies the corresponding specification
 *)

Theorem list_fold_right_satisfies_the_specification_of_list_fold_right :
  specification_of_list_fold_right list_fold_right.
Proof.
  unfold specification_of_list_fold_right, list_fold_right.
  split.
  - exact fold_unfold_list_fold_right_aux_nil.
  - exact fold_unfold_list_fold_right_aux_cons.
Qed.

Theorem list_fold_left_satisfies_the_specification_of_list_fold_left :
  specification_of_list_fold_left list_fold_left.
Proof.
  unfold specification_of_list_fold_left, list_fold_left.
  split.
  - exact fold_unfold_list_fold_left_aux_nil.
  - exact fold_unfold_list_fold_left_aux_cons.
Qed.

(*
   e. which function do foo and bar (defined just below) compute?
*)


Definition foo (V : Type) (vs : list V) :=
  list_fold_right V (list V) nil (fun v vs => v :: vs) vs.

Compute (test_copy foo).

Theorem foo_satisfies_the_specification_of_copy :
  specification_of_copy foo.
Proof.
  unfold specification_of_copy, foo.
  unfold list_fold_right.
  split.
  - intros V.
    exact (fold_unfold_list_fold_right_aux_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
  - intros V v vs'.
    exact (fold_unfold_list_fold_right_aux_cons V (list V) nil (fun (v : V) (vs : list V) => v :: vs) v vs').
Qed.

Definition bar (V : Type) (vs : list V) :=
  list_fold_left V (list V) nil (fun v vs => v :: vs) vs.

Compute (test_reverse bar).

Lemma eureka_lemma_bar_satisfies_the_specification_of_reverse :
  forall (V : Type)
         (nil_case vs' : list V),
  list_fold_left_aux V (list V) (nil_case) (fun (v0 : V) (vs : list V) => v0 :: vs) vs' =
  append_v0_aux V (list_fold_left_aux V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs') (nil_case).
Proof.
  intros V nil_case vs'.
  revert nil_case.
  induction vs' as [ | v' vs'' IHvs''].
  - intro nil_case.
    rewrite -> (fold_unfold_list_fold_left_aux_nil V (list V) nil_case (fun (v0 : V) (vs : list V) => v0 :: vs)).
    rewrite -> (fold_unfold_list_fold_left_aux_nil V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs)).
    rewrite -> (fold_unfold_append_v0_aux_nil V nil_case).
    reflexivity.
  - intro nil_case.
    rewrite -> (fold_unfold_list_fold_left_aux_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v' vs'').
    rewrite -> (fold_unfold_list_fold_left_aux_cons V (list V) nil_case (fun (v0 : V) (vs : list V) => v0 :: vs) v' vs'').
    rewrite -> (IHvs'' (v' :: nil_case)).
    rewrite -> (IHvs'' (v' :: nil)).
    Check (append_v0_aux_is_associative V (list_fold_left_aux V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs'') (v' :: nil) nil_case).
    rewrite <- (append_v0_aux_is_associative V (list_fold_left_aux V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs'') (v' :: nil) nil_case).
    unfold append_v0.
    rewrite -> (fold_unfold_append_v0_aux_cons V v' nil nil_case).
    rewrite -> (fold_unfold_append_v0_aux_nil V nil_case).
    reflexivity.
Qed.    
      
Theorem bar_satisfies_the_specification_of_reverse :
  specification_of_reverse bar.
Proof.
  unfold specification_of_reverse, bar.
  unfold list_fold_left.
  intros append H_append.
  split.
  - intros V.
    exact (fold_unfold_list_fold_left_aux_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
  - intros V v vs'.
    rewrite -> (fold_unfold_list_fold_left_aux_cons V (list V) nil (fun (v : V) (vs : list V) => v :: vs) v vs').
    rewrite <- (there_is_at_most_one_append_function V append_v0 append append_v0_satisfies_the_specification_of_append H_append (list_fold_left_aux V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs') (v :: nil)).
    Check (eureka_lemma_bar_satisfies_the_specification_of_reverse V (v :: nil) vs').
    exact (eureka_lemma_bar_satisfies_the_specification_of_reverse V (v :: nil) vs').
Qed.

(*
   f. implement length using either list_fold_right or list_fold_left, and justify your choice
 *)

Definition length_v2 (V : Type) (vs : list V) : nat :=
  list_fold_right V nat 0 (fun _ n => S n) vs.

Compute (test_length length_v2).

Theorem length_v2_satisfies_the_specification_of_length :
  specification_of_length length_v2.
Proof.
  unfold specification_of_length, length_v2.
  unfold list_fold_right.
  split.
  - intro V.
    exact (fold_unfold_list_fold_right_aux_nil V nat 0 (fun (_ : V) (n : nat) => S n)).
  - intros V v vs'.
    exact (fold_unfold_list_fold_right_aux_cons V nat 0 (fun (_ : V) (n : nat) => S n) v vs').
Qed.

Definition length_v3 (V : Type) (vs : list V) : nat :=
  list_fold_left V nat 0 (fun _ n => S n) vs.

Compute (test_length length_v3).


Lemma eureka_lemma_length_v3_satisfies_the_specification_of_length :
  forall (V : Type)
         (n : nat)
         (vs' : list V),
    list_fold_left_aux V nat (S n) (fun (_ : V) (n : nat) => S n) vs' =
    S (list_fold_left_aux V nat n (fun (_ : V) (n : nat) => S n) vs').
Proof.
  intros V n vs'.
  revert n.
  induction vs' as [ | v' vs'' IHvs''].
  - intro n.
    rewrite -> (fold_unfold_list_fold_left_aux_nil V nat (S n) (fun (_ : V) (n : nat) => S n)).
    rewrite -> (fold_unfold_list_fold_left_aux_nil V nat n (fun (_ : V) (n : nat) => S n)).
    reflexivity.
  - intro n.
    rewrite -> (fold_unfold_list_fold_left_aux_cons V nat (S n) (fun (_ : V) (n : nat) => S n) v' vs'').
    rewrite -> (fold_unfold_list_fold_left_aux_cons V nat n (fun (_ : V) (n : nat) => S n) v' vs'').
    rewrite -> (IHvs'' (S n)).
    reflexivity.
Qed.

Theorem length_v3_satisfies_the_specification_of_length :
  specification_of_length length_v3.
Proof.
  unfold specification_of_length, length_v3.
  unfold list_fold_left.
  split.
  - intro V.
    exact (fold_unfold_list_fold_left_aux_nil V nat 0 (fun (_ : V) (n : nat) => S n)).
  - intros V v vs'.
    rewrite -> (fold_unfold_list_fold_left_aux_cons V nat 0 (fun (_ : V) (n : nat) => S n) v vs').
    Check (eureka_lemma_length_v3_satisfies_the_specification_of_length V 0 vs').
    exact (eureka_lemma_length_v3_satisfies_the_specification_of_length V 0 vs').
Qed.    


(*
   g. implement copy using either list_fold_right or list_fold_left, and justify your choice
 *)

(* foo already implements copy *)

(*
   h. implement append using either list_fold_right or list_fold_left, and justify your choice
 *)

Definition append_v1 (V : Type) (v1s v2s : list V) : list V :=
  list_fold_right V (list V) v2s (fun v vs => v :: vs) v1s.

Compute (test_append append_v1).

Theorem append_v1_satisfies_the_specification_of_append :
  specification_of_append append_v1.
Proof.
  unfold specification_of_append, append_v1.
  unfold list_fold_right.
  split.
  - intros V v2s.
    exact (fold_unfold_list_fold_right_aux_nil V (list V) v2s (fun (v : V) (vs : list V) => v :: vs)).
  - intros V v1 v1s' v2s.
    exact (fold_unfold_list_fold_right_aux_cons V (list V) v2s (fun (v : V) (vs : list V) => v :: vs) v1 v1s').
Qed.

(*
   i. implement reverse using either list_fold_right or list_fold_left, and justify your choice
 *)

(* bar already implements reverse *)

(*
   j. implement map using either list_fold_right or list_fold_left, and justify your choice
 *)

Definition map_v1 (V W : Type) (f : V -> W) (vs : list V) : list W :=
  list_fold_right V (list W) nil (fun v ws => f v :: ws) vs.

Compute (test_map map_v1).

Theorem map_v1_satisfies_the_specification_of_map :
  specification_of_map map_v1.
Proof.
  unfold specification_of_map, map_v1.
  unfold list_fold_right.
  split.
  - intros V W f.
    exact (fold_unfold_list_fold_right_aux_nil V (list W) nil (fun (v : V) (ws : list W) => f v :: ws)).
  - intros V W f v vs'.
    exact (fold_unfold_list_fold_right_aux_cons V (list W) nil (fun (v : V) (ws : list W) => f v :: ws) v vs').
Qed.

(*
   k. relate list_fold_right and list_fold_left using reverse
 *)

Theorem relate :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (vs : list V),
    list_fold_right V W nil_case cons_case vs = list_fold_left V W nil_case cons_case (reverse_v0 V vs).
Proof.
  intros V W nil_case cons_case vs.
  unfold list_fold_right, list_fold_left, reverse_v0.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_list_fold_left_aux_nil V W nil_case cons_case).
    exact (fold_unfold_list_fold_right_aux_nil V W nil_case cons_case).
  - rewrite -> (fold_unfold_reverse_v0_aux_cons V v vs').
    rewrite -> (fold_unfold_list_fold_right_aux_cons V W nil_case cons_case v vs').
    rewrite -> IHvs'.
Abort.
    
Theorem relate2 :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (vs : list V),
    list_fold_right V W nil_case cons_case (reverse_v0 V vs) = list_fold_left V W nil_case cons_case vs.
Proof.
  intros V W nil_case cons_case vs.
  unfold list_fold_right, list_fold_left, reverse_v0.
  revert nil_case.
  induction vs as [ | v vs' IHvs'].
  - intro nil_case.
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_list_fold_left_aux_nil V W nil_case cons_case).
    exact (fold_unfold_list_fold_right_aux_nil V W nil_case cons_case).
  - intro nil_case.
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v vs').
    rewrite -> (fold_unfold_list_fold_left_aux_cons V W nil_case cons_case v vs').
    rewrite <- (IHvs' (cons_case v nil_case)).
Abort.    
(*
   l. implement list_fold_right using list_fold_left, without using reverse
 *)

(*
   m. implement list_fold_left using list_fold_right, without using reverse
*)

Definition is_left_permutative (V W : Type) (op2 : V -> W -> W) :=
  forall (v1 v2 : V)
         (v3 : W),
    op2 v1 (op2 v2 v3) = op2 v2 (op2 v1 v3).

(*
   n. show that
      if the cons case is a function that is left permutative,
      applying list_fold_left and applying list_fold_right
      to a nil case, this cons case, and a list
      give the same result
*)

Lemma eureka_lemma_the_grand_finale :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    is_left_permutative V W cons_case ->
    forall (nil_case : W)
           (v : V)
           (vs' : list V),
      list_fold_right_aux V W (cons_case v nil_case) cons_case vs' =
      cons_case v (list_fold_right_aux V W nil_case cons_case vs').
Proof.
  intros V W cons_case H_is_left_permutative nil_case v vs'.
  induction vs' as [ | v' vs'' IHvs'' ].
  - rewrite -> (fold_unfold_list_fold_right_aux_nil V W (cons_case v nil_case) cons_case).
    rewrite -> (fold_unfold_list_fold_right_aux_nil V W nil_case cons_case).
    reflexivity.
  - rewrite -> (fold_unfold_list_fold_right_aux_cons V W (cons_case v nil_case) cons_case v' vs'').
    rewrite -> (fold_unfold_list_fold_right_aux_cons V W nil_case cons_case v' vs'').
    unfold is_left_permutative in H_is_left_permutative.
    rewrite -> (H_is_left_permutative v v' (list_fold_right_aux V W nil_case cons_case vs'')).
    rewrite -> IHvs''.
    reflexivity.
Qed.

Theorem the_grand_finale :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    is_left_permutative V W cons_case ->
    forall (nil_case : W)
           (vs : list V),
      list_fold_left  V W nil_case cons_case vs =
      list_fold_right V W nil_case cons_case vs.
Proof.
  intros V W cons_case H_is_left_permutative nil_case vs.
  revert nil_case.
  unfold list_fold_left, list_fold_right.
  induction vs as [ | v vs' IHvs' ].
  - intro nil_case.
    rewrite -> (fold_unfold_list_fold_right_aux_nil V W nil_case cons_case).
    exact (fold_unfold_list_fold_left_aux_nil V W nil_case cons_case).
  - intro nil_case.
    rewrite -> (fold_unfold_list_fold_left_aux_cons V W nil_case cons_case v vs').
    rewrite -> (fold_unfold_list_fold_right_aux_cons V W nil_case cons_case v vs').
    rewrite -> (IHvs' (cons_case v nil_case)).
    exact (eureka_lemma_the_grand_finale V W cons_case H_is_left_permutative nil_case v vs').
Qed.

(*
   o. can you think of corollaries of this property?
*)

Lemma plus_is_left_permutative :
  is_left_permutative nat nat plus.
Proof.
  unfold is_left_permutative.
  Search (_ + (_ + _) = _ + (_ + _)).
  exact Nat.add_shuffle3.
Qed.

Corollary example_for_plus :
  forall ns : list nat,
    list_fold_left nat nat 0 plus ns = list_fold_right nat nat 0 plus ns.
Proof.
  Check (the_grand_finale nat nat plus plus_is_left_permutative 0).
  exact (the_grand_finale nat nat plus plus_is_left_permutative 0).
Qed.

Lemma mult_is_left_permutative :
  is_left_permutative nat nat mult.
Proof.
  unfold is_left_permutative.
  Search (_ * (_ * _) = _ * (_ * _)).
  exact Nat.mul_shuffle3.
Qed.

Corollary example_for_mult :
  forall ns : list nat,
    list_fold_left nat nat 1 mult ns = list_fold_right nat nat 1 mult ns.
Proof.
  Check (the_grand_finale nat nat mult mult_is_left_permutative 1).
  exact (the_grand_finale nat nat mult mult_is_left_permutative 1).
Qed.

Lemma successor_of_second_argument_is_left_permutative :
  forall (V : Type),
    is_left_permutative V nat (fun _ n => S n).
Proof.
  intro V.
  unfold is_left_permutative.
  intros v1 v2 v3.
  reflexivity.
Qed.

Corollary example_for_successor_of_second_argument :
  forall (V : Type)
         (ns : list V),
    list_fold_left V nat 0 (fun _ n => S n) ns = list_fold_right V nat 0 (fun _ n => S n) ns.
Proof.
  intro V.
  Check (the_grand_finale V nat (fun _ n => S n) (successor_of_second_argument_is_left_permutative V) 0).
  exact (the_grand_finale V nat (fun _ n => S n) (successor_of_second_argument_is_left_permutative V) 0).
Qed.


(* What do you make of this corollary?
   Can you think of more such corollaries?
*)

(*
   p. subsidiary question: does the converse of Theorem the_grand_finale hold?
*)

Theorem the_grand_finale_converse :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    (forall (nil_case : W)
            (vs : list V),
        list_fold_left  V W nil_case cons_case vs =
        list_fold_right V W nil_case cons_case vs) ->
    is_left_permutative V W cons_case.
Proof.
Abort.
  


(* ********** *)

(* Exercise 8: *)

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

Definition nat_nth_alt (V : Type) (n : nat) (vs : list V) : option V :=
  nat_fold_right
    (list V -> option V)
    (fun vs =>
       match vs with
       | nil =>
         None
       | v :: vs' =>
         Some v
       end)
    (fun ih vs =>
       match vs with
       | nil =>
         None
       | v :: vs' =>
         ih vs'
       end)
    n vs.
      
Compute (test_nat_nth nat_nth_alt).

Definition nat_nth_alt' (V : Type) (n : nat) (vs : list V) : option V :=
  nat_fold_left
    (list V -> option V)
    (fun vs =>
       match vs with
       | nil =>
         None
       | v :: vs' =>
         Some v
       end)
    (fun ih vs =>
       match vs with
       | nil =>
         None
       | v :: vs' =>
         ih vs'
       end)
    n vs.
      
Compute (test_nat_nth nat_nth_alt').

Definition list_nth_alt (V : Type) (vs : list V) (n : nat) : option V :=
  list_fold_right
    V (nat -> option V)
    (fun _ => None)
    (fun v ih n =>
       match n with
       | O =>
         Some v
       | S n' =>
         ih n'
       end)
    vs n.

Compute (test_list_nth list_nth_alt).

Definition fake_list_nth (V : Type) (vs : list V) (n : nat) : option V :=
  list_fold_left
    V (nat -> option V)
    (fun _ => None)
    (fun v ih n =>
       match n with
       | O =>
         Some v
       | S n' =>
         ih n'
       end)
    vs n.

Compute (test_list_nth fake_list_nth).

(* ********** *)

(* end of midterm-project.v *)
