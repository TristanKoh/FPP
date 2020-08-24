(* week-02_exercises.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 23 Aug 2020 *)

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

Require Import Arith Bool.

(* ********** *)

(* Exercise 1 *)

(*
Check (... : polymorphic_binary_tree (nat * bool)).
*)

(*
Check (... : polymorphic_binary_tree (polymorphic_binary_tree nat)).
*)

(* ********** *)

(* Exercise 2 *)

(*
Definition eqb_binary_tree_of_nats_and_bools ... ... : bool :=
  ...
*)

(*
Definition eqb_binary_tree_of_binary_trees_of_nats ... ... : bool :=
  ...
*)

(* ********** *)

(* Exercises about types: *)


Definition ta : forall A : Type, A -> A * A :=
  fun A a => (a, a).

Check ta.

Definition tb : forall A B : Type, A -> B -> A * B :=
  fun A B a b => (a, b).

Check tb.

Definition tc : forall A B : Type, A -> B -> B * A :=
  fun A B a b => (b, a).

Check tc.

Check (tt : unit). 

Definition td : forall (A : Type), (unit -> A) -> A :=
  fun A a => a (tt). 

Check td.

Definition te : forall A B : Type, (A -> B) -> A -> B :=
  fun A B a b => a b.

Check te.

Definition tf : forall A B : Type, A -> (A -> B) -> B :=
  fun A B a b => b (a).

Check tf.

Definition tg : forall A B C : Type, (A -> B -> C) -> A -> B -> C :=
  fun A B C a b c => a b c.

Check tg.

Definition th : forall A B C : Type, (A -> B -> C) -> B -> A -> C :=
  fun A B C a b c => a c b.

Check th.

Definition ti : forall A B C D : Type, (A -> C) -> (B -> D) -> A -> B -> C * D :=
  fun A B C D a b c d => (a c , b d).

Check ti.

Definition tj : forall A B C : Type, (A -> B) -> (B -> C) -> A -> C :=
  fun A B C a b c => b (a c).

Definition tk : forall A B : Type, A * B -> B * A :=
  fun A B x =>
    match x with
    | (a , b) => (b , a)
    end.

Check tk.

  (* Hint: use a match expression to destructure the input pair. *)

Definition tl : forall A B C : Type, (A * B -> C) -> A -> B -> C :=
  fun A B C a b c => a (b, c).

Check tl.

Definition tm : forall A B C : Type, (A -> B -> C) -> A * B -> C :=
  fun A B C f x =>
    match x with
    | (a , b) => f a b
    end.

Check tm.

Definition tn : forall A B C : Type, (A * (B * C)) -> (A * B) * C :=
  fun A B C d =>
    match d with
    | (a , e) =>
      match e with
      | (b , c) => ((a , b) , c)
      end
    end.

Check tn.

(* ********** *)

(* Exercises about propositions: *)

Proposition pa :
  forall A : Prop,
    A -> A * A.
Proof.
  intro A.
  intro H_A.
  split.
  exact H_A.
  exact H_A.
Qed.

Proposition pb :
  forall A B : Prop,
    A -> B -> A * B.
Proof.
  intros A B.
  intros H_A H_B.
  split.
  exact H_A.
  exact H_B.
Qed.

Proposition pc :
  forall A B : Prop,
    A -> B -> B * A.
Proof.
  intros A B.
  intros H_A H_B.
  split.
  exact H_B.
  exact H_A.
Qed.

Check tt.

Proposition pd :
  forall (A : Prop),
    (unit -> A) -> A.
Proof.
  intros A H_unit_implies_A.
  exact (H_unit_implies_A tt).
Qed.


Proposition pe :
  forall A B : Prop,
    (A -> B) -> A -> B.
Proof.
  intros A B.
  intros H_A_implies_B.
  exact H_A_implies_B.
Qed.

Proposition pf :
  forall A B : Prop,
    A -> (A -> B) -> B.
Proof.
  intros A B.
  intro H_A.
  intro H_A_implies_B.
  exact (H_A_implies_B H_A).
Qed.

Proposition pg :
  forall A B C : Prop,
    (A -> B -> C) -> A -> B -> C.
Proof.
  intros A B C.
  intro H_A_implies_B_implies_C.
  intro H_A.
  exact (H_A_implies_B_implies_C H_A).
Qed.

Proposition ph :
  forall A B C : Prop,
    (A -> B -> C) -> B -> A -> C.
Proof.
  intros A B C.
  intro H_A_implies_B_implies_C.
  intro H_B.
  intro H_A.
  exact (H_A_implies_B_implies_C H_A H_B).
Qed.

Proposition pi :
  forall A B C D : Prop,
    (A -> C) -> (B -> D) -> A -> B -> C /\ D.
Proof.
  intros A B C D.
  intros H_A_implies_C H_B_implies_D.
  intros H_A H_B.
  split.
  - exact (H_A_implies_C H_A).
  - exact (H_B_implies_D H_B).  
Qed.

Proposition pj :
  forall A B C : Prop,
    (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros A B C.
  intros H_A_implies_B H_B_implies_C.
  intros H_A.
  exact (H_B_implies_C (H_A_implies_B H_A)).
Qed.

Proposition pk :
  forall A B : Prop,
    A /\ B -> B /\ A.
Proof.
  intros A B [H_A H_B].
  exact (conj H_B H_A).
Qed.

Proposition pl :
  forall A B C : Prop,
    (A /\ B -> C) -> A -> B -> C.
Proof.
  intros A B C.
  intros H_A_and_B_implies_C H_A.
  intros H_B.
  exact (H_A_and_B_implies_C (conj H_A H_B)).
Qed.

Proposition pm :
  forall A B C : Prop,
    (A -> B -> C) -> A /\ B -> C.
Proof.
  intros A B C.
  intro H_A_implies_B_implies_C.
  intro H_A_and_B.
  destruct H_A_and_B as [H_A H_B].
  exact ((H_A_implies_B_implies_C H_A) H_B).
Qed.

Proposition pn :
  forall A B C : Prop,
    (A /\ (B /\ C)) -> (A /\ B) /\ C.
Proof.
  intros A B C.
  intro H_A_and_B_and_C.
  destruct H_A_and_B_and_C as [H_A [H_B H_C]].
  split.
  - split.
    exact H_A.
    exact H_B.
  - exact H_C.
Qed.

(* ********** *)

(* end of week-02_exercises.v *)
