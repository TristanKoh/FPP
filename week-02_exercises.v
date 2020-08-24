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

Inductive polymorphic_binary_tree (V : Type) : Type :=
| PLeaf : V -> polymorphic_binary_tree V
| PNode : polymorphic_binary_tree V -> polymorphic_binary_tree V -> polymorphic_binary_tree V.

(* ********** *)

(* Exercise 1 *)


Check (PLeaf (nat * bool) (1, true) : polymorphic_binary_tree (nat * bool)).


Check (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1) : polymorphic_binary_tree (polymorphic_binary_tree nat)).


(* ********** *)

(* Exercise 2 *)

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

Definition test_eqb_binary_tree_of_nats (candidate : polymorphic_binary_tree nat -> polymorphic_binary_tree nat -> bool) :=
  (candidate (PLeaf nat 1) (PLeaf nat 1) =b= true)
  &&
  (candidate (PLeaf nat 1) (PLeaf nat 2) =b= false)
  &&
  (candidate (PLeaf nat 2) (PLeaf nat 1) =b= false)
  &&
  (candidate (PLeaf nat 3)
             (PNode nat (PLeaf nat 5) (PLeaf nat 2))
   =b= false)
  &&
  (candidate (PNode nat (PLeaf nat 5) (PLeaf nat 2))
             (PLeaf nat 1)
   =b= false)
  &&
  (candidate (PNode nat (PLeaf nat 6) (PLeaf nat 7))
             (PNode nat (PLeaf nat 6) (PLeaf nat 7))
   =b= true)
  &&
  (candidate (PNode nat (PLeaf nat 6) (PLeaf nat 7))
             (PNode nat (PLeaf nat 7) (PLeaf nat 6))
   =b= false)
  &&
  (candidate (PNode nat
                    (PNode nat (PLeaf nat 8) (PLeaf nat 9))
                    (PLeaf nat 0))
             (PNode nat
                    (PNode nat (PLeaf nat 8) (PLeaf nat 9))
                    (PLeaf nat 0))
   =b= true)
  &&
  (candidate (PNode nat
                    (PNode nat (PLeaf nat 8) (PLeaf nat 9))
                    (PLeaf nat 0))
             (PNode nat
                    (PLeaf nat 0)
                    (PNode nat (PLeaf nat 8) (PLeaf nat 9)))
   =b= false)
  &&
  (candidate (PNode nat
                    (PNode nat (PLeaf nat 8) (PLeaf nat 9))
                    (PLeaf nat 0))
             (PNode nat
                    (PNode nat (PLeaf nat 9) (PLeaf nat 8))
                    (PLeaf nat 0))
   =b= false).

Fixpoint eqb_polymorphic_binary_tree (V : Type) (eqb_V : V -> V -> bool) (t1 t2 : polymorphic_binary_tree V) : bool :=
  match t1 with
  | PLeaf _ v1 =>
    match t2 with
    | PLeaf _ v2 =>
      eqb_V v1 v2
    | PNode _ t11 t12 =>
      false
    end
  | PNode _ t11 t12 =>
    match t2 with
    | PLeaf _ v2 =>
      false
    | PNode _ t21 t22 =>
      eqb_polymorphic_binary_tree V eqb_V t11 t21
      &&
      eqb_polymorphic_binary_tree V eqb_V t12 t22
    end
  end.

Definition eqb_binary_tree_of_nats (t1 t2 : polymorphic_binary_tree nat) : bool :=
  eqb_polymorphic_binary_tree nat beq_nat t1 t2.

Compute (test_eqb_binary_tree_of_nats eqb_binary_tree_of_nats).


Definition test_beq_nat_bool (candidate : (nat * bool) -> (nat * bool) -> bool) :=
  (candidate (5, true) (5, true) =b= true)
  &&
  (candidate (5, true) (6, true) =b= false)
  &&
  (candidate (6, true) (5, true) =b= false)
  &&
  (candidate (5, true) (5, false) =b= false)
  &&
  (candidate (5, false) (5, true) =b= false)
  &&
  (candidate (456, false) (456, false) =b= true)
  &&
  (candidate (923, false) (923, false) =b= true)
  &&
  (candidate (923, false) (923, true) =b= false)
  &&
  (candidate (67, true) (67, true) =b= true)
  &&
  (candidate (67, true) (76, true) =b= false).

Definition test_eqb_binary_tree_of_nats_and_bools (candidate : polymorphic_binary_tree (nat * bool) -> polymorphic_binary_tree (nat * bool) -> bool) :=
  (candidate (PLeaf (nat * bool) (1, true))
             (PLeaf (nat * bool) (1, true))
   =b= true)
  &&
  (candidate (PLeaf (nat * bool) (1, true))
             (PLeaf (nat * bool) (2, true))
   =b= false)
  &&
  (candidate (PLeaf (nat * bool) (2, true))
             (PLeaf (nat * bool) (1, true))
   =b= false)
  &&
  (candidate (PLeaf (nat * bool) (1, false))
             (PLeaf (nat * bool) (1, true))
   =b= false)
  &&
  (candidate (PLeaf (nat * bool) (1, true))
             (PLeaf (nat * bool) (1, false))
   =b= false)
  &&
  (candidate (PLeaf (nat * bool) (1, true))
             (PNode (nat * bool)
                    (PLeaf (nat * bool) (1, true))
                    (PLeaf (nat * bool) (1, true)))
   =b= false)
  &&
  (candidate (PNode (nat * bool)
                    (PLeaf (nat * bool) (1, true))
                    (PLeaf (nat * bool) (1, true)))
             (PLeaf (nat * bool) (1, true))
   =b= false)
  &&
  (candidate (PNode (nat * bool)
                    (PLeaf (nat * bool) (42, false))
                    (PLeaf (nat * bool) (67, true)))
             (PNode (nat * bool)
                    (PLeaf (nat * bool) (42, false))
                    (PLeaf (nat * bool) (67, true)))
   =b= true)
  &&
  (candidate (PNode (nat * bool)
                    (PLeaf (nat * bool) (67, true))
                    (PLeaf (nat * bool) (42, false)))
             (PNode (nat * bool)
                    (PLeaf (nat * bool) (42, false))
                    (PLeaf (nat * bool) (67, true)))
   =b= false)
  &&
  (candidate (PNode (nat * bool)
                    (PLeaf (nat * bool) (42, false))
                    (PLeaf (nat * bool) (67, true)))
             (PNode (nat * bool)
                    (PLeaf (nat * bool) (42, false))
                    (PLeaf (nat * bool) (67, false)))
   =b= false)
  &&
  (candidate (PNode (nat * bool)
                    (PLeaf (nat * bool) (42, false))
                    (PLeaf (nat * bool) (67, true)))
             (PNode (nat * bool)
                    (PLeaf (nat * bool) (42, false))
                    (PLeaf (nat * bool) (67, true)))
   =b= true)
  &&
  (candidate (PNode (nat * bool)
                    (PNode (nat * bool)
                           (PLeaf (nat * bool) (13, true))
                           (PLeaf (nat * bool) (48, false)))
                    (PLeaf (nat * bool) (67, true)))
             (PNode (nat * bool)
                    (PLeaf (nat * bool) (13, true))
                    (PLeaf (nat * bool) (48, false)))
   =b= false)
  &&
  (candidate (PNode (nat * bool)
                    (PNode (nat * bool)
                           (PLeaf (nat * bool) (13, true))
                           (PLeaf (nat * bool) (48, false)))
                    (PLeaf (nat * bool) (67, true)))
             (PNode (nat * bool)
                    (PNode (nat * bool)
                           (PLeaf (nat * bool) (13, true))
                           (PLeaf (nat * bool) (48, false)))
                    (PLeaf (nat * bool) (67, true)))
   =b= true)
  &&
  (candidate (PNode (nat * bool)
                    (PNode (nat * bool)
                           (PLeaf (nat * bool) (14, true))
                           (PLeaf (nat * bool) (48, false)))
                    (PLeaf (nat * bool) (67, true)))
             (PNode (nat * bool)
                    (PNode (nat * bool)
                           (PLeaf (nat * bool) (13, true))
                           (PLeaf (nat * bool) (48, false)))
                    (PLeaf (nat * bool) (67, true)))
   =b= false)
  &&
  (candidate (PNode (nat * bool)
                    (PNode (nat * bool)
                           (PLeaf (nat * bool) (48, false))
                           (PLeaf (nat * bool) (13, true)))
                    (PLeaf (nat * bool) (67, true)))
             (PNode (nat * bool)
                    (PNode (nat * bool)
                           (PLeaf (nat * bool) (13, true))
                           (PLeaf (nat * bool) (48, false)))
                    (PLeaf (nat * bool) (67, true)))
   =b= false).

Definition beq_nat_bool (p1 p2 : (nat * bool)) : bool :=
  let (n1, b1) := p1 in
  let (n2, b2) := p2 in
  beq_nat n1 n2 && eqb b1 b2.

Compute (test_beq_nat_bool beq_nat_bool).

Definition eqb_binary_tree_of_nats_and_bools (t1 t2 : polymorphic_binary_tree (nat * bool)) : bool :=
  eqb_polymorphic_binary_tree (nat * bool) beq_nat_bool t1 t2.

Compute (test_eqb_binary_tree_of_nats_and_bools eqb_binary_tree_of_nats_and_bools).

Definition test_eqb_binary_tree_of_binary_trees_of_nats(candidate : polymorphic_binary_tree (polymorphic_binary_tree nat) -> polymorphic_binary_tree (polymorphic_binary_tree nat) -> bool) :=
  (candidate (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
             (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
   =b= true)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
             (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2))
   =b= false)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat) (PNode nat (PLeaf nat 5) (PLeaf nat 2)))
             (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2))
   =b= false)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2))
             (PLeaf (polymorphic_binary_tree nat) (PNode nat (PLeaf nat 5) (PLeaf nat 2)))
   =b= false)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat) (PNode nat (PLeaf nat 5) (PLeaf nat 2)))
             (PLeaf (polymorphic_binary_tree nat) (PNode nat (PLeaf nat 5) (PLeaf nat 2)))
   =b= true)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat) (PNode nat (PLeaf nat 5) (PLeaf nat 3)))
             (PLeaf (polymorphic_binary_tree nat) (PNode nat (PLeaf nat 5) (PLeaf nat 2)))
   =b= false)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat) (PNode nat (PLeaf nat 5) (PLeaf nat 3)))
             (PLeaf (polymorphic_binary_tree nat) (PNode nat (PLeaf nat 3) (PLeaf nat 5)))
   =b= false)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat)
                    (PNode nat
                           (PNode nat (PLeaf nat 8) (PLeaf nat 9))
                           (PLeaf nat 0)))
             (PLeaf (polymorphic_binary_tree nat)
                    (PNode nat (PLeaf nat 5) (PLeaf nat 2)))
   =b= false)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat)
                    (PNode nat
                           (PNode nat (PLeaf nat 8) (PLeaf nat 9))
                           (PLeaf nat 0)))
             (PLeaf (polymorphic_binary_tree nat)
                    (PNode nat
                           (PNode nat (PLeaf nat 9) (PLeaf nat 8))
                           (PLeaf nat 0)))
   =b= false)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat)
                    (PNode nat
                           (PNode nat (PLeaf nat 8) (PLeaf nat 9))
                           (PLeaf nat 0)))
             (PLeaf (polymorphic_binary_tree nat)
                    (PNode nat
                           (PLeaf nat 0)
                           (PNode nat (PLeaf nat 9) (PLeaf nat 8))))
   =b= false)
  &&
  (candidate (PLeaf (polymorphic_binary_tree nat)
                    (PNode nat
                           (PNode nat (PLeaf nat 8) (PLeaf nat 9))
                           (PLeaf nat 0)))
             (PLeaf (polymorphic_binary_tree nat)
                    (PNode nat
                           (PNode nat (PLeaf nat 8) (PLeaf nat 9))
                           (PLeaf nat 0)))
   =b= true)
  &&
  (candidate (PNode (polymorphic_binary_tree nat)
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 5))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 6)))
             (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 5))
   =b= false)
  &&
  (candidate (PNode (polymorphic_binary_tree nat)
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 5))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 6)))
             (PNode (polymorphic_binary_tree nat)
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 6))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 5)))
   =b= false)
  &&
  (candidate (PNode (polymorphic_binary_tree nat)
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 5))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 6)))
             (PNode (polymorphic_binary_tree nat)
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 5))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 6)))
   =b= true)
  &&
  (candidate (PNode (polymorphic_binary_tree nat)
                    (PNode (polymorphic_binary_tree nat)
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2)))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 3)))
             (PNode (polymorphic_binary_tree nat)
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2)))
   =b= false)
  &&
  (candidate (PNode (polymorphic_binary_tree nat)
                    (PNode (polymorphic_binary_tree nat)
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2)))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 3)))
             (PNode (polymorphic_binary_tree nat)
                    (PNode (polymorphic_binary_tree nat)
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 3)))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 3)))
   =b= false)
  &&
  (candidate (PNode (polymorphic_binary_tree nat)
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 3))
                    (PNode (polymorphic_binary_tree nat)
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2))))
             (PNode (polymorphic_binary_tree nat)
                    (PNode (polymorphic_binary_tree nat)
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 3)))
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 3)))
   =b= false)
  &&
  (candidate (PNode (polymorphic_binary_tree nat)
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 3))
                    (PNode (polymorphic_binary_tree nat)
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2))))
             (PNode (polymorphic_binary_tree nat)
                    (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 3))
                    (PNode (polymorphic_binary_tree nat)
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 1))
                           (PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2))))
   =b= true).
    
Definition eqb_binary_tree_of_binary_trees_of_nats (t1 t2 : polymorphic_binary_tree (polymorphic_binary_tree nat)) : bool :=
  eqb_polymorphic_binary_tree (polymorphic_binary_tree nat) eqb_binary_tree_of_nats t1 t2.

Compute (test_eqb_binary_tree_of_binary_trees_of_nats eqb_binary_tree_of_binary_trees_of_nats).

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
