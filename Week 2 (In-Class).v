Require Import Arith Bool.

(* We need to explicitly declare the type of the inputs *)

Definition identity (V: Type) (v: V) : V :=
  v.
Check identity.

Definition make_pair (X Y : Type) (x : X) (y : Y) : X * Y :=
  (x, y).
Check make_pair.

Definition make_triple (X Y Z : Type) (x : X) (y : Y) (z : Z) : X * Y * Z :=
  (x, y, z).
Check make_triple.


(* This shows that it associates to the right *)
Check (1, 2, 3).
Check ((1, (2, 3)), ((1, 2), 3)).
Check ((1, 2), 3).


Definition make_pair' (X Y : Type)  : X -> Y -> X * Y :=
  fun x y => (x, y).
Check make_pair'.

Definition make_pair'' : forall (X Y : Type), X -> Y -> X * Y :=
  fun X Y x y => (x, y).
Check make_pair''.


(* Polymorphic Binary Tree *)
Inductive pbt (V : Type) : Type :=
| PLeaf : V -> pbt V
| PNode : pbt V -> pbt V -> pbt V.

Check (PLeaf nat 3).
Compute (PNode (bool * nat)
               (PLeaf (bool * nat) (true, 3))
               (PLeaf (bool *nat) (false, 0))).

Fixpoint pnumber_of_leaves (V : Type) (t : pbt V) : nat :=
  match t with
  | PLeaf _ v =>
    1
  | PNode _ t1 t2 =>
    pnumber_of_leaves V t1  + pnumber_of_leaves V t2
  end.

Check pnumber_of_leaves.

Definition test_pnumber_of_leaves (candidate : forall V : Type, pbt V -> nat) :=
  (candidate nat (PLeaf nat 2) =? 1)
  &&
  (candidate bool (PLeaf bool true) =? 1).

Compute (test_pnumber_of_leaves pnumber_of_leaves).

Definition compose (X Y Z : Type) (f : Y -> Z) (g : X -> Y) : X -> Z :=
  fun z => f (g z).
Check compose.



Search (_ + (_ + _) = (_ + _) + _).
Search ((_ + _) + _ = _ + (_ + _)).
Search (_ + 0 = _).
Check Nat.add_0_l.



Lemma m1 :
  forall A : Prop,
    A -> A.

Proof.
  intro A.
  intro H_A. (* Just a naming. Assumption that A holds. H - hypothesis *)
  exact H_A. (* State exactly *)

  Restart.

  intros A H_A.
  assumption. (* The goal is among the assumptions *)

  Restart.

  intros A H_A.
  apply H_A. (* Function is taking parameters *)
  
Qed.

Lemma m2 :
  forall A B : Prop,
    A -> B -> A. (* Given A and B, A holds *)
Proof.
  intros A B.
  intros H_A H_B.
  exact H_A.
Qed.



Lemma m3 :
  forall A B : Prop,
    A -> B -> A /\ B.
Proof.
  intros A B.
  intro H_A.
  intro H_B.
  split.
  exact H_A.
  exact H_B.

  Restart.

  intros A B.
  intros H_A H_B.
  split. 
  - exact H_A. (* Use '-' to focus on a particular subgoal, abstracting away everything else *)
  - exact H_B.

  Restart.
  intros A B.
  intros H_A H_B.
  Check (conj H_A H_B). (* Use to check *)
  exact (conj H_A H_B).

  Restart.

  intros A B.
  intros H_A H_B.
  split.
  { exact H_A. } (* Another way of focusing on subgoal *)
  (* Admitted. *) (* Should not show up in report *)

Abort. (* Give up by using abort. Also indicates that previous code is a draft *)

Lemma m4 :
  forall A B : Prop,
    A -> B -> A \/ B.
Proof.
  intros A B.
  intros H_A H_B. (* This basically just names our variables. Alternatively, just use intros with no arguments. *)
  right. (* Rmb Intro to Math Logic - When we have P. we can just write P \/ Q *)
  exact H_B.
Qed.


Lemma m5 :
  forall A B : Prop,
    A /\ B -> B /\ A.
Proof.
  intros A B.
  intro H_A_and_B.
  split.
  - destruct H_A_and_B as [H_A H_B]. (* "as [H_A H_B)" is optional but it guarantees the variables names are what we want *)
    exact H_B.
  - destruct H_A_and_B as [H_A H_B].
    exact H_A.

  Restart.

  intros A B.
  intro H_A_and_B.
  split.
  - destruct H_A_and_B as [_ H_B]. (* '_' because not required *) (* Can also use clear H_A *)
    exact H_B.
  - destruct H_A_and_B as [H_A _].
    exact H_A.

  Restart.

  intros A B.
  intro H_A_and_B.
  destruct H_A_and_B as [H_A H_B].
  split.
  exact H_B.
  exact H_A.

  Restart.

  intros A B.
  intro H_A_and_B.
  destruct H_A_and_B as [H_A H_B].
  Check (conj H_B H_A). (* Check is just useful for us to check that what we are about to type is correct *)
  exact (conj H_B H_A).
  
Qed.


Lemma m6 :
  forall A B C : Prop,
    A /\ B /\ C -> C /\ B /\ A.
Proof.
  intros A B C.
  intro H_A_and_B_and_C.
  destruct H_A_and_B_and_C as [H_A [H_B H_C]].
  Check (conj H_C (conj H_B H_A)).
  exact (conj H_C (conj H_B H_A)).

  Restart.

  intros A B C.
  intros [H_A [H_B H_C]].
  Check (conj H_C (conj H_B H_A)).
  exact (conj H_C (conj H_B H_A)).
 
Qed.

Lemma m7 :
  forall A B : Prop,
    A \/ B -> B \/ A.
Proof.
  intros A B.
  intros [H_A | H_B]. (* This creates 2 subgoals - show the left side first and then the right *)
  right. (* We show that the left side of A \/ B gets us the right side of B \/ A *)
  exact H_A.
  left. (* We show that the right side of A \/ B gets us the left side of B \/ A *)
  exact H_B.
Qed.
