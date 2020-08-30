(* week-03_exercises.v *)
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

(* Exercise 1 *)

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
  intros add1 add2.
  unfold tail_recursive_specification_of_addition.
  intros [H_add1_O H_add1_S] [H_add2_O H_add2_S].
  intro x.
  induction x as [ | x' IHx'].
  - intro y.
    rewrite -> (H_add2_O y).
    exact (H_add1_O y).
  - intro y.
    rewrite -> (H_add2_S x' y).
    rewrite -> (H_add1_S x' y).
    rewrite -> (IHx'(S y)).
    reflexivity.
Qed.

(* Exercise 4 *)
Theorem the_resident_addition_function_satisfies_the_tail_recursive_specification_of_addition :
  tail_recursive_specification_of_addition Nat.add.
Proof.
  unfold tail_recursive_specification_of_addition.
  split.
  - intro y.
    Search (0 + _ = _).
    exact (plus_O_n y).
  - intros x' y.
    Search (S _ + _ = _ + S _).
    (* TODO *)
Abort.


(* Exercise 9 *)

Inductive binary_tree (V : Type) : Type :=
| Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.


Definition specification_of_mirror (mirror : forall V : Type, binary_tree V -> binary_tree V) : Prop :=
  (forall (V : Type)
          (v : V),
      mirror V (Leaf V v) =
      Leaf V v)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      mirror V (Node V t1 t2) =
      Node V (mirror V t2) (mirror V t1)).

Proposition there_is_at_most_one_mirror :
  forall mirror1 mirror2 : forall V : Type, binary_tree V -> binary_tree V,
    specification_of_mirror mirror1 ->
    specification_of_mirror mirror2 ->
    forall (V : Type)
           (t : binary_tree V),
        mirror1 V t = mirror2 V t.
Proof.
  intros mirror1 mirror2.
  unfold specification_of_mirror.
  intros [H_mirror1_Leaf H_mirror1_Node] [H_mirror2_Leaf H_mirror2_Node].
  intros V t.
  induction t as [n | t1 IHt1 t2 IHt2].
  - revert V n.
    intros V v.
    rewrite -> (H_mirror2_Leaf V).
    rewrite -> (H_mirror1_Leaf V).
    reflexivity.
  - rewrite -> (H_mirror2_Node V t1 t2).
    rewrite -> (H_mirror1_Node V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.    


Definition specification_of_number_of_leaves (number_of_leaves : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type)
          (v : V),
      number_of_leaves V (Leaf V v) =
      1)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      number_of_leaves V (Node V t1 t2) =
      number_of_leaves V t1 + number_of_leaves V t2).

Proposition there_is_at_most_one_number_of_leaves :
  forall leaves1 leaves2 : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_leaves leaves1 ->
    specification_of_number_of_leaves leaves2 ->
    forall (V: Type)
           (t : binary_tree V),
      leaves1 V t = leaves2 V t.
Proof.
  intros leaves1 leaves2.
  unfold specification_of_number_of_leaves.
  intros [H_leaves1_Leaf H_leaves1_Node] [H_leaves2_Leaf H_leaves2_Node].
  intros V t.
  induction t as [n | t1 IHt1 t2 IHt2].
  - revert V n.
    intros V v.
    rewrite -> (H_leaves2_Leaf V).
    rewrite -> (H_leaves1_Leaf V).
    reflexivity.
  - rewrite -> (H_leaves2_Node V t1 t2).
    rewrite -> (H_leaves1_Node V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.

Definition specification_of_number_of_nodes (number_of_nodes : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type)
          (v : V),
      number_of_nodes V (Leaf V v) =
      0)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      number_of_nodes V (Node V t1 t2) =
      S (number_of_nodes V t1 + number_of_nodes V t2)).

Proposition there_is_at_most_one_number_of_nodes :
  forall nodes1 nodes2 : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_nodes nodes1 ->
    specification_of_number_of_nodes nodes2 ->
    forall (V : Type)
           (t : binary_tree V),
      nodes1 V t = nodes2 V t.
Proof.
  intros nodes1 nodes2.
  unfold specification_of_number_of_nodes.
  intros [H_nodes1_Leaf H_nodes1_Node] [H_nodes2_Leaf H_nodes2_Node].
  intros V t.
  induction t as [n | t1 IHt1 t2 IHt2].
  - revert V n.
    intros V v.
    rewrite -> (H_nodes2_Leaf V).
    rewrite -> (H_nodes1_Leaf V).
    reflexivity.
  - rewrite -> (H_nodes2_Node V t1 t2).
    rewrite -> (H_nodes1_Node V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.

(* end of week-03_exercises.v *)