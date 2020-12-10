(* week-03_induction-over-binary-trees.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 27 Aug 2020 *)

(* ********** *)

Inductive binary_tree (V : Type) : Type :=
| Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

(* ********** *)

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

(* ***** *)

Proposition there_is_at_most_one_mirror_function :
  forall mirror1 mirror2 : forall V : Type, binary_tree V -> binary_tree V,
    specification_of_mirror mirror1 ->
    specification_of_mirror mirror2 ->
    forall (V : Type)
           (t : binary_tree V),
      mirror1 V t = mirror2 V t.
Proof.
Abort.

(* ***** *)

Theorem mirror_is_involutory :
  forall mirror : forall V : Type, binary_tree V -> binary_tree V,
    specification_of_mirror mirror ->
    forall (V : Type)
           (t : binary_tree V),
      mirror V (mirror V t) = t.
Proof.
  intro mirror.
  unfold specification_of_mirror.
  intros [S_Leaf S_Node].
  intros V t.
  induction t as [ v | t1 IHt1 t2 IHt2].
  - revert V v.
    intros V v.
    Check (S_Leaf V v).
    rewrite ->  (S_Leaf V v).
    Check (S_Leaf V v).
(*
    exact (S_Leaf V v).
*)
    rewrite -> (S_Leaf V v).
    reflexivity.
  - revert IHt2.
    revert t2.
    revert IHt1.
    revert t1.
    intros t1 IHt1 t2 IHt2.
    Check (S_Node V t1 t2).
    rewrite -> (S_Node V t1 t2).
    Check (S_Node V (mirror V t2) (mirror V t1)).
    rewrite -> (S_Node V (mirror V t2) (mirror V t1)).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.

  Restart. (* now for a less verbose proof: *)

  intros mirror S_mirror V t.
  induction t as [ v | t1 IHt1 t2 IHt2].
  - unfold specification_of_mirror in S_mirror.
    destruct S_mirror as [S_Leaf _].
    Check (S_Leaf V v).
    rewrite ->  (S_Leaf V v).
    Check (S_Leaf V v).
    exact (S_Leaf V v).
  - unfold specification_of_mirror in S_mirror.
    destruct S_mirror as [_ S_Node].
    Check (S_Node V t1 t2).
    rewrite -> (S_Node V t1 t2).
    Check (S_Node V (mirror V t2) (mirror V t1)).
    rewrite -> (S_Node V (mirror V t2) (mirror V t1)).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.

(* ********** *)

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

(* ***** *)

Theorem about_the_relative_number_of_leaves_and_nodes_in_a_tree :
  forall number_of_leaves : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_leaves number_of_leaves ->
    forall number_of_nodes : forall V : Type, binary_tree V -> nat,
      specification_of_number_of_nodes number_of_nodes ->
      forall (V : Type)
             (t : binary_tree V),
        number_of_leaves V t = S (number_of_nodes V t).
Proof.
  intro number_of_leaves.
  unfold specification_of_number_of_leaves.
  intros [S_nol_Leaf S_nol_Node].
  intro number_of_nodes.
  unfold specification_of_number_of_nodes.
  intros [S_non_Leaf S_non_Node].
  
  Restart. (* with less clutter among the assumptions *)

  intros nol S_nol non S_non V t.
  induction t as [v | t1 IHt1 t2 IHt2].
  - unfold specification_of_number_of_leaves in S_nol.
    destruct S_nol as [S_nol_Leaf _].
    unfold specification_of_number_of_nodes in S_non.
    destruct S_non as [S_non_Leaf _].
    Check (S_non_Leaf V v).
    rewrite ->  (S_non_Leaf V v).
    Check (S_nol_Leaf V v).
    exact  (S_nol_Leaf V v).
  - unfold specification_of_number_of_leaves in S_nol.
    destruct S_nol as [_ S_nol_Node].
    unfold specification_of_number_of_nodes in S_non.
    destruct S_non as [_ S_non_Node].
    Check (S_nol_Node V t1 t2).
    rewrite -> (S_nol_Node V t1 t2).
    Check (S_non_Node V t1 t2).
    rewrite -> (S_non_Node V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    Search (S _ +  _).
    Check (plus_Sn_m (non V t1) (S (non V t2))).
    rewrite ->  (plus_Sn_m (non V t1) (S (non V t2))).
    Search (_ +  S _ = _).
    Search (_ = _ +  S _).
    Check (plus_n_Sm (non V t1) (non V t2)).
    rewrite <- (plus_n_Sm (non V t1) (non V t2)).
    reflexivity.
Qed.

(* ********** *)

(* end of week-03_induction-over-binary-trees.v *)

