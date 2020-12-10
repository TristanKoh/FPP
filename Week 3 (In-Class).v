Lemma identity :
  forall A :Prop,
    A -> A.

Proof.
  intro A.
Abort.

Lemma modus_ponens :
  forall (A B : Prop),
    A -> (A -> B) -> B.
Proof.
  intro A.
  intro B.
  intro H_A.
  intro H_A_implies_B.
  apply H_A_implies_B.
  exact H_A.
  Show Proof.
Qed.
    
Lemma modus_ponens' :
  forall (A B : Prop),
    A -> (A -> B) -> B.
Proof.
  exact (fun (A B : Prop) (H_A : A) (H_A_implies_B : A -> B) => H_A_implies_B H_A).
Qed.

Inductive binary_tree (V : Type) : Type :=
| Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

Print binary_tree.

Check binary_tree_ind.


Definition specification_of_mirror (mirror : forall V : Type, binary_tree V -> binary_tree V) : Prop :=
  (forall (V : Type) (v : V),
      mirror V (Leaf V v) = Leaf V v)
  /\
  (forall (V : Type) (t1 t2 : binary_tree V),
      mirror V (Node V t1 t2) = Node V (mirror V t2) (mirror V t1)).


Theorem mirror_is_involutory :
  forall mirror : forall V : Type, binary_tree V -> binary_tree V,
    specification_of_mirror mirror ->
    forall (V : Type)
           (t : binary_tree V),
      mirror V (mirror V t) = t.
Proof.
  intro mirror.
  unfold specification_of_mirror.
  intros [H_Leaf H_Node].
  intros V t.
  induction t as [v | t1 IHt1 t2 IHt2].
  - Check (H_Leaf V v).
    rewrite -> (H_Leaf V v).
    Check (H_Leaf V v).
    exact (H_Leaf V v).
    (*
  - revert IHt2.
    revert t2.
    revert IHt1.
    revert t1.
*)
  - Check (H_Node V t1 t2).
    rewrite -> (H_Node V t1 t2).
    Check (H_Node V (mirror V t2) (mirror V t1)).
    rewrite -> (H_Node V (mirror V t2) (mirror V t1)).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.

    Show Proof.
Qed.


Fixpoint mirror (V: Type) (t: binary_tree V) : binary_tree V :=
  match t with
  | Leaf _ v => Leaf V v
  | Node _ t1 t2 =>
    Node V (mirror V t2) (mirror V t1)
  end.

Compute (specification_of_mirror mirror).












  

Definition specification_of_number_of_leaves (number_of_leaves : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type) (v : V),
      number_of_leaves V (Leaf V v) = 1)
  /\
  (forall (V : Type) (t1 t2 : binary_tree V),
      number_of_leaves V (Node V t1 t2) = number_of_leaves V t1 + number_of_leaves V t2).

Definition specification_of_number_of_nodes (number_of_nodes : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type) (v : V),
      number_of_nodes V (Leaf V v) = 0)
  /\
  (forall (V : Type) (t1 t2 : binary_tree V),
      number_of_nodes V (Node V t1 t2) = S(number_of_nodes V t1 + number_of_nodes V t2)).

Theorem about_the_relative_number_of_leaves_and_nodes_in_a_tree :
  forall number_of_leaves : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_leaves number_of_leaves ->
    forall number_of_nodes : forall V :  Type, binary_tree V -> nat,
      specification_of_number_of_nodes number_of_nodes ->
      forall (V : Type)
             (t : binary_tree V),
        number_of_leaves V t = S (number_of_nodes V t).
Proof.
  intros number_of_leaves.
  unfold specification_of_number_of_leaves.
  intros [H_nol_Leaf H_nol_Node].
  intros number_of_nodes.
  unfold specification_of_number_of_nodes.
  intros [H_non_Leaf H_non_Node].
  intros V t.
  induction t as [v | t1 IHt1 t2 IHt2].
  - Check (H_non_Leaf V v). (* We can rewrite the other one first, thus doing exact *)
    rewrite -> (H_non_Leaf V v).
    Check (H_nol_Leaf V v).
    exact (H_nol_Leaf V v).
    
  Restart.

  (* We can delay unfolding till later when we know what we acutally need *)
  intros nol S_nol non S_non V t.
  induction t as [v | t1 IHt1 t2 IHt2].
  - unfold specification_of_number_of_leaves in S_nol.
    destruct S_nol as [H_nol_Leaf _].
    unfold specification_of_number_of_nodes in S_non.
    destruct S_non as [H_non_Leaf _].
    Check (H_nol_Leaf V v).
    rewrite -> (H_nol_Leaf V v).
    Check (H_non_Leaf V v).
    rewrite -> (H_non_Leaf V v).
    reflexivity.
  - unfold specification_of_number_of_leaves in S_nol.
    destruct S_nol as [_ H_nol_Node].
    unfold specification_of_number_of_nodes in S_non.
    destruct S_non as [_ H_non_Node].
    Check (H_nol_Node V t1 t2).
    rewrite -> (H_nol_Node V t1 t2).
    Check (H_non_Node V t1 t2).
    rewrite -> (H_non_Node V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    Search (S _ + _).
    Check (plus_Sn_m (non V t1) (S (non V t2))).
    rewrite -> (plus_Sn_m (non V t1) (S (non V t2))).
    Search (_ + S _).
    Check (plus_n_Sm (non V t1) (non V t2)).
    rewrite <- (plus_n_Sm (non V t1) (non V t2)).
    reflexivity.
Qed.


(* This is the same *)
Theorem about_the_relative_number_of_leaves_and_nodes_in_a_tree :
  forall (number_of_leaves : forall V : Type, binary_tree V -> nat)
         (number_of_nodes : forall V :  Type, binary_tree V -> nat),
    specification_of_number_of_leaves number_of_leaves ->
    specification_of_number_of_nodes number_of_nodes ->
    forall (V : Type)
           (t : binary_tree V),
      number_of_leaves V t = S (number_of_nodes V t).
Proof.
Abort.
