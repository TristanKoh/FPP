(* week-10_calder-mobiles.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 25 Oct 2020 *)

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

(* ********* *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Inductive binary_tree : Type :=
| Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.

(* ***** *)

Fixpoint weight (t : binary_tree) : nat :=
  match t with
  | Leaf n =>
    n
  | Node t1 t2 =>
    weight t1 + weight t2
  end.

Lemma fold_unfold_weight_Leaf :
  forall n : nat,
    weight (Leaf n) = n.
Proof.
  fold_unfold_tactic weight.
Qed.

Lemma fold_unfold_weight_Node :
  forall t1 t2 : binary_tree,
    weight (Node t1 t2) = weight t1 + weight t2.
Proof.
  fold_unfold_tactic weight.
Qed.

(* ***** *)

Fixpoint balancedp (t : binary_tree) : bool :=
  match t with
  | Leaf n =>
    true
  | Node t1 t2 =>
    balancedp t1 && balancedp t2 && (weight t1 =? weight t2)
  end.

Lemma fold_unfold_balancedp_Leaf :
  forall n : nat,
    balancedp (Leaf n) =
    true.
Proof.
  fold_unfold_tactic balancedp.
Qed.

Lemma fold_unfold_balancedp_Node :
  forall t1 t2 : binary_tree,
    balancedp (Node t1 t2) =
    (balancedp t1 && balancedp t2 && (weight t1 =? weight t2)).
Proof.
  fold_unfold_tactic balancedp.
Qed.

(* ********** *)

Fixpoint wb_ds_aux (t : binary_tree) : option nat :=
  match t with
  | Leaf n =>
    Some n
  | Node t1 t2 =>
    match wb_ds_aux t1 with
    | Some w1 =>
      match wb_ds_aux t2 with
      | Some w2 =>
        if beq_nat w1 w2
        then Some (w1 + w2)
        else None
      | None =>
        None
      end
    | None =>
      None
    end
  end.

Lemma fold_unfold_wb_ds_aux_Leaf :
  forall n : nat,
    wb_ds_aux (Leaf n) =
    Some n.
Proof.
  fold_unfold_tactic wb_ds_aux.
Qed.

Lemma fold_unfold_wb_ds_aux_Node :
  forall t1 t2 : binary_tree,
    wb_ds_aux (Node t1 t2) =
    match wb_ds_aux t1 with
    | Some w1 =>
      match wb_ds_aux t2 with
      | Some w2 =>
        if beq_nat w1 w2
        then Some (w1 + w2)
        else None
      | None =>
        None
      end
    | None =>
      None
    end.
Proof.
  fold_unfold_tactic wb_ds_aux.
Qed.

Definition wb_ds (t : binary_tree) : bool :=
  match wb_ds_aux t with
  | Some _ =>
    true
  | None =>
    false
  end.

(* ********** *)

Lemma soundness_of_wb_ds_aux :
  forall (t : binary_tree)
         (w : nat),
    wb_ds_aux t = Some w ->
    balancedp t = true /\ w = weight t.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2]; intros w H_aux.
  - rewrite -> fold_unfold_wb_ds_aux_Leaf in H_aux.
    injection H_aux as H_aux.
    rewrite -> fold_unfold_balancedp_Leaf.
    rewrite -> fold_unfold_weight_Leaf.
    symmetry in H_aux.
    split; [reflexivity | exact H_aux].
  - rewrite -> fold_unfold_wb_ds_aux_Node in H_aux.
    case (wb_ds_aux t1) as [w1 | ] eqn:Ht1.
    + case (wb_ds_aux t2) as [w2 | ] eqn:Ht2.
      * case (w1 =? w2) eqn:H_w1_w2.
        ** injection H_aux as H_aux.
           rewrite -> fold_unfold_balancedp_Node.
           rewrite -> fold_unfold_weight_Node.
           Check (IHt1 w1 (eq_refl (Some w1))).
           destruct (IHt1 w1 (eq_refl (Some w1))) as [Bt1 W1].
           destruct (IHt2 w2 (eq_refl (Some w2))) as [Bt2 W2].
           rewrite -> Bt1.
           rewrite -> Bt2.
           rewrite <- W1.
           rewrite <- W2.
           unfold andb.
           symmetry in H_aux.
           split; [exact H_w1_w2 | exact H_aux].
        ** discriminate H_aux.
      * discriminate H_aux.
    + discriminate H_aux.
Qed.

Theorem soundness_of_wb_ds :
  forall t : binary_tree,
    wb_ds t = true ->
    balancedp t = true.
Proof.
  intros t H_t.
  unfold wb_ds in H_t.
  case (wb_ds_aux t) as [w | ] eqn:H_aux.
  + Check (soundness_of_wb_ds_aux t w H_aux).
    destruct (soundness_of_wb_ds_aux t w H_aux) as [ly _].
    exact ly.
  + discriminate H_t.
Qed.

(* ********** *)

Lemma completeness_of_wb_ds_aux :
  forall t : binary_tree,
    (exists w : nat,
        wb_ds_aux t = Some w /\ w = weight t /\ balancedp t = true)
    \/
    (wb_ds_aux t = None /\ balancedp t = false).
Proof.
  intro t.
  induction t as [n | t1 [[w1 [Ht1 [W1 B1]]] | [Ht1 B1]] t2 [[w2 [Ht2 [W2 B2]]] | [Ht2 B2]]].
  - rewrite -> fold_unfold_wb_ds_aux_Leaf.
    rewrite -> fold_unfold_weight_Leaf.
    rewrite -> fold_unfold_balancedp_Leaf.
    left.
    exists n.
    split; [reflexivity | (split; reflexivity)].
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    rewrite -> Ht1.
    rewrite -> Ht2.
    rewrite <- W1.
    rewrite <- W2.
    rewrite -> B1.
    rewrite -> B2.
    case (w1 =? w2) eqn:H_w1_w2.
    + left.
      exists (w1 + w2).
      unfold andb.
      split; [reflexivity | (split; reflexivity)].
    + right.
      unfold andb.
      split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    rewrite -> Ht1.
    rewrite -> Ht2.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    unfold andb.
    split; reflexivity.
Qed.

Theorem completeness_of_wb_ds :
  forall t : binary_tree,
    balancedp t = true ->
    wb_ds t = true.
Proof.
  intros t H_t.
  unfold wb_ds.
  destruct (completeness_of_wb_ds_aux t) as [[w [H_aux [H_w H_b]]] | [H_aux H_b]].
  - rewrite -> H_aux.
    reflexivity.
  - rewrite -> H_t in H_b.
    discriminate H_b.
Qed.

(* ********** *)

Fixpoint balanced (t : binary_tree) : Prop :=
  match t with
  | Leaf n =>
    True
  | Node t1 t2 =>
    balanced t1 /\ balanced t2 /\ weight t1 = weight t2
  end.

Lemma fold_unfold_balanced_Leaf :
  forall n : nat,
    balanced (Leaf n) =
    True.
Proof.
  fold_unfold_tactic balanced.
Qed.

Lemma fold_unfold_balanced_Node :
  forall t1 t2 : binary_tree,
    balanced (Node t1 t2) =
    (balanced t1 /\ balanced t2 /\ weight t1 = weight t2).
Proof.
  fold_unfold_tactic balanced.
Qed.

(* ********** *)

(* Exercise 4a *)

Theorem soundness_of_balancedp :
  forall t : binary_tree,
    balancedp t = true ->
    balanced t.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].
  - intro H_balancedp.
    rewrite -> fold_unfold_balanced_Leaf.
    reflexivity.
  - intro H_balancedp.    
    rewrite -> fold_unfold_balanced_Node.
    rewrite -> fold_unfold_balancedp_Node in H_balancedp.
    Check (andb_prop).
    Check (andb_prop (balancedp t1 && balancedp t2) (weight t1 =? weight t2)). 
    assert (H_balancedp' := (andb_prop (balancedp t1 && balancedp t2) (weight t1 =? weight t2))).
    assert (H_balancedp' := (H_balancedp' H_balancedp)).
    destruct H_balancedp' as [H_balancedp_t1_and_t2 H_weight].
    Check (andb_prop (balancedp t1) (balancedp t2)).
    assert (H_balancedp_t1_and_t2' := (andb_prop (balancedp t1) (balancedp t2))).
    assert (H_balancedp_t1_and_t2' := (H_balancedp_t1_and_t2' H_balancedp_t1_and_t2)).
    destruct H_balancedp_t1_and_t2' as [H_balancedp_t1 H_balancedp_t2].
    assert (H_balanced_t1 := (IHt1 H_balancedp_t1)).
    assert (H_balanced_t2 := (IHt2 H_balancedp_t2)).
    split.
    + exact H_balanced_t1.
    + split.
      * exact H_balanced_t2.
      * Check (beq_nat_true (weight t1) (weight t2)).
        assert (H_weight' := (beq_nat_true (weight t1) (weight t2))).
        assert (H_weight' := (H_weight' H_weight)).
        exact H_weight'.
Qed.


Theorem completeness_of_balancedp :
  forall t : binary_tree,
    balanced t ->
    balancedp t = true.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].
  - intro H_balanced.
    rewrite -> fold_unfold_balancedp_Leaf.
    reflexivity.
  - intro H_balanced.
    rewrite -> fold_unfold_balancedp_Node.
    rewrite -> fold_unfold_balanced_Node in H_balanced.
    destruct H_balanced as [H_balanced_1 H_balanced_2_and_weight].
    destruct H_balanced_2_and_weight as [H_balanced_2 H_weight].
    assert (H_balancedp_t1 := (IHt1 H_balanced_1)). 
    assert (H_balancedp_t2 := (IHt2 H_balanced_2)).
    rewrite -> H_balancedp_t1.
    rewrite -> H_balancedp_t2.
    rewrite -> H_weight.
    Search (_ =? _).
    rewrite -> Nat.eqb_refl.
    reflexivity.
Qed.


(* Exercise 4b *)

Lemma eureka_lemma_True :
  forall (x : nat),
    x = x -> True.
Proof.
  intros x H_x.
  reflexivity.
Qed.

Lemma soundness_of_wb_ds_aux_prop :
  forall (t : binary_tree)
         (w : nat),
    wb_ds_aux t = Some w ->
    balanced t = True /\ w = weight t.
Proof.
  intro t.
  induction t as [w' | t1 IHt1 t2 IHt2].
  - intros w H_aux.
    split.
    -- exact (fold_unfold_balanced_Leaf w).
    -- rewrite -> (fold_unfold_weight_Leaf).
       rewrite -> (fold_unfold_wb_ds_aux_Leaf) in H_aux.
       injection H_aux as H_aux.
       symmetry.
       exact H_aux.
  - intros w H_aux.
    rewrite -> fold_unfold_wb_ds_aux_Node in H_aux.
    case (wb_ds_aux t1) as [w1 | ] eqn:Ht1.
    + case (wb_ds_aux t2) as [w2 | ] eqn:Ht2.
      * case (w1 =? w2) eqn:H_w1_w2.
        ** injection H_aux as H_aux.
           rewrite -> fold_unfold_balanced_Node.
           rewrite -> fold_unfold_weight_Node.
           Check (IHt1 w1 (eq_refl (Some w1))).
           destruct (IHt1 w1 (eq_refl (Some w1))) as [Bt1 W1].
           destruct (IHt2 w2 (eq_refl (Some w2))) as [Bt2 W2].
           rewrite -> Bt1.
           rewrite -> Bt2.
           rewrite <- W1.
           rewrite <- W2.
           unfold andb.
           symmetry in H_aux.
           Search (_ =? _).
           assert (H_w1_w2'' := (beq_nat_true w1 w2)).
           assert (H_w1_w2'' := (H_w1_w2'' H_w1_w2)).
           rewrite -> H_w1_w2''.
           split.
           *** Check (eureka_lemma_True w2).
               assert (H_True := (eureka_lemma_True w2)).

                     
           (*
           split; [exact H_w1_w2' | exact H_aux].
        ** discriminate H_aux.
      * discriminate H_aux.
    + discriminate H_aux.
    *)
Admitted.


Theorem soundness_of_wb_ds_prop :
  forall t : binary_tree,
    wb_ds t = true ->
    balanced t = True.
Proof.
  intros t H_t.
  unfold wb_ds in H_t.
  case (wb_ds_aux t) as [w | ] eqn:H_aux.
  + Check (soundness_of_wb_ds_aux_prop t w H_aux).
    destruct (soundness_of_wb_ds_aux_prop t w H_aux) as [ly _].
    exact ly.
  + discriminate H_t.
Qed.


Lemma completeness_of_wb_ds_aux_prop :
  forall t : binary_tree,
    (exists w : nat,
        wb_ds_aux t = Some w /\ w = weight t /\ balanced t = True)
    \/
    (wb_ds_aux t = None /\ balanced t = False).
Proof.
  intro t.
  induction t as [n | t1 [[w1 [Ht1 [W1 B1]]] | [Ht1 B1]] t2 [[w2 [Ht2 [W2 B2]]] | [Ht2 B2]]].
  - rewrite -> fold_unfold_wb_ds_aux_Leaf.
    rewrite -> fold_unfold_weight_Leaf.
    rewrite -> fold_unfold_balanced_Leaf.
    left.
    exists n.
    split; [reflexivity | (split; reflexivity)].
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balanced_Node.
    rewrite -> Ht1.
    rewrite -> Ht2.
    rewrite <- W1.
    rewrite <- W2.
    rewrite -> B1.
    rewrite -> B2.
    case (w1 =? w2) eqn:H_w1_w2.
    + left.
      exists (w1 + w2).
      unfold andb.
      split.
      * reflexivity.
      * split.
        ** reflexivity.
        ** Search (_ =? _).
           assert (H_w1_w2' := (beq_nat_true w1 w2)).
           assert (H_w1_w2' := (H_w1_w2' H_w1_w2)).
           rewrite -> H_w1_w2'.
           Search (_ /\ _).
           Search (_ = _).
           
      (* 
      split; [reflexivity | (split; reflexivity)].
    + right.
      unfold andb.
      split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balanced_Node.
    rewrite -> Ht1.
    rewrite -> Ht2.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balanced_Node.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balanced_Node.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    unfold andb.
    split; reflexivity.
*)
Admitted.
  

Theorem completeness_of_wb_ds_prop :
  forall t : binary_tree,
    balanced t = True ->
    wb_ds t = true.
Proof.
  intros t H_t.
  unfold wb_ds.
  destruct (completeness_of_wb_ds_aux_prop t) as [[w [H_aux [H_w H_b]]] | [H_aux H_b]].
  - rewrite -> H_aux.
    reflexivity.
  - rewrite -> H_t in H_b.
    (* 
    discriminate H_b.
*)
Abort.


(* Exercise 5 *)


Fixpoint binary_tree_fold (V : Type) (lea : nat -> V) (nod : V -> V -> V) (t : binary_tree) : V :=
  match t with
  | Leaf n =>
    lea n
  | Node t1 t2 =>
    nod (binary_tree_fold V lea nod t1)
        (binary_tree_fold V lea nod t2)
  end.

Lemma fold_unfold_binary_tree_fold_Leaf :
  forall (V : Type)
         (lea : nat -> V)
         (nod : V -> V -> V)
         (n : nat),
    binary_tree_fold V lea nod (Leaf n) =
    lea n.
Proof.
  fold_unfold_tactic binary_tree_fold.
Qed.

Lemma fold_unfold_binary_tree_fold_Node :
  forall (V : Type)
         (lea : nat -> V)
         (nod : V -> V -> V)
         (t1 t2 : binary_tree),
    binary_tree_fold V lea nod (Node t1 t2) =
    nod (binary_tree_fold V lea nod t1)
        (binary_tree_fold V lea nod t2).
Proof.
  fold_unfold_tactic binary_tree_fold.
Qed.




Definition wb_ds_aux_alt (t : binary_tree) : option nat :=
  binary_tree_fold
    (option nat)
    (fun n => Some n)
    (fun ih1 ih2 => match ih1 with
                    | Some w1 =>
                      match ih2 with
                      | Some w2 =>
                        if beq_nat w1 w2
                        then Some (w1 + w2)
                        else None
                      | None =>
                        None
                      end
                    | None =>
                      None
                    end)
    t.


Definition wb_ds_alt (t : binary_tree) : bool :=
  match wb_ds_aux_alt t with
  | Some _ =>
    true
  | None =>
    false
  end.

Lemma soundness_of_wb_ds_aux_alt :
  forall (t : binary_tree)
         (w : nat),
    wb_ds_aux_alt t = Some w ->
    balancedp t = true /\ w = weight t.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2]; intros w H_aux; unfold wb_ds_aux_alt in H_aux.
  - rewrite -> fold_unfold_binary_tree_fold_Leaf in H_aux.
    injection H_aux as H_aux.
    rewrite -> fold_unfold_balancedp_Leaf.
    rewrite -> fold_unfold_weight_Leaf.
    symmetry in H_aux.
    split; [reflexivity | exact H_aux].
  - rewrite -> fold_unfold_binary_tree_fold_Node in H_aux.
    case (wb_ds_aux_alt t1) as [w1 | ] eqn:Ht1; unfold wb_ds_aux_alt in Ht1; rewrite -> Ht1 in H_aux.
      + case (wb_ds_aux_alt t2) as [w2 | ] eqn:Ht2; unfold wb_ds_aux_alt in Ht2; rewrite -> Ht2 in H_aux.
        * case (w1 =? w2) eqn:H_w1_w2.
          ** injection H_aux as H_aux.
             rewrite -> fold_unfold_balancedp_Node.
             rewrite -> fold_unfold_weight_Node.
             Check (IHt1 w1 (eq_refl (Some w1))).
             destruct (IHt1 w1 (eq_refl (Some w1))) as [Bt1 W1].
             destruct (IHt2 w2 (eq_refl (Some w2))) as [Bt2 W2].
             rewrite -> Bt1.
             rewrite -> Bt2.
             rewrite <- W1.
             rewrite <- W2.
             unfold andb.
             symmetry in H_aux.
             split; [exact H_w1_w2 | exact H_aux].
          ** discriminate H_aux.
        * discriminate H_aux.
      + discriminate H_aux.
Qed.

Theorem soundness_of_wb_ds_alt :
  forall t : binary_tree,
    wb_ds_alt t = true ->
    balancedp t = true.
Proof.
  intros t H_t.
  unfold wb_ds_alt in H_t.
  case (wb_ds_aux_alt t) as [w | ] eqn:H_aux.
  + Check (soundness_of_wb_ds_aux_alt t w H_aux).
    destruct (soundness_of_wb_ds_aux_alt t w H_aux) as [ly _].
    exact ly.
  + discriminate H_t.
Qed.

Lemma completeness_of_wb_ds_aux_alt :
  forall t : binary_tree,
    (exists w : nat,
        wb_ds_aux_alt t = Some w /\ w = weight t /\ balancedp t = true)
    \/
    (wb_ds_aux_alt t = None /\ balancedp t = false).
Proof.
  intro t.
  induction t as [n | t1 [[w1 [Ht1 [W1 B1]]] | [Ht1 B1]] t2 [[w2 [Ht2 [W2 B2]]] | [Ht2 B2]]]; unfold wb_ds_aux_alt.
  - rewrite -> fold_unfold_binary_tree_fold_Leaf.
    rewrite -> fold_unfold_weight_Leaf.
    rewrite -> fold_unfold_balancedp_Leaf.
    left.
    exists n.
    split; [reflexivity | (split; reflexivity)].
  - rewrite -> fold_unfold_binary_tree_fold_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    unfold wb_ds_aux_alt in Ht1, Ht2.
    rewrite -> Ht1.
    rewrite -> Ht2.
    rewrite <- W1.
    rewrite <- W2.
    rewrite -> B1.
    rewrite -> B2.
    case (w1 =? w2) eqn:H_w1_w2.
    + left.
      exists (w1 + w2).
      unfold andb.
      split; [reflexivity | (split; reflexivity)].
    + right.
      unfold andb.
      split; reflexivity.
  - rewrite -> fold_unfold_binary_tree_fold_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    unfold wb_ds_aux_alt in Ht1, Ht2.
    rewrite -> Ht1.
    rewrite -> Ht2.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_binary_tree_fold_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    unfold wb_ds_aux_alt in Ht1.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_binary_tree_fold_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    unfold wb_ds_aux_alt in Ht1.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    unfold andb.
    split; reflexivity.
Qed.

Theorem completeness_of_wb_ds_alt :
  forall t : binary_tree,
    balancedp t = true ->
    wb_ds_alt t = true.
Proof.
  intros t H_t.
  unfold wb_ds_alt.
  destruct (completeness_of_wb_ds_aux_alt t) as [[w [H_aux [H_w H_b]]] | [H_aux H_b]].
  - rewrite -> H_aux.
    reflexivity.
  - rewrite -> H_t in H_b.
    discriminate H_b.
Qed.


Theorem equivalence_of_wb_ds_aux_and_wb_ds_aux_alt :
  forall t : binary_tree,
    wb_ds_aux t = wb_ds_aux_alt t.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2]; unfold wb_ds_aux_alt.
  - rewrite -> fold_unfold_wb_ds_aux_Leaf.
    rewrite -> fold_unfold_binary_tree_fold_Leaf.
    reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> IHt1.
    rewrite -> IHt2.
    rewrite -> fold_unfold_binary_tree_fold_Node.
    fold (wb_ds_aux_alt t1).
    fold (wb_ds_aux_alt t2).
    reflexivity.
Qed.


(* ********** *)

(* Exercise 6 *)

Inductive binary_tree' : Type :=
| Leaf' : nat -> binary_tree'
| Node' : binary_tree' -> nat -> binary_tree' -> binary_tree'.

(* ***** *)

Fixpoint weight' (t : binary_tree') : nat :=
  match t with
  | Leaf' n =>
    n
  | Node' t1 n t2 =>
    weight' t1 + n + weight' t2
  end.

Lemma fold_unfold_weight'_Leaf' :
  forall n : nat,
    weight' (Leaf' n) = n.
Proof.
  fold_unfold_tactic weight'.
Qed.

Lemma fold_unfold_weight'_Node' :
  forall (t1 t2 : binary_tree')
         (n : nat),
    weight' (Node' t1 n t2) = weight' t1 + n + weight' t2.
Proof.
  fold_unfold_tactic weight'.
Qed.

(* ***** *)

Fixpoint balancedp' (t : binary_tree') : bool :=
  match t with
  | Leaf' n =>
    true
  | Node' t1 n t2 =>
    balancedp' t1 && balancedp' t2 && (weight' t1 =? weight' t2)
  end.

Lemma fold_unfold_balancedp'_Leaf' :
  forall n : nat,
    balancedp' (Leaf' n) =
    true.
Proof.
  fold_unfold_tactic balancedp'.
Qed.

Lemma fold_unfold_balancedp'_Node' :
  forall (t1 t2 : binary_tree')
         (n : nat),
    balancedp' (Node' t1 n t2) =
    (balancedp' t1 && balancedp' t2 && (weight' t1 =? weight' t2)).
Proof.
  fold_unfold_tactic balancedp'.
Qed.

Fixpoint wb_ds_aux' (t : binary_tree') : option nat :=
  match t with
  | Leaf' n =>
    Some n
  | Node' t1 n t2 =>
    match wb_ds_aux' t1 with
    | Some w1 =>
      match wb_ds_aux' t2 with
      | Some w2 =>
        if beq_nat w1 w2
        then Some (w1 + n + w2)
        else None
      | None =>
        None
      end
    | None =>
      None
    end
  end.

Lemma fold_unfold_wb_ds_aux'_Leaf' :
  forall n : nat,
    wb_ds_aux' (Leaf' n) =
    Some n.
Proof.
  fold_unfold_tactic wb_ds_aux'.
Qed.

Lemma fold_unfold_wb_ds_aux'_Node' :
  forall (t1 t2 : binary_tree')
         (n : nat),
    wb_ds_aux' (Node' t1 n t2) =
    match wb_ds_aux' t1 with
    | Some w1 =>
      match wb_ds_aux' t2 with
      | Some w2 =>
        if beq_nat w1 w2
        then Some (w1 + n + w2)
        else None
      | None =>
        None
      end
    | None =>
      None
    end.
Proof.
  fold_unfold_tactic wb_ds_aux'.
Qed.

Definition wb_ds' (t : binary_tree') : bool :=
  match wb_ds_aux' t with
  | Some _ =>
    true
  | None =>
    false
  end.

(* ********** *)

Lemma soundness_of_wb_ds_aux' :
  forall (t : binary_tree')
         (w : nat),
    wb_ds_aux' t = Some w ->
    balancedp' t = true /\ w = weight' t.
Proof.
  intro t.
  induction t as [n | t1 IHt1 n t2 IHt2]; intros w H_aux.
  - rewrite -> fold_unfold_wb_ds_aux'_Leaf' in H_aux.
    injection H_aux as H_aux.
    rewrite -> fold_unfold_balancedp'_Leaf'.
    rewrite -> fold_unfold_weight'_Leaf'.
    symmetry in H_aux.
    split; [reflexivity | exact H_aux].
  - rewrite -> fold_unfold_wb_ds_aux'_Node' in H_aux.
    case (wb_ds_aux' t1) as [w1 | ] eqn:Ht1.
    + case (wb_ds_aux' t2) as [w2 | ] eqn:Ht2.
      * case (w1 =? w2) eqn:H_w1_w2.
        ** injection H_aux as H_aux.
           rewrite -> fold_unfold_balancedp'_Node'.
           rewrite -> fold_unfold_weight'_Node'.
           Check (IHt1 w1 (eq_refl (Some w1))).
           destruct (IHt1 w1 (eq_refl (Some w1))) as [Bt1 W1].
           destruct (IHt2 w2 (eq_refl (Some w2))) as [Bt2 W2].
           rewrite -> Bt1.
           rewrite -> Bt2.
           rewrite <- W1.
           rewrite <- W2.
           unfold andb.
           symmetry in H_aux.
           split; [exact H_w1_w2 | exact H_aux].
        ** discriminate H_aux.
      * discriminate H_aux.
    + discriminate H_aux.
Qed.

Theorem soundness_of_wb_ds' :
  forall t : binary_tree',
    wb_ds' t = true ->
    balancedp' t = true.
Proof.
  intros t H_t.
  unfold wb_ds' in H_t.
  case (wb_ds_aux' t) as [w | ] eqn:H_aux.
  + Check (soundness_of_wb_ds_aux' t w H_aux).
    destruct (soundness_of_wb_ds_aux' t w H_aux) as [ly _].
    exact ly.
  + discriminate H_t.
Qed.

(* ********** *)

Lemma completeness_of_wb_ds_aux' :
  forall t : binary_tree',
    (exists w : nat,
        wb_ds_aux' t = Some w /\ w = weight' t /\ balancedp' t = true)
    \/
    (wb_ds_aux' t = None /\ balancedp' t = false).
Proof.
  intro t.
  induction t as [n | t1 [[w1 [Ht1 [W1 B1]]] | [Ht1 B1]] n t2 [[w2 [Ht2 [W2 B2]]] | [Ht2 B2]]].
  - rewrite -> fold_unfold_wb_ds_aux'_Leaf'.
    rewrite -> fold_unfold_weight'_Leaf'.
    rewrite -> fold_unfold_balancedp'_Leaf'.
    left.
    exists n.
    split; [reflexivity | (split; reflexivity)].
  - rewrite -> fold_unfold_wb_ds_aux'_Node'.
    rewrite -> fold_unfold_weight'_Node'.
    rewrite -> fold_unfold_balancedp'_Node'.
    rewrite -> Ht1.
    rewrite -> Ht2.
    rewrite <- W1.
    rewrite <- W2.
    rewrite -> B1.
    rewrite -> B2.
    case (w1 =? w2) eqn:H_w1_w2.
    + left.
      exists (w1 + n + w2).
      unfold andb.
      split; [reflexivity | (split; reflexivity)].
    + right.
      unfold andb.
      split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux'_Node'.
    rewrite -> fold_unfold_weight'_Node'.
    rewrite -> fold_unfold_balancedp'_Node'.
    rewrite -> Ht1.
    rewrite -> Ht2.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux'_Node'.
    rewrite -> fold_unfold_weight'_Node'.
    rewrite -> fold_unfold_balancedp'_Node'.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux'_Node'.
    rewrite -> fold_unfold_weight'_Node'.
    rewrite -> fold_unfold_balancedp'_Node'.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    unfold andb.
    split; reflexivity.
Qed.

Theorem completeness_of_wb_ds' :
  forall t : binary_tree',
    balancedp' t = true ->
    wb_ds' t = true.
Proof.
  intros t H_t.
  unfold wb_ds'.
  destruct (completeness_of_wb_ds_aux' t) as [[w [H_aux [H_w H_b]]] | [H_aux H_b]].
  - rewrite -> H_aux.
    reflexivity.
  - rewrite -> H_t in H_b.
    discriminate H_b.
Qed.
 
 
 
 
 
 
 
(* ********** *)

(* end of week-10_calder-mobiles.v *)
