
Proposition two_specifications_of_addition_equivalent :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add <->
    recursive_specification_of_addition add.
Proof.
  intro add.
  unfold tail_recursive_specification_of_addition.
  unfold recursive_specification_of_addition.
  split.
  - intros [H_add1_O H_add1_S].
    split. 
    * exact H_add1_O.
    * intros x' y.
      Check (H_add1_S x' y).
      rewrite -> (H_add1_S x' y).
      induction x' as [ | x' IHx'].
      -- Check (H_add1_O (S y)).
         rewrite -> (H_add1_O (S y)).
         rewrite -> H_add1_O.
         reflexivity.
      -- Check (H_add1_S x' y).
         rewrite -> (H_add1_S x' y).
         rewrite -> IHx'.
         rewrite -> (H_add1_S x' (S y)).
         induction y as [ | y' IHy'].
(*
         induction x' as [ | x' IHx''].
         ** Check (H_add1_S 0 (S y)).
            rewrite -> (H_add1_S 0 (S y)).
            Check (H_add1_O (S (S y))).
            rewrite -> (H_add1_O (S (S y))).
            Check (H_add1_S 0 y).
            rewrite -> (H_add1_S 0 y).
            Check (H_add1_O (S y)).
            rewrite -> (H_add1_O (S y)).
            reflexivity.
         ** Check (H_add1_S (S x') (S y)).
            rewrite -> (H_add1_S (S x') (S y)).
            rewrite -> (H_add1_S x' (S (S y))).
            rewrite -> (H_add1_S (S x') y).
            rewrite -> (H_add1_S x' (S y)).
            Abort.*)


            
Abort.

Proposition recursive_addition_is_associative :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall x y z : nat,
      add (add x y) z = add x (add y z).
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  intros x y z.
  induction x as [ | x' IHx'].
  - Check (H_add_O y).
    rewrite -> (H_add_O y).
    Check (H_add_O (add y z)).
    rewrite -> (H_add_O (add y z)).
    reflexivity.
  - Check (H_add_S x' y).
    rewrite -> (H_add_S x' y).
    Check (H_add_S (add x' y) z).
    rewrite -> (H_add_S (add x' y) z).
    Check (H_add_S x' (add y z)).
    rewrite -> (H_add_S x' (add y z)).
    rewrite -> IHx'.
    reflexivity.
Qed.

Proposition tail_recursive_addition_is_associative :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall x y z : nat,
      add (add x y) z = add x (add y z).
Proof.
  intro add.
  unfold tail_recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  intros x.
  induction x as [ | x' IHx'].
  - intros y z.
    Check (H_add_O y).
    rewrite -> (H_add_O y).
    Check (H_add_O (add y z)).
    rewrite -> (H_add_O (add y z)).
    reflexivity.
  - intros y z.
    Check (H_add_S x' y).
yh    rewrite -> (H_add_S x' y).
    Check (H_add_S x' (add y z)).
    rewrite -> (H_add_S x' (add y z)).
  Restart.
  intro add.
  unfold tail_recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  intros x y z.
  induction x as [ | x' IHx'].
  - Check (H_add_O y).
    rewrite -> (H_add_O y).
    Check (H_add_O (add y z)).
    rewrite -> (H_add_O (add y z)).
    reflexivity.
  - Check (H_add_S x' y).
    rewrite -> (H_add_S x' y).
    Check (H_add_S x' (add y z)).
    rewrite -> (H_add_S x' (add y z)).
    
