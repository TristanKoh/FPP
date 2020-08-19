
Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Definition beq_bool (A B: bool) : bool :=
  match A with
  | true =>
    match B with
    | true =>
      true
    | false =>
      false
    end
  | false =>
    match B with
    | true =>
      false
    | false =>
      true
    end
  end.
  
Notation "A =b= B" :=
  (beq_bool A B) (at level 70, right associativity).

Inductive binary_tree :=
| Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.


Fixpoint beq_binary_tree (t1 t2 : binary_tree) : bool :=
  match t1 with
    Leaf n1 =>
    match t2 with
      Leaf n2 =>
      n1 =n= n2
    | Node t21 t22 =>
      false
    end
  | Node t11 t12 =>
    match t2 with
      Leaf n2 =>
      false
    | Node t21 t22 =>
      (beq_binary_tree t11 t21) && (beq_binary_tree t12 t22)
    end
  end.

Notation "A =bt= B" :=
  (beq_binary_tree A B) (at level 70, right associativity).


(* Exercise 2 *)


(* Number of nodes of a tree *)

(* Unit test *)

Definition test_number_of_nodes (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 10) =n= 0)
  &&
  (candidate (Node (Leaf 10)
                   (Leaf 20)) =n= 1)
  &&
  (candidate (Node (Leaf 10)
                   (Node (Leaf 20)
                         (Leaf 30))) =n= 2)
  &&
  (candidate (Node (Node (Leaf 10)
                            (Leaf 20))
                   (Leaf 30)) =n= 2)
  &&
  (candidate (Node (Node (Node (Leaf 30)
                               (Leaf 31))
                         (Leaf 20))
                   (Node (Leaf 21)
                         (Node (Leaf 32)
                               (Leaf 33))))
   =n= 5)
  &&
  (candidate (Node (Node (Node (Leaf 30)
                               (Node (Leaf 40)
                                     (Leaf 41)))
                         (Leaf 20))
                   (Node (Leaf 21)
                         (Node (Leaf 31)
                               (Leaf 21))))
   =n= 6).


(* Definition *)

Fixpoint number_of_nodes (t : binary_tree) : nat :=
  match t with
  | Leaf n =>
    0
  | Node t1 t2 =>
    S ((number_of_nodes t1) + (number_of_nodes t2))
  end.

Compute (test_number_of_nodes number_of_nodes).



(* Smallest leaf *)

(* Unit test *)
Definition test_smallest_leaf (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 10) =n= 10)
  &&
  (candidate (Node (Leaf 10)
                   (Leaf 20)) =n= 10)
  &&
  (candidate (Node (Leaf 10)
                   (Node (Leaf 20)
                         (Leaf 30))) =n= 10)
  &&
  (candidate (Node (Node (Leaf 20)
                            (Leaf 20))
                   (Leaf 30)) =n= 20)
  &&
  (candidate (Node (Node (Leaf 30)
                            (Leaf 40))
                   (Leaf 100)) =n= 30).


(* Function *)

Fixpoint smallest_leaf (t: binary_tree) : nat :=
  match t with
  | Leaf n => n
  | Node t1 t2 =>
    min (smallest_leaf t1) (smallest_leaf t2)
  end.

Compute (test_smallest_leaf smallest_leaf).


(* Weight of binary tree - Sum of integers in the leaves *)

Definition test_weight (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 10) =n= 10)
  &&
  (candidate (Node (Leaf 10)
                   (Leaf 20)) =n= 30)
  &&
  (candidate (Node (Leaf 10)
                   (Node (Leaf 20)
                         (Leaf 30))) =n= 60)
  &&
  (candidate (Node (Node (Leaf 10)
                            (Leaf 20))
                   (Leaf 30)) =n= 60)
  &&
  (candidate (Node (Node (Leaf 20)
                            (Leaf 20))
                   (Leaf 100)) =n= 140).

Fixpoint weight (t: binary_tree) : nat :=
  match t with
  | Leaf n =>
    n
  | Node t1 t2 =>
    (weight t1) + (weight t2)
  end.

Compute (test_weight weight).



(* Height of binary tree *)

(* Unit test *)

Definition test_height (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 10)
   =n= 0)
  &&
  (candidate (Node (Leaf 10)
                   (Leaf 20))
   =n= 1)
  &&
  (candidate (Node (Leaf 10)
                   (Node (Leaf 20)
                         (Leaf 30)))
   =n= 2)
  &&
  (candidate (Node (Leaf 10)
                   (Node (Leaf 20)
                         (Node (Leaf 30)
                               (Leaf 31))))
   =n= 3)
  &&
  (candidate (Node (Node (Node (Leaf 30)
                               (Leaf 31))
                         (Leaf 20))
                   (Node (Leaf 21)
                         (Node (Leaf 32)
                               (Leaf 33))))
   =n= 3)
  &&
  (candidate (Node (Node (Node (Leaf 30)
                               (Node (Leaf 40)
                                     (Leaf 41)))
                         (Leaf 20))
                   (Node (Leaf 21)
                         (Node (Leaf 31)
                               (Leaf 21))))
   =n= 4)
  &&
  (candidate (Node (Leaf 10)
                   (Node (Leaf 20)
                         (Node (Leaf 30)
                               (Node (Leaf 40)
                                     (Node (Leaf 50)
                                           (Node (Leaf 60)
                                                 (Node (Leaf 70)
                                                       (Leaf 71))))))))
   =n= 7).
                                    

(* Function *)

Fixpoint height (t: binary_tree) : nat :=
  match t with
  | Leaf n =>
    0
  | Node t1 t2 =>
    S(max (height t1) (height t2))
  end.

Compute (test_height height).




(* Well balancedness of a mobile *)

Definition test_well_balanced (candidate: binary_tree -> bool) : bool :=
  (candidate (Leaf 1)
   =b= true)
  &&
  (candidate (Node (Leaf 1)
                   (Leaf 1))
   =b= true)
  &&
  (candidate (Node (Leaf 1)
                   (Leaf 2))
   =b= false)
  &&
  (candidate (Node (Leaf 2)
                     (Leaf 1))
   =b= false)
  &&
  (candidate (Node (Node (Leaf 1)
                         (Leaf 1))
                   (Leaf 2))
   =b= true)
  &&
  (candidate (Node (Leaf 2)
                   (Node (Leaf 1)
                         (Leaf 1)))
   =b= true)
  &&
  (candidate (Node (Node (Leaf 2)
                         (Node (Leaf 1)
                               (Leaf 1)))
                   (Node (Node (Node (Leaf 1)
                                     (Leaf 1))
                               (Node (Leaf 1)
                                     (Leaf 1)))
                         (Leaf 6)))
   =b= false)
  &&
  (candidate (Node (Node (Leaf 4)
                         (Node (Leaf 2)
                               (Leaf 2)))
                   (Node (Node (Node (Leaf 2)
                                     (Leaf 1))
                               (Node (Leaf 1)
                                     (Leaf 2)))
                         (Leaf 6)))
   =b= false).
    

Inductive option :=
| None : option
| Some : nat -> option.


(* Function *)

(* Lambda dropped version *)

Definition well_balanced (t: binary_tree) : bool :=
  let fix visit t :=
      match t with
      | Leaf n => Some n
      | Node t1 t2 =>
        match visit t1 with
        | None => None
        | Some w1 =>
          (match visit t2 with
           | None => None
           | Some w2 =>
             if w1 =n= w2
             then Some (w1 + w2)
             else None
           end)
        end
      end
  in match visit t with
     | None => false
     | Some w => true
     end.

Compute (test_well_balanced well_balanced).


(* Lambda lifted version 

Fixpoint well_balanced (t: binary_tree) : bool :=
  match t with
  | Leaf n => Some n
  | Node t1 t2 =>
    match well_balanced t1 with
    | None => None
    | Some w1 =>
      (match well_balanced t2 with
       | None => None
       | Some w2 =>
         if w1 =n= w2
         then Some (w1 + w2)
         else None
       end)
    end
  end
    match t with
    | None => false
    | Some w => true
    end.

*)                      
                               

(* Mirror *)
Definition test_mirror (candidate: binary_tree -> binary_tree) : bool :=
  (candidate
     (Leaf 1)
   =bt= (Leaf 1))
  &&
  (candidate
     (Node (Leaf 10)
           (Leaf 20))
   =bt= (Node (Leaf 20)
           (Leaf 10)))
  &&
  (candidate
     (Node (Leaf 10)
           (Node (Leaf 20)
                 (Leaf 30)))
   =bt= (Node (Node (Leaf 30)
                 (Leaf 20))
           (Leaf 10)))
  &&
  (candidate
     (Node (Node (Leaf 10)
                 (Leaf 20))
           (Node (Leaf 30)
                 (Leaf 40)))
   =bt= (Node (Node (Leaf 40)
                 (Leaf 30))
           (Node (Leaf 20)
                 (Leaf 10)))).
                 

(* Function *)
Fixpoint mirror (t: binary_tree) : binary_tree :=
  match t with
  | Leaf n => Leaf n
  | Node t1 t2 =>
    Node (mirror t2) (mirror t1)
  end.

Compute (test_mirror mirror).
