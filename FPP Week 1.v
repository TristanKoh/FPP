
(* week-01_functional-programming-in-Coq.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 15 Aug 2020 *)

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

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

Definition test_add (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 1)
  &&
  (candidate 1 0 =n= 1)
  &&
  (candidate 1 1 =n= 2)
  &&
  (candidate 1 2 =n= 3)
  &&
  (candidate 2 1 =n= 3)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 2765 1313 =n= 4078)
  &&
  (candidate 2500 2500 =n= 5000)
  &&
  (candidate 0 5000 =n= 5000)
  &&
  (candidate 5000 0 =n= 5000)
  &&
  (candidate 1 4999 =n= 5000)
  &&
  (candidate 4999 1 =n= 5000)
  .

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => S (add_v1 i' j)
  end.

Compute (test_add add_v1).

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

Definition add_v3 (i j : nat) : nat :=
  let fix visit n :=
    match n with
      | O => j
      | S n' => S (visit n')
    end
  in visit i.

Compute (test_add add_v3).

Definition add_v4 (i j : nat) : nat :=
  let fix visit n a :=
    match n with
      | O => a
      | S n' => visit n' (S a)
    end
  in visit i j.

Compute (test_add add_v4).

(* ***** *)

(* Exercise 1 *)

Definition test_mul (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 0)
  &&
  (candidate 1 0 =n= 0)
  &&
  (candidate 1 1 =n= 1)
  &&
  (candidate 1 2 =n= 2)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  .

Fixpoint mul_v1 (i j : nat) : nat :=
  match i with
    | O => O
    | S i' => add_v4 j (mul_v1 i' j)
  end.

Compute (test_mul mul_v1).

Definition mul_v2 (i j : nat) : nat :=
  let fix visit n :=
    match n with
      | O => O
      | S n' => add_v4 j (visit n')
    end
  in visit i.

Compute (test_mul mul_v2).

Definition mul_v3 (i j : nat) : nat :=
  let fix visit n a :=
    match n with
      | O => a
      | S n' => visit n' (add_v4 j a)
    end
  in visit i O.

Compute (test_mul mul_v3).


(* ***** *)


Definition test_power (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 1)
  &&
  (candidate 0 1 =n= 0)
  &&
  (candidate 1 0 =n= 1)
  &&
  (candidate 1 1 =n= 1)
  &&
  (candidate 1 2 =n= 1)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 3 2 =n= 9)
  &&
  (candidate 2 3 =n= 8)
  &&
  (candidate 3 3 =n= 27)
  .
  
Fixpoint power_v1 (x n : nat) : nat :=
  match n with
    | O => 1
    | S n' => mul_v3 x (power_v1 x n')
  end.

Compute (test_power power_v1).

Definition power_v2 (x n : nat) : nat :=
  let fix visit i :=
    match i with
      | O => 1
      | S i' => mul_v3 x (visit i')
    end
  in visit n.

Compute (test_power power_v2).

Definition power_v3 (x n: nat) : nat :=
  let fix visit i a :=
    match i with
      | O => a
      | S i' => visit i' (mul_v3 x a)
    end
  in visit n 1.

Compute (test_power power_v3).
  

(* ***** *)

Definition test_fac (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 1)
  &&
  (candidate 1 =n= 1)
  &&
  (candidate 2 =n= 2)
  &&
  (candidate 3 =n= 6)
  &&
  (candidate 4 =n= 24)
  &&
  (candidate 5 =n= 120)
  &&
  (candidate 6 =n= 720)
  .
  
Fixpoint fac_v1 (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => mul_v3 n (fac_v1 n')
  end.

Compute (test_fac fac_v1).


Definition fac_v2 (n : nat) : nat :=
  let fix visit i :=
    match i with
      | O => 1
      | S i' => mul_v3 i (visit i')
    end
  in visit n.

Compute (test_fac fac_v2).


Definition fac_v3 (n : nat) : nat :=
  let fix visit i a :=
    match i with
      | O => a
      | S i' => visit i' (mul_v3 i a)
    end
  in visit n 1.

Compute (test_fac fac_v3).


(* ***** *)


Definition test_fib (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 0)
  &&
  (candidate 1 =n= 1)
  &&
  (candidate 2 =n= 1)
  &&
  (candidate 3 =n= 2)
  &&
  (candidate 4 =n= 3)
  &&
  (candidate 5 =n= 5)
  &&
  (candidate 6 =n= 8)
  &&
  (candidate 7 =n= 13)
  &&
  (candidate 8 =n= 21)
  &&
  (candidate 9 =n= 34)
  &&
  (candidate 10 =n= 55)
  .
  
Fixpoint fib_v1 (n : nat) : nat :=
  match n with
    | O => O
    | S n' => match n' with
                | O => 1
                | S n'' => add_v3 (fib_v1 n') (fib_v1 n'')
              end
  end.

Compute (test_fib fib_v1).

Definition fib_v2 (n : nat) : nat :=
  let fix visit n :=
      match n with
      | O => O
      | S n' => match n' with
                | O => 1
                | S n'' => add_v3 (visit n') (visit n'')
                end
      end
  in visit n.
                 
Compute (test_fib fib_v2).

Definition fib_v3 (n : nat) : nat :=
  let fix visit n f0 f1:=
      match n with
      | O => f0
      | S n' => visit n' (add_v3 f0 f1) f0
      end
  in visit n 0 1.
                 
Compute (test_fib fib_v3).
  

(* ***** *)

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).


Definition test_even (candidate: nat -> bool) : bool :=
  (candidate 0 =b= true)
  &&
  (candidate 1 =b= false)
  &&
  (candidate 2 =b= true)
  &&
  (candidate 3 =b= false)
  &&
  (candidate 4 =b= true)
  &&
  (candidate 5 =b= false)
  &&
  (candidate 6 =b= true)
  &&
  (candidate 7 =b= false)
  &&
  (candidate 8 =b= true)
  .

Fixpoint even_v1 (n : nat) : bool :=
  match n with
    | O => true
    | S n' => negb (even_v1 n')
  end.

Compute (test_even even_v1).

Definition even_v2 (n : nat) : bool :=
  let fix visit n :=
    match n with
      | O => true
      | S n' => negb (visit n')
    end
  in visit n.

Compute (test_even even_v2).

Definition even_v3 (n : nat) : bool :=
  let fix visit n a :=
    match n with
      | O => a
      | S n' => visit n' (negb a)
    end
  in visit n true.

Compute (test_even even_v3).


(* ***** *)


Definition test_odd (candidate: nat -> bool) : bool :=
  (candidate 0 =b= false)
  &&
  (candidate 1 =b= true)
  &&
  (candidate 2 =b= false)
  &&
  (candidate 3 =b= true)
  &&
  (candidate 4 =b= false)
  &&
  (candidate 5 =b= true)
  &&
  (candidate 6 =b= false)
  &&
  (candidate 7 =b= true)
  &&
  (candidate 8 =b= false)
  .

Fixpoint odd_v1 (n : nat) : bool :=
  match n with
    | O => false
    | S n' => negb (odd_v1 n')
  end.

Compute (test_odd odd_v1).

Definition odd_v2 (n : nat) : bool :=
  let fix visit n :=
    match n with
      | O => false
      | S n' => negb (visit n')
    end
  in visit n.

Compute (test_odd odd_v2).

Definition odd_v3 (n : nat) : bool :=
  let fix visit n a :=
    match n with
      | O => a
      | S n' => visit n' (negb a)
    end
  in visit n false.

Compute (test_odd odd_v3).

(* ********** *)

(* Exercise 2 *)

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


(* ********** *)

(* Exercise 3 *)

Inductive binary_tree' :=
| Leaf' : binary_tree'
| Node' : binary_tree' -> nat -> binary_tree' -> binary_tree'.

Definition test_number_of_leaves' (candidate: binary_tree' -> nat) : bool :=
  (candidate Leaf' =n= 1)
  &&
  (candidate (Node' Leaf' 42 Leaf') =n= 2)
  &&
  (candidate (Node' Leaf' 42 (Node' Leaf' 42 Leaf')) =n= 3)
  &&
  (candidate (Node' (Node' Leaf' 42 Leaf') 42 Leaf') =n= 3)
  &&
  (candidate (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf')) =n= 4)
  &&
  (candidate (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) =n= 5)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 Leaf') 42 (Node' Leaf' 42 Leaf')) =n= 5)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 Leaf') 42 (Node' (Node' Leaf' 42 Leaf') 42 Leaf')) =n= 6)
  &&
  (candidate (Node' (Node' Leaf' 42 (Node' Leaf' 42 Leaf')) 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) =n= 6)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf')) 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) =n= 7)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 Leaf') 42 (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf'))) =n= 7)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf')) 42 (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf'))) =n= 8)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) =n= 8)
  .

Fixpoint number_of_leaves'_v0 (t : binary_tree') : nat :=
  match t with
  | Leaf' => 1
  | Node' t1 n t2 => (number_of_leaves'_v0 t1) + (number_of_leaves'_v0 t2)
  end.

Compute (test_number_of_leaves' number_of_leaves'_v0).

Definition number_of_leaves'_v1 (t : binary_tree') : nat :=
  let fix visit t a :=
      match t with
      | Leaf' => S a
      | Node' t1 n t2 => visit t2 (visit t1 a)
      end
  in visit t 0.

Compute (test_number_of_leaves' number_of_leaves'_v1).
  
  
Definition test_number_of_nodes' (candidate: binary_tree' -> nat) : bool :=
  (candidate Leaf' =n= 0)
  &&
  (candidate (Node' Leaf' 42 Leaf') =n= 1)
  &&
  (candidate (Node' Leaf' 42 (Node' Leaf' 42 Leaf')) =n= 2)
  &&
  (candidate (Node' (Node' Leaf' 42 Leaf') 42 Leaf') =n= 2)
  &&
  (candidate (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf')) =n= 3)
  &&
  (candidate (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) =n= 4)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 Leaf') 42 (Node' Leaf' 42 Leaf')) =n= 4)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 Leaf') 42 (Node' (Node' Leaf' 42 Leaf') 42 Leaf')) =n= 5)
  &&
  (candidate (Node' (Node' Leaf' 42 (Node' Leaf' 42 Leaf')) 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) =n= 5)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf')) 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) =n= 6)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 Leaf') 42 (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf'))) =n= 6)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf')) 42 (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 Leaf'))) =n= 7)
  &&
  (candidate (Node' (Node' (Node' Leaf' 42 Leaf') 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) 42 (Node' Leaf' 42 (Node' Leaf' 42 Leaf'))) =n= 7)
  .

Fixpoint number_of_nodes'_v0 (t : binary_tree') : nat :=
  match t with
  | Leaf' => O
  | Node' t1 n t2 => S ((number_of_nodes'_v0 t1) + (number_of_nodes'_v0 t2))
  end.

Compute (test_number_of_nodes' number_of_nodes'_v0).

Definition number_of_nodes'_v1 (t : binary_tree') : nat :=
  match number_of_leaves'_v1 t with
  | O => O
  | S n' => n'
  end.

Compute (test_number_of_nodes' number_of_nodes'_v1).

Definition number_of_nodes'_v2 (t : binary_tree') : nat :=
  let fix visit t a :=
      match t with
      | Leaf' => a
      | Node' t1 n t2 => visit t2 (visit t1 (S a))
      end
  in visit t 0.

Compute (test_number_of_nodes' number_of_nodes'_v2).

(* ********** *)

(* Exercise 4 *)

Inductive binary_tree'' :=
| Leaf'' : nat -> binary_tree''
| Node'' : binary_tree'' -> nat -> binary_tree'' -> binary_tree''.

Definition test_number_of_leaves'' (candidate: binary_tree'' -> nat) : bool :=
  (candidate (Leaf'' 21) =n= 1)
  &&
  (candidate (Node'' (Leaf'' 21) 42 (Leaf'' 21)) =n= 2)
  &&
  (candidate (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) =n= 3)
  &&
  (candidate (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21)) =n= 3)
  &&
  (candidate (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) =n= 4)
  &&
  (candidate (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 5)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) =n= 5)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21)) 42 (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21))) =n= 6)
  &&
  (candidate (Node'' (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 6)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 7)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21)) 42 (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 7)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) 42 (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 8)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 8)
  .

Fixpoint number_of_leaves''_v0 (t : binary_tree'') : nat :=
  match t with
  | Leaf'' n => 1
  | Node'' t1 n t2 => (number_of_leaves''_v0 t1) + (number_of_leaves''_v0 t2)
  end.

Compute (test_number_of_leaves'' number_of_leaves''_v0).

Definition number_of_leaves''_v1 (t : binary_tree'') : nat :=
  let fix visit t a :=
      match t with
      | Leaf'' n => S a
      | Node'' t1 n t2 => visit t2 (visit t1 a)
      end
  in visit t 0.

Compute (test_number_of_leaves'' number_of_leaves''_v1).

Definition test_number_of_nodes'' (candidate: binary_tree'' -> nat) : bool :=
  (candidate (Leaf'' 21) =n= 0)
  &&
  (candidate (Node'' (Leaf'' 21) 42 (Leaf'' 21)) =n= 1)
  &&
  (candidate (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) =n= 2)
  &&
  (candidate (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21)) =n= 2)
  &&
  (candidate (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) =n= 3)
  &&
  (candidate (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 4)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) =n= 4)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21)) 42 (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21))) =n= 5)
  &&
  (candidate (Node'' (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 5)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 6)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Leaf'' 21)) 42 (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 6)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21))) 42 (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 7)
  &&
  (candidate (Node'' (Node'' (Node'' (Leaf'' 21) 42 (Leaf'' 21)) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) 42 (Node'' (Leaf'' 21) 42 (Node'' (Leaf'' 21) 42 (Leaf'' 21)))) =n= 7)
  .

Fixpoint number_of_nodes''_v0 (t : binary_tree'') : nat :=
  match t with
  | Leaf'' n => O
  | Node'' t1 n t2 => S ((number_of_nodes''_v0 t1) + (number_of_nodes''_v0 t2))
  end.

Compute (test_number_of_nodes'' number_of_nodes''_v0).

Definition number_of_nodes''_v1 (t : binary_tree'') : nat :=
  match number_of_leaves''_v1 t with
  | O => O
  | S n' => n'
  end.

Compute (test_number_of_nodes'' number_of_nodes''_v1).

Definition number_of_nodes''_v2 (t : binary_tree'') : nat :=
  let fix visit t a :=
      match t with
      | Leaf'' n => a
      | Node'' t1 n t2 => visit t2 (visit t1 (S a))
      end
  in visit t 0.

Compute (test_number_of_nodes'' number_of_nodes''_v2).


(* ********** *)

(* end of week-01_functional-programming-in-Coq.v *)
