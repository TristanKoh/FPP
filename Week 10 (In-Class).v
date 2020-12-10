Require Import Arith Bool.

Lemma plus_time_2 :
  forall x : nat,
    x + x = 2 * x.
Proof.
  intro x.
  rewrite -> Nat.mul_succ_l.
  rewrite -> Nat.mul_1_l.
  reflexivity.
Qed.
    


Lemma twice :
  forall n : nat,
    S (S (2 * n)) = 2 * S n.
Proof.
  intro n.
  rewrite <- (plus_time_2 n).
  rewrite -> plus_n_Sm.
  rewrite <- plus_Sn_m.
  exact (plus_time_2 (S n)).

  Restart.
  
  intro n.
  induction n as [ | n'].
  - rewrite -> (Nat.mul_1_r 2).
    rewrite -> (Nat.mul_0_r 2).
    reflexivity.
  - Search (_ * S _).
    rewrite -> (Nat.mul_succ_r 2 n').
    rewrite -> (Nat.mul_succ_r 2 (S n')).
    Search (S (_ + _)).
    rewrite <- (Nat.add_succ_l (2 * n') 2).
    rewrite <- (Nat.add_succ_l (S (2 * n')) 2).
    rewrite <- IHn'.
    reflexivity.
    
  Restart.
    
  intro n.
  unfold Nat.mul.
  rewrite -> 2 Nat.add_0_r.
  rewrite <- Nat.add_succ_r.
  rewrite <- Nat.add_succ_l.
  reflexivity.
  
  Restart.
  
  intro n.
  Search (_ * S _).
  rewrite -> (Nat.mul_succ_r 2 n).
  Search (_ + S _).
  rewrite -> (Nat.add_succ_r (2 * n) 1).
  rewrite -> (Nat.add_1_r (2 * n)).
  reflexivity.
  
  Restart.
Qed.