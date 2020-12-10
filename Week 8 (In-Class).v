Require Import Arith.

Lemma quotient :
  forall (n d : nat),
      0 < d ->
  exists (q r : nat),
    (n = q * d + r) /\ (r < d).
Proof.
  intros n d.
  intro H_d_greater_than_0.
  induction n as [ | n'].
  - exists 0, 0.
    split.
    + rewrite -> (Nat.mul_0_l d).
      rewrite -> (Nat.add_0_l 0).
      reflexivity.
    + exact H_d_greater_than_0.
  - destruct IHn' as [q [r [H_left H_right]]].
    Search (_ < _ \/ _ = _).
    rewrite <- (Nat.lt_eq_cases (S r) d).
    exists q, (S r).
    split.
    + rewrite -> H_left.
      Search (_ + S _).
      rewrite -> (Nat.add_succ_r (q * d) r).
      reflexivity.
    + Search (S _ < _).

    exists (S q, 0).
  

Fixpoint division (n d : nat) :=
  match n with
  | 0 => (0, 0)
  | S n' => let (q, r) := division n' d in
            match d with
            | S r'


Definition specification_of_division (division : forall (n d : nat) -> nat * nat) :=
  (forall d : nat,
      division 0 d = (0, 0))
  /\
  (forall (n' d : nat),
      division (S n') d = ()).



