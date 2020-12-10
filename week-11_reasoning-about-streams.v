(* week-11_reasoning-about-streams.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 31 Oct 2020 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Lemma binomial_expansion :
  forall x y : nat,
    (x + y) * (x + y) =
    x * x + 2 * x * y + y * y.
Proof.
  intros x y.
  ring.
Qed.

Definition binomial_expansion_Sn :
  forall n : nat,
    (S n) * (S n) =
    S (2 * n) + n * n.
Proof.
  intro n.
  ring.
Qed.

(* ********** *)

CoInductive stream (V : Type) : Type :=
| Cons : V -> stream V -> stream V.

CoInductive bisimilar : forall V : Type, stream V -> stream V -> Prop :=
| Bisimilar :
    forall (V : Type)
           (eq_V : V -> V -> Prop)
           (v1 v2 : V)
           (v1s v2s : stream V),
    eq_V v1 v2 ->
    bisimilar V v1s v2s ->
    bisimilar V (Cons V v1 v1s) (Cons V v2 v2s).

(* ********** *)

(* Reasoning with streams: *)

Definition stream_decompose (V : Type) (vs : stream V) :=
  match vs with
  | Cons _ v vs' =>
    Cons V v vs'
  end.

Theorem stream_decomposition :
  forall (V : Type)
         (vs : stream V),
    vs = stream_decompose V vs.
Proof.
  intros V [v vs'].
  unfold stream_decompose.
  reflexivity.
Qed.

(* ********** *)

(* "prefix m ns" maps the stream ns into the list of its m first elements *)

Fixpoint prefix (V : Type) (n : nat) (vs : stream V) : list V :=
  match n with
  | 0 => nil
  | S n' => match vs with
            | Cons _ v vs' => v :: (prefix V n' vs')
            end
  end.

Lemma fold_unfold_prefix_0 :
  forall (V : Type)
         (vs : stream V),
    prefix V 0 vs = nil.
Proof.
  fold_unfold_tactic prefix.
Qed.

Lemma fold_unfold_prefix_S :
  forall (V : Type)
         (n' : nat)
         (v : V)
         (vs' : stream V),
    prefix V (S n') (Cons V v vs') =
    v :: (prefix V n' vs').
Proof.
  fold_unfold_tactic prefix.
Qed.

(* ********** *)

(* "partial_sums ns" maps a stream of natural numbers to the stream of its partial sums *)

CoFixpoint partial_sums_aux (a : nat) (ns : stream nat) : stream nat :=
  match ns with
    | Cons _ n ns' =>
      Cons nat (n + a) (partial_sums_aux (n + a) ns')
  end.

Lemma fold_unfold_partial_sums_aux :
  forall (a n : nat)
         (ns' : stream nat),
    partial_sums_aux a (Cons nat n ns') =
    Cons nat (n + a) (partial_sums_aux (n + a) ns').
Proof.
  intros a n ns'.
  rewrite -> (stream_decomposition
                nat
                (partial_sums_aux a (Cons nat n ns'))).
  unfold stream_decompose.
  unfold partial_sums_aux;
    fold partial_sums_aux.
  reflexivity.
Qed.

Definition partial_sums ns := partial_sums_aux 0 ns.

(* ********** *)

CoFixpoint zeroes : stream nat :=
  Cons nat 0 zeroes.

(*
Compute prefix nat 3 zeroes.
     = 0 :: 0 :: 0 :: nil
     : list nat
*)

Lemma fold_unfold_zeroes :
  zeroes = Cons nat 0 zeroes.
Proof.
  rewrite -> (stream_decomposition nat zeroes) at 1.
  unfold stream_decompose.
  unfold zeroes;
    fold zeroes.
  reflexivity.
Qed.

CoFixpoint ones : stream nat :=
  Cons nat 1 ones.

(*
Compute prefix nat 3 ones.
     = 1 :: 1 :: 1 :: nil
     : list nat
*)

Lemma fold_unfold_ones :
  ones = Cons nat 1 ones.
Proof.
  rewrite -> (stream_decomposition nat ones) at 1.
  unfold stream_decompose.
  unfold ones;
    fold ones.
  reflexivity.
Qed.

Definition ones' :=
  partial_sums (Cons nat 1 zeroes).

(*
Compute prefix nat 4 ones'.
     = 1 :: 1 :: 1 :: 1 :: nil
     : list nat
*)

Theorem the_same_ones :
  bisimilar nat ones ones'.
Proof.
Abort.

(* ********** *)

CoFixpoint zero_one_s : stream nat :=
  Cons nat 0 (Cons nat 1 zero_one_s).

(*
Compute prefix nat 5 zero_one_s.
     = 0 :: 1 :: 0 :: 1 :: 0 :: nil
     : list nat
*)

Lemma unfold_zero_one_s :
  zero_one_s = Cons nat 0 (Cons nat 1 zero_one_s).
Proof.
  rewrite -> (stream_decomposition nat zero_one_s) at 1.
  rewrite -> (stream_decomposition nat zero_one_s) at 1.
  unfold stream_decompose.
  unfold zero_one_s;
    fold zero_one_s.
  reflexivity.
Qed.

CoFixpoint one_zero_s : stream nat :=
  Cons nat 1 (Cons nat 0 one_zero_s).

(*
Compute prefix nat 5 one_zero_s.
     = 1 :: 0 :: 1 :: 0 :: 1 :: nil
     : list nat
*)

Lemma unfold_one_zero_s :
  one_zero_s = Cons nat 1 (Cons nat 0 one_zero_s).
Proof.
  rewrite -> (stream_decomposition nat one_zero_s) at 1.
  rewrite -> (stream_decomposition nat one_zero_s) at 1.
  unfold stream_decompose.
  unfold one_zero_s;
    fold one_zero_s.
  reflexivity.
Qed.

Theorem the_same_zero_one_s :
  bisimilar nat zero_one_s (Cons nat 0 one_zero_s).
Proof.
Abort.

Theorem the_same_one_zero_s :
  bisimilar nat one_zero_s (Cons nat 1 zero_one_s).
Proof.
Abort.

(* ********** *)

CoFixpoint make_successive_numbers (i : nat) : stream nat :=
  Cons nat i (make_successive_numbers (S i)).

(*
Compute prefix nat 4 (make_successive_numbers 5).
     = 5 :: 6 :: 7 :: 8 :: nil
     : list nat
*)

Lemma unfold_make_successive_numbers :
  forall i : nat,
    make_successive_numbers i =
    Cons nat i (make_successive_numbers (S i)).
Proof.
  intro i.
  rewrite -> (stream_decomposition nat (make_successive_numbers i)).
  unfold stream_decompose.
  unfold make_successive_numbers;
    fold make_successive_numbers.
  reflexivity.
Qed.

Definition successive_positive_numbers :=
  make_successive_numbers 1.

(*
Compute prefix nat 4 successive_positive_numbers.
     = 1 :: 2 :: 3 :: 4 :: nil
     : list nat
*)

Definition successive_positive_numbers' :=
  partial_sums ones.

(*
Compute prefix nat 4 successive_positive_numbers'.
     = 1 :: 2 :: 3 :: 4 :: nil
     : list nat
*)

Theorem the_same_successive_positive_numbers :
  bisimilar
    nat
    successive_positive_numbers
    successive_positive_numbers'.
Proof.
Abort.

(* ********** *)

CoFixpoint make_stream_of_successive_odd_numbers (i : nat)  : stream nat :=
  Cons nat (S (2 * i)) (make_stream_of_successive_odd_numbers (S i)).

(*
Compute prefix nat 5 (make_stream_of_successive_odd_numbers 10).
*)

Lemma unfold_make_stream_of_successive_odd_numbers :
  forall i : nat,
    make_stream_of_successive_odd_numbers i =
    Cons nat
         (S (2 * i))
         (make_stream_of_successive_odd_numbers (S i)).
Proof.
  intro i.
  rewrite -> (stream_decomposition
                nat
                (make_stream_of_successive_odd_numbers i)).
  unfold stream_decompose.
  unfold make_stream_of_successive_odd_numbers;
    fold make_stream_of_successive_odd_numbers.
  reflexivity.
Qed.

Definition stream_of_successive_odd_numbers : stream nat :=
  make_stream_of_successive_odd_numbers 0.

(*
Compute (prefix nat 7 stream_of_successive_odd_numbers).
     = 1 :: 3 :: 5 :: 7 :: 9 :: 11 :: 13 :: nil
     : list nat
*)

Definition stream_of_successive_positive_squares' : stream nat :=
  partial_sums stream_of_successive_odd_numbers.

(*
Compute (prefix nat 7 stream_of_successive_positive_squares').
     = 1 :: 4 :: 9 :: 16 :: 25 :: 36 :: 49 :: nil
     : list nat
*)

CoFixpoint make_stream_of_successive_squares (i : nat) : stream nat :=
  Cons nat (i * i) (make_stream_of_successive_squares (S i)).

Lemma unfold_make_stream_of_successive_squares :
  forall i : nat,
    make_stream_of_successive_squares i =
    Cons nat 
         (i * i)
         (make_stream_of_successive_squares (S i)).
Proof.
  intro i.
  rewrite -> (stream_decomposition
                nat
                (make_stream_of_successive_squares i)).
  unfold stream_decompose.
  unfold make_stream_of_successive_squares;
    fold make_stream_of_successive_squares.
  reflexivity.
Qed.

Definition stream_of_successive_positive_squares : stream nat :=
  make_stream_of_successive_squares 1.

(*
Compute (prefix nat 7 stream_of_successive_positive_squares).
     = 1 :: 4 :: 9 :: 16 :: 25 :: 36 :: 49 :: nil
     : list nat
*)

Theorem the_same_successive_squares :
  bisimilar
    nat
    stream_of_successive_positive_squares
    stream_of_successive_positive_squares'.
Proof.
Abort.

(* ********** *)

CoFixpoint stream_append (V : Type) (v1s v2s : stream V) :=
  match v1s with
  | Cons _ v1 v1s' =>
    Cons V v1 (stream_append V v1s' v2s)
  end.

Lemma fold_unfold_stream_append :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : stream V),
    stream_append V (Cons V v1 v1s') v2s =
    Cons V v1 (stream_append V v1s' v2s).
Proof.
  intros V v1 v1s' v2s.
  rewrite -> (stream_decomposition V (stream_append V (Cons V v1 v1s') v2s)).
  unfold stream_decompose.
  unfold stream_append at 1; fold stream_append.
  reflexivity.
Qed.

Proposition about_stream_append :
  forall (V : Type)
         (eq_V : V -> V -> Prop),
    (forall v : V,
        eq_V v v) ->
    forall v1s v2s : stream V,
      bisimilar V (stream_append V v1s v2s) v1s.
Proof.
Abort.

(* ********** *)

(* end of week-11_reasoning-about-streams.v *)
