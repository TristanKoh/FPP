(* term-project.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 15 Nov 2020 *)

(* ********** *)

(* Three language processors for arithmetic expressions. *)

(*
   name:
   student ID number:
   e-mail address:
*)

(* ********** *)

(*

The primary goal of this term project is to prove the following theorem:

  Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret sp = run (compile sp).

for

* a source language of arithmetic expressions:

    Inductive arithmetic_expression : Type :=
    | Literal : nat -> arithmetic_expression
    | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
    | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.
    
    Inductive source_program : Type :=
    | Source_program : arithmetic_expression -> source_program.

* a target language of byte-code instructions:

    Inductive byte_code_instruction : Type :=
    | PUSH : nat -> byte_code_instruction
    | ADD : byte_code_instruction
    | SUB : byte_code_instruction.
    
    Inductive target_program : Type :=
    | Target_program : list byte_code_instruction -> target_program.

* a semantics of expressible values:

    Inductive expressible_value : Type :=
    | Expressible_nat : nat -> expressible_value
    | Expressible_msg : string -> expressible_value.

* a source interpreter

    interpret : source_program -> expressible_value

* a compiler

    compile : source_program -> target_program

* a target interpreter

    run : target_program -> expressible_value

The source for errors is subtraction,
since subtracting two natural numbers does not always yield a natural number:
for example, 3 - 2 is defined but not 2 - 3.

You are expected, at the very least:

* to implement a source interpreter
  and to verify that it satisfies its specification

* to implement a target interpreter (i.e., a virtual machine)
  and to verify that it satisfies its specification

* to implement a compiler
  and to verify that it satisfies its specification

* to prove that the diagram commutes, i.e., to show that
  interpreting any given expression
  gives the same result as
  compiling this expression and then running the resulting compiled program

Beyond this absolute minimum, in decreasing importance, it would be good:

* to make a copy of the above in a separate file
  and modify it mutatis mutandis
  so that the three language processors operate from right to left instead of from left to right,

* to write an accumulator-based compiler and to prove that it satisfies the specification,

* to investigate byte-code verification,

* to investigate decompilation, and

* if there is any time left, to prove that each of the specifications specifies a unique function.

Also, feel free to expand the source language and the target language,
e.g., with multiplication, quotient, and modulo.

*)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
  
Require Import Arith Bool List String Ascii.

(* caution: only use natural numbers up to 5000 *)
Definition string_of_nat (q0 : nat) : string :=
  let s0 := String (ascii_of_nat (48 + (q0 mod 10))) EmptyString
  in if q0 <? 10
     then s0
     else let q1 := q0 / 10
          in let s1 := String (ascii_of_nat (48 + (q1 mod 10))) s0
             in if q1 <? 10
                then s1
                else let q2 := q1 / 10
                     in let s2 := String (ascii_of_nat (48 + (q2 mod 10))) s1
                        in if q2 <? 10
                           then s2
                           else let q3 := q2 / 10
                                in let s2 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                        in if q3 <? 10
                           then s2
                           else "00000".

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
| Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
| Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
| Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     evaluate (Literal n) = Expressible_nat n)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2))).

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Task 1: 
   a. time permitting, prove that each of the definitions above specifies at most one function;
   b. implement these two functions; and
   c. verify that each of your functions satisfies its specification.
*)

Proposition there_is_at_most_one_evaluate :
  forall evaluate1 evaluate2 : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate1 ->
    specification_of_evaluate evaluate2 ->
    forall ae : arithmetic_expression,
      evaluate1 ae = evaluate2 ae.
Proof.
  intros evaluate1 evaluate2 S_evaluate1 S_evaluate2 ae.
  destruct S_evaluate1 as [H_eval1_Literal
                             [[H_eval1_Plus_msg1 [H_eval1_Plus_msg2 H_eval1_Plus_nat]]
                                [H_eval1_Minus_msg1 [H_eval1_Minus_msg2 [H_eval1_Minus_underflow H_eval1_Minus_nat]]]]].
  destruct S_evaluate2 as [H_eval2_Literal
                             [[H_eval2_Plus_msg1 [H_eval2_Plus_msg2 H_eval2_Plus_nat]]
                                [H_eval2_Minus_msg1 [H_eval2_Minus_msg2 [H_eval2_Minus_underflow H_eval2_Minus_nat]]]]].
  induction ae as [n | ae1 H_eval1_ae1 ae2 H_eval1_ae2 | ae1 H_eval1_ae1 ae2 H_eval1_ae2].
  - rewrite -> (H_eval1_Literal n).
    rewrite -> (H_eval2_Literal n).
    reflexivity.
  - case (evaluate2 ae1) as [n1 | s1] eqn:H_eval2_ae1.
    + case (evaluate2 ae2) as [n2 | s2] eqn:H_eval2_ae2.
      * rewrite -> (H_eval1_Plus_nat ae1 ae2 n1 n2 H_eval1_ae1 H_eval1_ae2).
        rewrite -> (H_eval2_Plus_nat ae1 ae2 n1 n2 H_eval2_ae1 H_eval2_ae2).
        reflexivity.
      * rewrite -> (H_eval1_Plus_msg2 ae1 ae2 n1 s2 H_eval1_ae1 H_eval1_ae2).
        rewrite -> (H_eval2_Plus_msg2 ae1 ae2 n1 s2 H_eval2_ae1 H_eval2_ae2).
        reflexivity.
    + rewrite -> (H_eval1_Plus_msg1 ae1 ae2 s1 H_eval1_ae1).
      rewrite -> (H_eval2_Plus_msg1 ae1 ae2 s1 H_eval2_ae1).
      reflexivity.
  - case (evaluate2 ae1) as [n1 | s1] eqn:H_eval2_ae1.
    + case (evaluate2 ae2) as [n2 | s2] eqn:H_eval2_ae2.
      * case (n1 <? n2) eqn:H_n1_n2.
        -- rewrite -> (H_eval1_Minus_underflow ae1 ae2 n1 n2 H_eval1_ae1 H_eval1_ae2 H_n1_n2).
           rewrite -> (H_eval2_Minus_underflow ae1 ae2 n1 n2 H_eval2_ae1 H_eval2_ae2 H_n1_n2).
           reflexivity.
        -- rewrite -> (H_eval1_Minus_nat ae1 ae2 n1 n2 H_eval1_ae1 H_eval1_ae2 H_n1_n2).
           rewrite -> (H_eval2_Minus_nat ae1 ae2 n1 n2 H_eval2_ae1 H_eval2_ae2 H_n1_n2).
           reflexivity.
      * rewrite -> (H_eval1_Minus_msg2 ae1 ae2 n1 s2 H_eval1_ae1 H_eval1_ae2).
        rewrite -> (H_eval2_Minus_msg2 ae1 ae2 n1 s2 H_eval2_ae1 H_eval2_ae2).
        reflexivity.
    + rewrite -> (H_eval1_Minus_msg1 ae1 ae2 s1 H_eval1_ae1).
      rewrite -> (H_eval2_Minus_msg1 ae1 ae2 s1 H_eval2_ae1).
      reflexivity.
Qed.

Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n => Expressible_nat n
  | Plus ae1 ae2 =>
    match evaluate ae1 with
    | Expressible_msg s1 => Expressible_msg s1
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_msg s2 => Expressible_msg s2
      | Expressible_nat n2 => Expressible_nat (n1 + n2)
      end
    end
  | Minus ae1 ae2 =>
    match evaluate ae1 with
    | Expressible_msg s1 => Expressible_msg s1
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_msg s2 => Expressible_msg s2
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
        else Expressible_nat (n1 - n2)
      end
    end
  end.

Lemma fold_unfold_evaluate_Literal :
  forall n : nat,
    evaluate (Literal n) = Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Plus :
  forall ae1 ae2 : arithmetic_expression,
    evaluate (Plus ae1 ae2) =
    match evaluate ae1 with
    | Expressible_msg s1 => Expressible_msg s1
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_msg s2 => Expressible_msg s2
      | Expressible_nat n2 => Expressible_nat (n1 + n2)
      end
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Minus :
  forall ae1 ae2 : arithmetic_expression,
    evaluate (Minus ae1 ae2) =
    match evaluate ae1 with
    | Expressible_msg s1 => Expressible_msg s1
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_msg s2 => Expressible_msg s2
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
        else Expressible_nat (n1 - n2)
      end
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Theorem evaluate_satisfies_the_specification_of_evaluate :
  specification_of_evaluate evaluate.
Proof.
  unfold specification_of_evaluate.
  split.
  - exact fold_unfold_evaluate_Literal.
  - split.
    + split.
      * intros ae1 ae2 s1 H_eval_ae1.
        rewrite -> (fold_unfold_evaluate_Plus ae1 ae2).
        rewrite -> H_eval_ae1.
        reflexivity.
      * split.
        -- intros ae1 ae2 n1 s2 H_eval_ae1 H_eval_ae2.
           rewrite -> (fold_unfold_evaluate_Plus ae1 ae2).
           rewrite -> H_eval_ae1.
           rewrite -> H_eval_ae2.
           reflexivity.
        -- intros ae1 ae2 n1 n2 H_eval_ae1 H_eval_ae2.
           rewrite -> (fold_unfold_evaluate_Plus ae1 ae2).
           rewrite -> H_eval_ae1.
           rewrite -> H_eval_ae2.
           reflexivity.
    + split.
      * intros ae1 ae2 s1 H_eval_ae1.
        rewrite -> (fold_unfold_evaluate_Minus ae1 ae2).
        rewrite -> H_eval_ae1.
        reflexivity.
      * split.
        -- intros ae1 ae2 n1 s2 H_eval_ae1 H_eval_ae2.
           rewrite -> (fold_unfold_evaluate_Minus ae1 ae2).
           rewrite -> H_eval_ae1.
           rewrite -> H_eval_ae2.
           reflexivity.
        -- split.
           ++ intros ae1 ae2 n1 n2 H_eval_ae1 H_eval_ae2 H_n1_n2.
              rewrite -> (fold_unfold_evaluate_Minus ae1 ae2).
              rewrite -> H_eval_ae1.
              rewrite -> H_eval_ae2.
              rewrite -> H_n1_n2.
              reflexivity.
           ++ intros ae1 ae2 n1 n2 H_eval_ae1 H_eval_ae2 H_n1_n2.
              rewrite -> (fold_unfold_evaluate_Minus ae1 ae2).
              rewrite -> H_eval_ae1.
              rewrite -> H_eval_ae2.
              rewrite -> H_n1_n2.
              reflexivity.
Qed.

Proposition there_is_at_most_one_interpret :
  forall interpret1 interpret2 : source_program -> expressible_value,
    specification_of_interpret interpret1 ->
    specification_of_interpret interpret2 ->
    forall sp : source_program,
      interpret1 sp = interpret2 sp.
Proof.
  intros interpret1 interpret2 S_interpret1 S_interpret2 [ae].
  unfold specification_of_interpret in S_interpret1, S_interpret2.
  rewrite -> (S_interpret1 evaluate evaluate_satisfies_the_specification_of_evaluate ae).
  rewrite -> (S_interpret2 evaluate evaluate_satisfies_the_specification_of_evaluate ae).
  reflexivity.
Qed.

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae => evaluate ae
  end.

Theorem interpret_satisfies_the_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret, interpret.
  intros evaluate' S_evaluate' ae.
  Check (there_is_at_most_one_evaluate
           evaluate evaluate'
           evaluate_satisfies_the_specification_of_evaluate
           S_evaluate'
           ae).
  exact (there_is_at_most_one_evaluate
           evaluate evaluate'
           evaluate_satisfies_the_specification_of_evaluate
           S_evaluate'
           ae).
Qed.

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
| PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

(* Target programs: *)

Inductive target_program : Type :=
| Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (forall (n : nat)
          (ds : data_stack),
     decode_execute (PUSH n) ds = OK (n :: ds))
  /\
  ((decode_execute ADD nil = KO "ADD: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute ADD (n2 :: nil) = KO "ADD: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       decode_execute ADD (n2 :: n1 :: ds) = OK ((n1 + n2) :: ds)))
  /\
  ((decode_execute SUB nil = KO "SUB: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute SUB (n2 :: nil) = KO "SUB: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = true ->
       decode_execute SUB (n2 :: n1 :: ds) = KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = false ->
       decode_execute SUB (n2 :: n1 :: ds) = OK ((n1 - n2) :: ds))).

(* Task 2:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)

Proposition there_is_at_most_one_decode_execute :
  forall decode_execute1 decode_execute2 : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute decode_execute1 ->
    specification_of_decode_execute decode_execute2 ->
    forall (bcis : byte_code_instruction)
           (ds : data_stack),
      decode_execute1 bcis ds = decode_execute2 bcis ds.
Proof.
  intros decode_execute1 decode_execute2 S_de1 S_de2 bcis ds.
  destruct S_de1 as [H_push1
                       [[H_add1_nil [H_add1_n1 H_add1_n2_n1]]
                          [H_sub1_nil [H_sub1_n2 [H_sub1_n1_n2_true H_sub1_n1_n2_false]]]]].
  destruct S_de2 as [H_push2
                       [[H_add2_nil [H_add2_n1 H_add2_n2_n1]]
                          [H_sub2_nil [H_sub2_n2 [H_sub2_n1_n2_true H_sub2_n1_n2_false]]]]].
  case bcis as [n | | ].
  - rewrite -> (H_push1 n ds).
    rewrite -> (H_push2 n ds).
    reflexivity.
  - case ds as [ | n ds'].
    + rewrite -> H_add1_nil.
      rewrite -> H_add2_nil.
      reflexivity.
    + case ds' as [ | n' ds''].
      * rewrite -> (H_add1_n1 n).
        rewrite -> (H_add2_n1 n).
        reflexivity.
      * rewrite -> (H_add1_n2_n1 n' n).
        rewrite -> (H_add2_n2_n1 n' n).
        reflexivity.
  - case ds as [ | n ds'].
    + rewrite -> H_sub1_nil.
      rewrite -> H_sub2_nil.
      reflexivity.
    + case ds' as [ | n' ds''].
      * rewrite -> (H_sub1_n2 n).
        rewrite -> (H_sub2_n2 n).
        reflexivity.
      * case (n' <? n) eqn:H_n1_n2.
        -- rewrite -> (H_sub1_n1_n2_true n' n ds'' H_n1_n2).
           rewrite -> (H_sub2_n1_n2_true n' n ds'' H_n1_n2).
           reflexivity.
        -- rewrite -> (H_sub1_n1_n2_false n' n ds'' H_n1_n2).
           rewrite -> (H_sub2_n1_n2_false n' n ds'' H_n1_n2).
           reflexivity.
Qed.      


Definition decode_execute (bcis : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | PUSH n =>
    OK (n :: ds)
  | ADD =>
    match ds with
    | nil =>
      KO "ADD: stack underflow"
    | (n2 :: nil) =>
      KO "ADD: stack underflow"
    | (n2 :: n1 :: ds) =>
      OK ((n1 + n2) :: ds)
    end
  | SUB =>
    match ds with
    | nil =>
      KO "SUB: stack underflow"
    | (n2 :: nil) =>
      KO "SUB: stack underflow"
    | (n2 :: n1 :: ds) =>
      if n1 <? n2
      then KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
      else OK ((n1 - n2) :: ds)
    end
  end.

Theorem decode_execute_satisfies_the_specification_of_decode_execute :
  specification_of_decode_execute decode_execute.
Proof.
  unfold specification_of_decode_execute, decode_execute.
  split.
  - intros n ds.
    reflexivity.
  - split.
    + split.
      * reflexivity.
      * split.
        -- intro n.
           reflexivity.
        -- intros n1 n2 ds.
           reflexivity.
    + split.
      * reflexivity.
      * split.
        -- intro n.
           reflexivity.
        -- split.
           ++ intros n1 n2 ds H_n1_n2.
              rewrite H_n1_n2.
              reflexivity.
           ++ intros n1 n2 ds H_n1_n2.
              rewrite H_n1_n2.
              reflexivity.
Qed.

(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  forall decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute decode_execute ->
    (forall ds : data_stack,
        fetch_decode_execute_loop nil ds = OK ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack),
        decode_execute bci ds = OK ds' ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        fetch_decode_execute_loop bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack)
            (s : string),
        decode_execute bci ds = KO s ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        KO s).

(* Task 3:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)

Proposition there_is_at_most_one_fetch_decode_execute_loop :
  forall fetch_decode_execute_loop1 fetch_decode_execute_loop2 : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop1 ->
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop2 ->
    forall (bcis : list byte_code_instruction)
           (ds : data_stack),
      fetch_decode_execute_loop1 bcis ds = fetch_decode_execute_loop2 bcis ds.
Proof.
  intros loop1 loop2 S_loop1 S_loop2 bcis.
  unfold specification_of_fetch_decode_execute_loop in S_loop1, S_loop2.
  assert (S_loop1 := S_loop1 decode_execute decode_execute_satisfies_the_specification_of_decode_execute).
  assert (S_loop2 := S_loop2 decode_execute decode_execute_satisfies_the_specification_of_decode_execute).
  destruct S_loop1 as [H_loop1_nil [H_loop1_cons_OK H_loop1_cons_KO]].
  destruct S_loop2 as [H_loop2_nil [H_loop2_cons_OK H_loop2_cons_KO]].
  induction bcis as [ | bci bcis' IHbcis']; intro ds.
  - rewrite -> (H_loop1_nil ds).
    rewrite -> (H_loop2_nil ds).
    reflexivity.
  - case (decode_execute bci ds) as [ds' | s] eqn:H_de.
    + rewrite -> (H_loop1_cons_OK bci bcis' ds ds' H_de).
      rewrite -> (H_loop2_cons_OK bci bcis' ds ds' H_de).
      rewrite -> (IHbcis' ds').
      reflexivity.
    + rewrite -> (H_loop1_cons_KO bci bcis' ds s H_de).
      rewrite -> (H_loop2_cons_KO bci bcis' ds s H_de).
      reflexivity.
Qed.

Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | nil =>
    OK ds
  | bci :: bcis' =>
    match decode_execute bci ds with
    | OK ds' =>
      fetch_decode_execute_loop bcis' ds'
    | KO s =>
      KO s
    end
  end.

Lemma fold_unfold_fetch_decode_execute_loop_nil :
  forall ds : data_stack,
    fetch_decode_execute_loop nil ds =
    OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop (bci :: bcis') ds =
    match decode_execute bci ds with
    | OK ds =>
      fetch_decode_execute_loop bcis' ds
    | KO s =>
      KO s
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Theorem fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros decode_execute' S_decode_execute'.
  split.
  - exact fold_unfold_fetch_decode_execute_loop_nil.
  - split.
    + intros bci bcis' ds ds' H_decode_execute'_bci_ds.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci bcis' ds).
      Check (there_is_at_most_one_decode_execute).
      Check (there_is_at_most_one_decode_execute
               decode_execute'
               decode_execute
               S_decode_execute'
               decode_execute_satisfies_the_specification_of_decode_execute
               bci
               ds).
      rewrite -> (there_is_at_most_one_decode_execute
                    decode_execute'
                    decode_execute
                    S_decode_execute'
                    decode_execute_satisfies_the_specification_of_decode_execute
                    bci
                    ds) in H_decode_execute'_bci_ds.
      rewrite -> H_decode_execute'_bci_ds.
      reflexivity.
    + intros bci bcis' ds s H_decode_execute'_bci_ds.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci bcis' ds).
      rewrite -> (there_is_at_most_one_decode_execute
                    decode_execute'
                    decode_execute
                    S_decode_execute'
                    decode_execute_satisfies_the_specification_of_decode_execute
                    bci
                    ds) in H_decode_execute'_bci_ds.
      rewrite -> H_decode_execute'_bci_ds.
      reflexivity.
Qed.


(* ********** *)

(* Task 4:
   Prove that for any lists of byte-code instructions bcis1 and bcis2,
   and for any data stack ds,
   executing the concatenation of bcis1 and bcis2 (i.e., bcis1 ++ bcis2) with ds
   gives the same result as
   (1) executing bcis1 with ds, and then
   (2) executing bcis2 with the resulting data stack, if there exists one.
*)

Lemma fold_unfold_append_nil :
  forall bcis2 : list byte_code_instruction,
    nil ++ bcis2 = bcis2.
Proof.
  fold_unfold_tactic List.app.
Qed.

Lemma fold_unfold_append_cons :
  forall (bci1 : byte_code_instruction)
         (bci1s bci2s : list byte_code_instruction),
    (bci1 :: bci1s) ++ bci2s =
    bci1 :: (bci1s ++ bci2s).
Proof.
  fold_unfold_tactic List.app.
Qed.

Theorem concatenation_of_two_list_bcis_with_ds :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds : data_stack),
    (forall ds' : data_stack,  
        fetch_decode_execute_loop bcis1 ds = OK ds' ->
        fetch_decode_execute_loop bcis2 ds' =
        fetch_decode_execute_loop (bcis1 ++ bcis2) ds)
    /\
    (forall s : string,
        fetch_decode_execute_loop bcis1 ds = KO s ->
        fetch_decode_execute_loop (bcis1 ++ bcis2) ds = KO s).
Proof.
  intros bcis1.
  induction bcis1 as [ | bci1 bcis1' IHbcis1']; intros bcis2 ds; split.
  - intros ds' H_loop_bcis1.
    rewrite -> (fold_unfold_append_nil bcis2).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_nil ds) in H_loop_bcis1.
    injection H_loop_bcis1 as H_ds.
    rewrite -> H_ds.
    reflexivity.
  - intros s H_loop_bcis1.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_nil ds) in H_loop_bcis1.
    discriminate H_loop_bcis1.
  - intros ds' H_loop_bcis1.
    rewrite -> (fold_unfold_append_cons bci1 bcis1' bcis2).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci1 (bcis1' ++ bcis2) ds).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci1 bcis1' ds) in H_loop_bcis1.
    case (decode_execute bci1 ds) as [ds'' | s].
    + destruct (IHbcis1' bcis2 ds'') as [IHds'' _].
      exact (IHds'' ds' H_loop_bcis1).
    + destruct (IHbcis1' bcis2 ds') as [IHds'' _].
      discriminate H_loop_bcis1.
  - intros s H_loop_bcis1.
    rewrite -> (fold_unfold_append_cons bci1 bcis1' bcis2).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci1 (bcis1' ++ bcis2) ds).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci1 bcis1' ds) in H_loop_bcis1.
    case (decode_execute bci1 ds) as [ds' | s'].
    + destruct (IHbcis1' bcis2 ds') as [_ IHs].
      exact (IHs s H_loop_bcis1).
    + exact H_loop_bcis1.
Qed. 

(* ********** *)

Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
        fetch_decode_execute_loop bcis nil = OK nil ->
        run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
        fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
        run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
        fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
        run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
        fetch_decode_execute_loop bcis nil = KO s ->
        run (Target_program bcis) = Expressible_msg s).

(* Task 5:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)


Proposition there_is_at_most_one_run :
  forall (decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
    specification_of_decode_execute decode_execute ->
    forall (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
      specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
      forall (run1 run2 : target_program -> expressible_value),
        specification_of_run run1 ->
        specification_of_run run2 ->
        forall (tp : target_program),
          run1 tp = run2 tp.
Proof.
  intros decode_execute H_decode_execute fetch_decode_execute_loop H_fetch_decode_execute_loop run1 run2 S_run1 S_run2 [bcis].
  unfold specification_of_run in S_run1, S_run2.
  assert (S_run1 := S_run1 fetch_decode_execute_loop H_fetch_decode_execute_loop). 
  assert (S_run2 := S_run2 fetch_decode_execute_loop H_fetch_decode_execute_loop).
  destruct S_run1 as [H_run1_nil [H_run1_n [H_run1_n_n' H_run1_s]]].
  destruct S_run2 as [H_run2_nil [H_run2_n [H_run2_n_n' H_run2_s]]].
  case (fetch_decode_execute_loop bcis nil) as [ds | s] eqn:H_loop.
  - case ds as [ | n ds'].
    + rewrite -> (H_run1_nil bcis H_loop).
      rewrite -> (H_run2_nil bcis H_loop).
      reflexivity.
    + case ds' as [ | n' ds''].
      * rewrite -> (H_run1_n bcis n H_loop).
        rewrite -> (H_run2_n bcis n H_loop).
        reflexivity.
      * rewrite -> (H_run1_n_n' bcis n n' ds'' H_loop).
        rewrite -> (H_run2_n_n' bcis n n' ds'' H_loop).
        reflexivity.
  - rewrite -> (H_run1_s bcis s H_loop).
    rewrite -> (H_run2_s bcis s H_loop).
    reflexivity.

Restart.

  intros decode_execute H_decode_execute fetch_decode_execute_loop H_fetch_decode_execute_loop run1 run2 S_run1 S_run2 [bcis].
  unfold specification_of_run in S_run1, S_run2.
  assert (S_run1 := S_run1 fetch_decode_execute_loop H_fetch_decode_execute_loop). 
  assert (S_run2 := S_run2 fetch_decode_execute_loop H_fetch_decode_execute_loop).
  destruct S_run1 as [H_run1_nil [H_run1_n [H_run1_n_n' H_run1_s]]].
  destruct S_run2 as [H_run2_nil [H_run2_n [H_run2_n_n' H_run2_s]]].
  case (fetch_decode_execute_loop bcis nil) as [[ | n [ | n' ds'']] | s] eqn:H_loop.
  - rewrite -> (H_run1_nil bcis H_loop).
    rewrite -> (H_run2_nil bcis H_loop).
    reflexivity.
  - rewrite -> (H_run1_n bcis n H_loop).
    rewrite -> (H_run2_n bcis n H_loop).
    reflexivity.
  - rewrite -> (H_run1_n_n' bcis n n' ds'' H_loop).
    rewrite -> (H_run2_n_n' bcis n n' ds'' H_loop).
    reflexivity.
  - rewrite -> (H_run1_s bcis s H_loop).
    rewrite -> (H_run2_s bcis s H_loop).
    reflexivity.
Qed.

Definition run (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
    | OK nil =>
      Expressible_msg "no result on the data stack"
    | OK (n :: nil) =>
      Expressible_nat n
    | OK (n :: n' :: ds') =>
      Expressible_msg "too many results on the data stack"
    | KO s =>
      Expressible_msg s
    end
  end.

Theorem run_satisfies_the_specification_of_run :
  specification_of_run run.
Proof.
  unfold specification_of_run.
  intros fetch_decode_execute_loop' S_loop.
  split.
  - intros bcis H_fetch_decode_execute_loop_nil.
    unfold run.
    Check (there_is_at_most_one_fetch_decode_execute_loop).
    Check (there_is_at_most_one_fetch_decode_execute_loop
             fetch_decode_execute_loop'
             fetch_decode_execute_loop
             S_loop
             fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop
             bcis
             nil).
    rewrite -> (there_is_at_most_one_fetch_decode_execute_loop
                  fetch_decode_execute_loop'
                  fetch_decode_execute_loop
                  S_loop
                  fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop
                  bcis
                  nil) in H_fetch_decode_execute_loop_nil.
    rewrite -> H_fetch_decode_execute_loop_nil.
    reflexivity.
  - split.
    + intros bcis n H_fetch_decode_execute_loop'.
      unfold run.
      rewrite -> (there_is_at_most_one_fetch_decode_execute_loop
                    fetch_decode_execute_loop'
                    fetch_decode_execute_loop
                    S_loop
                    fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop
                    bcis
                    nil) in H_fetch_decode_execute_loop'.
      rewrite -> H_fetch_decode_execute_loop'.
      reflexivity.
    + split.
      * intros bcis n n' ds'' H_fetch_decode_execute_loop'.
        unfold run.
        rewrite -> (there_is_at_most_one_fetch_decode_execute_loop
                      fetch_decode_execute_loop'
                      fetch_decode_execute_loop
                      S_loop
                      fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop
                      bcis
                      nil) in H_fetch_decode_execute_loop'.
        rewrite -> H_fetch_decode_execute_loop'.
        reflexivity.
      * intros bcis s H_fetch_decode_execute_loop'. 
        unfold run.
        rewrite -> (there_is_at_most_one_fetch_decode_execute_loop
                      fetch_decode_execute_loop'
                      fetch_decode_execute_loop
                      S_loop
                      fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop
                      bcis
                      nil) in H_fetch_decode_execute_loop'.
        rewrite -> H_fetch_decode_execute_loop'.
        reflexivity.
Qed.
        
(* ********** *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).

(* Task 6:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function using list concatenation, i.e., ++; and
   c. verify that your function satisfies the specification.
 *)

Proposition there_is_at_most_one_compile_aux :
  forall compile_aux1 compile_aux2 :  arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux1 ->
    specification_of_compile_aux compile_aux2 ->
    forall (ae : arithmetic_expression),
      compile_aux1 ae = compile_aux2 ae.
Proof.
  intros compile_aux1 compile_aux2 S_compile_aux1 S_compile_aux2 ae.
  destruct S_compile_aux1 as [H_compile_aux1_Literal [H_compile_aux1_Plus H_compile_aux1_Minus]]. 
  destruct S_compile_aux2 as [H_compile_aux2_Literal [H_compile_aux2_Plus H_compile_aux2_Minus]]. 
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - rewrite -> (H_compile_aux1_Literal n).
    rewrite -> (H_compile_aux2_Literal n).
    reflexivity.
  - rewrite -> (H_compile_aux1_Plus ae1 ae2).
    rewrite -> (H_compile_aux2_Plus ae1 ae2).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - rewrite -> (H_compile_aux1_Minus ae1 ae2).
    rewrite -> (H_compile_aux2_Minus ae1 ae2).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.

Fixpoint compile_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    PUSH n :: nil
  | Plus ae1 ae2 =>
    (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
    (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)
  end.

Lemma fold_unfold_compile_aux_Literal :
  forall n : nat,
    compile_aux (Literal n) =
    PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux (Plus ae1 ae2) =
    (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_aux.                      
Qed.

Lemma fold_unfold_compile_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux (Minus ae1 ae2) =
    (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_aux.                      
Qed.


Theorem compile_aux_satisfies_the_specification_of_compile_aux :
  specification_of_compile_aux compile_aux.
Proof.
  unfold specification_of_compile_aux.
  split.
  - exact fold_unfold_compile_aux_Literal.
  - split.
    + exact fold_unfold_compile_aux_Plus.
    + exact fold_unfold_compile_aux_Minus.
Qed.

   

(* ********** *)

Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

(* Task 7:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)


Proposition there_is_at_most_one_compile :
  forall compile1 compile2 : source_program -> target_program,
    specification_of_compile compile1 ->
    specification_of_compile compile2 ->
    forall ae : arithmetic_expression,
      compile1 (Source_program ae) = compile2 (Source_program ae).
Proof.
  intros compile1 compile2 S_compile1 S_compile2 ae.
  Check (S_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux ae).
  rewrite -> (S_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux ae).
  rewrite -> (S_compile2 compile_aux compile_aux_satisfies_the_specification_of_compile_aux ae).
  reflexivity.
Qed.

Definition compile (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_aux ae)
  end.

Theorem compile_satisfies_the_specification_of_compile :
  specification_of_compile compile.
Proof.
  unfold specification_of_compile, compile.
  intros compile_aux' S_compile_aux ae.
  Check (there_is_at_most_one_compile_aux
           compile_aux
           compile_aux'
           compile_aux_satisfies_the_specification_of_compile_aux
           S_compile_aux
           ae).
  rewrite -> (there_is_at_most_one_compile_aux
                compile_aux
                compile_aux'
                compile_aux_satisfies_the_specification_of_compile_aux
                S_compile_aux
                ae).
  reflexivity.
Qed.

(* ********** *)


(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
*)


Fixpoint compile_aux_acc (ae : arithmetic_expression) (a : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    PUSH n :: a
  | Plus ae1 ae2 =>
    compile_aux_acc ae1 (compile_aux_acc ae2 (ADD :: a))
  | Minus ae1 ae2 =>
    compile_aux_acc ae1 (compile_aux_acc ae2 (SUB :: a))
  end.

Definition compile_acc (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_aux_acc ae nil)
  end.

Lemma fold_unfold_compile_aux_acc_Literal :
  forall (n : nat)
         (a : list byte_code_instruction),
    compile_aux_acc (Literal n) a =
    PUSH n :: a.
Proof.
  fold_unfold_tactic compile_aux_acc.
Qed.

Lemma fold_unfold_compile_aux_acc_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_aux_acc (Plus ae1 ae2) a =
    compile_aux_acc ae1 (compile_aux_acc ae2 (ADD :: a)).
Proof.
  fold_unfold_tactic compile_aux_acc.
Qed.

Lemma fold_unfold_compile_aux_acc_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_aux_acc (Minus ae1 ae2) a =
    compile_aux_acc ae1 (compile_aux_acc ae2 (SUB :: a)).
Proof.
  fold_unfold_tactic compile_aux_acc.
Qed.

Lemma compile_aux_acc_lemma :
  forall (ae : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_aux_acc ae a =
    compile_aux ae ++ a.
Proof.
  intros ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro a.
  - rewrite -> (fold_unfold_compile_aux_acc_Literal n a).
    rewrite -> (fold_unfold_compile_aux_Literal n).
    rewrite -> (fold_unfold_append_cons (PUSH n) nil a).
    rewrite -> (fold_unfold_append_nil a).
    reflexivity.
  - rewrite -> (fold_unfold_compile_aux_acc_Plus ae1 ae2 a).
    rewrite -> (fold_unfold_compile_aux_Plus ae1 ae2).
    rewrite -> (IHae2 (ADD :: a)).
    rewrite -> (IHae1 (compile_aux ae2 ++ ADD :: a)).
    Check (List.app_assoc).
    rewrite <- (List.app_assoc (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) a).
    rewrite <- (List.app_assoc (compile_aux ae2) (ADD :: nil) a). 
    rewrite -> (fold_unfold_append_cons ADD nil a).
    rewrite -> (fold_unfold_append_nil a).
    reflexivity.
  - rewrite -> (fold_unfold_compile_aux_acc_Minus ae1 ae2 a).
    rewrite -> (fold_unfold_compile_aux_Minus ae1 ae2).
    rewrite -> (IHae2 (SUB :: a)).
    rewrite -> (IHae1 (compile_aux ae2 ++ SUB :: a)).
    rewrite <- (List.app_assoc (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) a).
    rewrite <- (List.app_assoc (compile_aux ae2) (SUB :: nil) a). 
    rewrite -> (fold_unfold_append_cons SUB nil a).
    rewrite -> (fold_unfold_append_nil a).
    reflexivity.
Qed.    

Proposition compile_acc_satisfies_the_specification_of_compile :
  specification_of_compile compile_acc.
Proof.
  unfold specification_of_compile, compile_acc.
  intros compile_aux' S_compile_aux ae.
  assert (S_compile_aux' := S_compile_aux).
  destruct S_compile_aux as [H_compile_aux_Literal [H_compile_aux_Plus H_compile_aux_Minus]].
  case ae as [n | ae1 ae2 | ae1 ae2].
  - rewrite -> (fold_unfold_compile_aux_acc_Literal n).
    rewrite -> (H_compile_aux_Literal n).
    reflexivity.
  - rewrite -> (fold_unfold_compile_aux_acc_Plus ae1 ae2 nil).
    rewrite -> (H_compile_aux_Plus ae1 ae2).
    Check (there_is_at_most_one_compile_aux).
    Check (there_is_at_most_one_compile_aux
             compile_aux
             compile_aux'
             compile_aux_satisfies_the_specification_of_compile_aux
             S_compile_aux'
             ae1).
    rewrite -> (there_is_at_most_one_compile_aux
                  compile_aux'
                  compile_aux
                  S_compile_aux'
                  compile_aux_satisfies_the_specification_of_compile_aux
                  ae1).
    rewrite -> (there_is_at_most_one_compile_aux
                  compile_aux'
                  compile_aux
                  S_compile_aux'
                  compile_aux_satisfies_the_specification_of_compile_aux
                  ae2).
    rewrite -> (compile_aux_acc_lemma ae2 (ADD :: nil)).
    rewrite -> (compile_aux_acc_lemma ae1 (compile_aux ae2 ++ ADD :: nil)).
    reflexivity.
  - rewrite -> (fold_unfold_compile_aux_acc_Minus ae1 ae2 nil).
    rewrite -> (H_compile_aux_Minus ae1 ae2).
    rewrite -> (there_is_at_most_one_compile_aux
                  compile_aux'
                  compile_aux
                  S_compile_aux'
                  compile_aux_satisfies_the_specification_of_compile_aux
                  ae1).
    rewrite -> (there_is_at_most_one_compile_aux
                  compile_aux'
                  compile_aux
                  S_compile_aux'
                  compile_aux_satisfies_the_specification_of_compile_aux
                  ae2).
    rewrite -> (compile_aux_acc_lemma ae2 (SUB :: nil)).
    rewrite -> (compile_aux_acc_lemma ae1 (compile_aux ae2 ++ SUB :: nil)).
    reflexivity.
Qed.


Proposition compile_and_compile_acc_are_equivalent :
  forall sp : source_program,
    compile sp = compile_acc sp.
Proof.
  intros [ae].
  Check (there_is_at_most_one_compile
           compile
           compile_acc
           compile_satisfies_the_specification_of_compile
           compile_acc_satisfies_the_specification_of_compile
           ae).
  exact (there_is_at_most_one_compile
           compile
           compile_acc
           compile_satisfies_the_specification_of_compile
           compile_acc_satisfies_the_specification_of_compile
           ae).
Qed.


(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
 *)


Lemma eureka_lemma_the_commutative_diagram :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (n : nat),
        evaluate ae = Expressible_nat n ->
        fetch_decode_execute_loop (compile_aux ae) ds = OK (n :: ds))
    /\
    (forall (s : string),
        evaluate ae = Expressible_msg s ->
        fetch_decode_execute_loop (compile_aux ae) ds = KO s).
Proof.
  intros ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro ds; split.
  - intros n' H_nat.
    rewrite -> (fold_unfold_evaluate_Literal n) in H_nat.
    injection H_nat as H_nat.
    rewrite <- H_nat.
    rewrite -> (fold_unfold_compile_aux_Literal n).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons (PUSH n) nil ds).
    unfold decode_execute.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_nil (n :: ds)).
    reflexivity.
  - intros s H_s.
    rewrite -> (fold_unfold_evaluate_Literal n) in H_s.
    discriminate H_s.
  - intros n H_nat.
    rewrite -> (fold_unfold_evaluate_Plus ae1 ae2) in H_nat.
    rewrite -> (fold_unfold_compile_aux_Plus ae1 ae2).
    case (evaluate ae1) as [n1 | s1] eqn:H_eval_ae1.
    + case (evaluate ae2) as [n2 | s2] eqn:H_eval_ae2.
      * destruct (concatenation_of_two_list_bcis_with_ds
                    (compile_aux ae1)
                    (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat1 _].
        destruct (IHae1 ds) as [H_loop1 _].
        Check (H_loop1 n1 (eq_refl (Expressible_nat n1))).
        Check (H_concat1 (n1 :: ds) (H_loop1 n1 (eq_refl (Expressible_nat n1)))).
        rewrite <- (H_concat1 (n1 :: ds) (H_loop1 n1 (eq_refl (Expressible_nat n1)))).
        destruct (concatenation_of_two_list_bcis_with_ds
                    (compile_aux ae2)
                    (ADD :: nil) (n1 :: ds)) as [H_concat2 _].
        destruct (IHae2 (n1 :: ds)) as [H_loop2 _].
        rewrite <- (H_concat2 (n2 :: n1 :: ds) (H_loop2 n2 (eq_refl (Expressible_nat n2)))).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_cons ADD nil (n2 :: n1 :: ds)).
        unfold decode_execute.
        rewrite -> (fold_unfold_fetch_decode_execute_loop_nil (n1 + n2 :: ds)).
        injection H_nat as H_nat.
        rewrite -> H_nat.
        reflexivity.
      * discriminate H_nat.
    + discriminate H_nat.
  - intros s H_s.
    rewrite -> (fold_unfold_evaluate_Plus ae1 ae2) in H_s.
    rewrite -> (fold_unfold_compile_aux_Plus ae1 ae2).
    case (evaluate ae1) as [n1 | s1] eqn:H_eval_ae1.
    + case (evaluate ae2) as [n2 | s2] eqn:H_eval_ae2.
      * discriminate H_s.
      * destruct (concatenation_of_two_list_bcis_with_ds
                    (compile_aux ae1)
                    (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat1 _].
        destruct (IHae1 ds) as [H_loop1 _].
        rewrite <- (H_concat1 (n1 :: ds) (H_loop1 n1 (eq_refl (Expressible_nat n1)))).
        destruct (concatenation_of_two_list_bcis_with_ds
                    (compile_aux ae2)
                    (ADD :: nil) (n1 :: ds)) as [_ H_concat2].
        destruct (IHae2 (n1 :: ds)) as [_ H_loop2].
        rewrite -> (H_concat2 s (H_loop2 s H_s)).
        reflexivity.
    + destruct (concatenation_of_two_list_bcis_with_ds
                  (compile_aux ae1)
                  (compile_aux ae2 ++ ADD :: nil) ds) as [_ H_concat1].
      destruct (IHae1 ds) as [_ H_loop1].
      rewrite <- (H_concat1 s (H_loop1 s H_s)).
        reflexivity.
  - intros n H_nat.
    rewrite -> (fold_unfold_evaluate_Minus ae1 ae2) in H_nat.
    rewrite -> (fold_unfold_compile_aux_Minus ae1 ae2).
    case (evaluate ae1) as [n1 | s1] eqn:H_eval_ae1.
    + case (evaluate ae2) as [n2 | s2] eqn:H_eval_ae2.
      * case (n1 <? n2) eqn:H_n1_n2.
        -- discriminate H_nat.
        -- destruct (concatenation_of_two_list_bcis_with_ds
                       (compile_aux ae1)
                       (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat1 _].
           destruct (IHae1 ds) as [H_loop1 _].
           rewrite <- (H_concat1 (n1 :: ds) (H_loop1 n1 (eq_refl (Expressible_nat n1)))).
           destruct (concatenation_of_two_list_bcis_with_ds
                       (compile_aux ae2)
                       (SUB :: nil) (n1 :: ds)) as [H_concat2 _].
           destruct (IHae2 (n1 :: ds)) as [H_loop2 _].
           rewrite <- (H_concat2 (n2 :: n1 :: ds) (H_loop2 n2 (eq_refl (Expressible_nat n2)))).
           rewrite -> (fold_unfold_fetch_decode_execute_loop_cons SUB nil (n2 :: n1 :: ds)).
           unfold decode_execute.
           rewrite -> H_n1_n2.
           rewrite -> (fold_unfold_fetch_decode_execute_loop_nil (n1 - n2 :: ds)).
           injection H_nat as H_nat.
           rewrite -> H_nat.
           reflexivity.
      * discriminate H_nat.
      + discriminate H_nat.
  - intros s H_s.
      rewrite -> (fold_unfold_evaluate_Minus ae1 ae2) in H_s.
      rewrite -> (fold_unfold_compile_aux_Minus ae1 ae2).
      case (evaluate ae1) as [n1 | s1] eqn:H_eval_ae1.
    + case (evaluate ae2) as [n2 | s2] eqn:H_eval_ae2.
      * case (n1 <? n2) eqn:H_n1_n2.
        -- destruct (concatenation_of_two_list_bcis_with_ds
                       (compile_aux ae1)
                       (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat1 _].
           destruct (IHae1 ds) as [H_loop1 _].
           rewrite <- (H_concat1 (n1 :: ds) (H_loop1 n1 (eq_refl (Expressible_nat n1)))).
           destruct (concatenation_of_two_list_bcis_with_ds
                       (compile_aux ae2)
                       (SUB :: nil) (n1 :: ds)) as [H_concat2 _].
           destruct (IHae2 (n1 :: ds)) as [H_loop2 _].
           rewrite <- (H_concat2 (n2 :: n1 :: ds) (H_loop2 n2 (eq_refl (Expressible_nat n2)))).
           rewrite -> (fold_unfold_fetch_decode_execute_loop_cons SUB nil (n2 :: n1 :: ds)).
           unfold decode_execute.
           rewrite -> H_n1_n2.
           injection H_s as H_s.
           rewrite <- H_s.
           reflexivity.
        -- discriminate H_s.
      * destruct (concatenation_of_two_list_bcis_with_ds
                    (compile_aux ae1)
                    (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat1 _].
        destruct (IHae1 ds) as [H_loop1 _].
        rewrite <- (H_concat1 (n1 :: ds) (H_loop1 n1 (eq_refl (Expressible_nat n1)))).
        destruct (concatenation_of_two_list_bcis_with_ds
                    (compile_aux ae2)
                    (SUB :: nil) (n1 :: ds)) as [_ H_concat2].
        destruct (IHae2 (n1 :: ds)) as [_ H_loop2].
        rewrite <- (H_concat2 s (H_loop2 s H_s)).
        reflexivity.
    + destruct (concatenation_of_two_list_bcis_with_ds
                  (compile_aux ae1)
                  (compile_aux ae2 ++ SUB :: nil) ds) as [_ H_concat1].
      destruct (IHae1 ds) as [_ H_loop1].
      rewrite <- (H_concat1 s (H_loop1 s H_s)).
      reflexivity.
Qed.

Theorem the_commutative_diagram :
  forall (sp : source_program),
    interpret sp = run (compile sp).
Proof.
  intros [ae].
  unfold compile, interpret, run.
  Check (eureka_lemma_the_commutative_diagram ae nil).
  destruct (eureka_lemma_the_commutative_diagram ae nil) as [H_OK H_KO].
  case (evaluate ae) as [n | s] eqn:H_ae.
  - rewrite -> (H_OK n (eq_refl (Expressible_nat n))).
    reflexivity.
  - rewrite -> (H_KO s (eq_refl (Expressible_msg s))).
    reflexivity.
Qed.

(* ********** *)

(* Byte-code verification:
   the following verifier symbolically executes a byte-code program
   to check whether no underflow occurs during execution
   and whether when the program completes,
   there is one and one only natural number on top of the stack.
   The second argument of verify_aux is a natural number
   that represents the size of the stack.
*)

Fixpoint verify_aux (bcis : list byte_code_instruction) (n : nat) : option nat :=
  match bcis with
    | nil =>
      Some n
    | bci :: bcis' =>
      match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
      end
  end.

Definition verify (p : target_program) : bool :=
  match p with
  | Target_program bcis =>
    match verify_aux bcis 0 with
    | Some n =>
      match n with
      | 1 =>
        true
      | _ =>
        false
      end
    | _ =>
      false
    end
  end. 

(* Task 10 (time permitting):
   Prove that the compiler emits code
   that is accepted by the verifier.
*)

Lemma fold_unfold_verify_aux_nil :
  forall n : nat,
    verify_aux nil n = Some n.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (n : nat),
    verify_aux (bci :: bcis') n =
    match bci with
    | PUSH _ =>
      verify_aux bcis' (S n)
    | _ =>
      match n with
      | S (S n') =>
        verify_aux bcis' (S n')
      | _ =>
        None
      end
    end.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Theorem concatenation_of_two_list_bcis_with_n :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (n n' : nat),
    verify_aux bcis1 n = Some n' ->
    verify_aux (bcis1 ++ bcis2) n = verify_aux bcis2 n'.
Proof.
  intro bcis1.
  induction bcis1 as [ | bci bcis1 IHbcis]; intros bcis2 n n'.
  - rewrite -> (fold_unfold_append_nil bcis2).
    rewrite -> (fold_unfold_verify_aux_nil n).
    intro H_n.
    injection H_n as H_n.
    rewrite -> H_n.
    reflexivity.
  - intro H_verify_aux.
    rewrite -> (fold_unfold_append_cons bci bcis1 bcis2).
    rewrite -> (fold_unfold_verify_aux_cons bci (bcis1 ++ bcis2) n).
    rewrite -> (fold_unfold_verify_aux_cons bci bcis1 n) in H_verify_aux.
    case bci as [ n'' | | ].
    + rewrite -> (IHbcis bcis2 (S n) n' H_verify_aux).
      reflexivity.
    + case n as [ | n''].
      * discriminate H_verify_aux.
      * case n'' as [ | n'''].
        -- discriminate H_verify_aux.
        -- rewrite -> (IHbcis bcis2 (S n''') n' H_verify_aux).
           reflexivity.
    + case n as [ | n''].
      * discriminate H_verify_aux.
      * case n'' as [ | n'''].
        -- discriminate H_verify_aux.
        -- rewrite -> (IHbcis bcis2 (S n''') n' H_verify_aux).
           reflexivity.
Qed.

Lemma the_compiler_emits_well_behaved_code_aux :
  forall (ae : arithmetic_expression)
         (n : nat),
    verify_aux (compile_aux ae) n = Some (S n).
Proof.
  intro ae.
  induction ae as [n' | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro n.
  - rewrite -> (fold_unfold_compile_aux_Literal n').
    rewrite -> (fold_unfold_verify_aux_cons (PUSH n') nil n).
    rewrite -> (fold_unfold_verify_aux_nil (S n)).
    reflexivity.
  - rewrite -> (fold_unfold_compile_aux_Plus ae1 ae2).
    Check (concatenation_of_two_list_bcis_with_n
             (compile_aux ae1)
             (compile_aux ae2 ++ ADD :: nil) n (S n)).
    rewrite -> (concatenation_of_two_list_bcis_with_n
                  (compile_aux ae1)
                  (compile_aux ae2 ++ ADD :: nil) n (S n) (IHae1 n)).
    rewrite -> (concatenation_of_two_list_bcis_with_n
                  (compile_aux ae2)
                  (ADD :: nil) (S n) (S (S n)) (IHae2 (S n))).
    rewrite -> (fold_unfold_verify_aux_cons ADD nil (S (S n))).
    rewrite -> (fold_unfold_verify_aux_nil (S n)).
    reflexivity.
  - rewrite -> (fold_unfold_compile_aux_Minus ae1 ae2).
    rewrite -> (concatenation_of_two_list_bcis_with_n
                  (compile_aux ae1)
                  (compile_aux ae2 ++ SUB :: nil) n (S n) (IHae1 n)).
    rewrite -> (concatenation_of_two_list_bcis_with_n
                  (compile_aux ae2)
                  (SUB :: nil) (S n) (S (S n)) (IHae2 (S n))).
    rewrite -> (fold_unfold_verify_aux_cons SUB nil (S (S n))).
    rewrite -> (fold_unfold_verify_aux_nil (S n)).
    reflexivity.
Qed.

Theorem the_compiler_emits_well_behaved_code :
  forall sp : source_program,
    verify (compile sp) = true.
Proof.
  intros [ae].
  unfold compile, verify.
  case ae as [n | ae1 ae2 | ae1 ae2]; unfold verify.
  - rewrite -> (fold_unfold_compile_aux_Literal n).
    rewrite -> (fold_unfold_verify_aux_cons (PUSH n) nil 0).
    rewrite -> (fold_unfold_verify_aux_nil 1).
    reflexivity.
  - rewrite -> (fold_unfold_compile_aux_Plus ae1 ae2).
    Check (concatenation_of_two_list_bcis_with_n
             (compile_aux ae1)
             (compile_aux ae2 ++ ADD :: nil) 0 1).
    Check (the_compiler_emits_well_behaved_code_aux ae1 0).
    rewrite -> (concatenation_of_two_list_bcis_with_n
                  (compile_aux ae1)
                  (compile_aux ae2 ++ ADD :: nil) 0 1
                  (the_compiler_emits_well_behaved_code_aux ae1 0)).
    rewrite -> (concatenation_of_two_list_bcis_with_n
                  (compile_aux ae2)
                  (ADD :: nil) 1 2
                  (the_compiler_emits_well_behaved_code_aux ae2 1)).
    rewrite -> (fold_unfold_verify_aux_cons ADD nil 2).
    rewrite -> (fold_unfold_verify_aux_nil 1).
    reflexivity.
  - rewrite -> (fold_unfold_compile_aux_Minus ae1 ae2).
    Check (concatenation_of_two_list_bcis_with_n
             (compile_aux ae1)
             (compile_aux ae2 ++ SUB :: nil) 0 1).
    Check (the_compiler_emits_well_behaved_code_aux ae1 0).
    rewrite -> (concatenation_of_two_list_bcis_with_n
                  (compile_aux ae1)
                  (compile_aux ae2 ++ SUB :: nil) 0 1
                  (the_compiler_emits_well_behaved_code_aux ae1 0)).
    rewrite -> (concatenation_of_two_list_bcis_with_n
                  (compile_aux ae2)
                  (SUB :: nil) 1 2
                  (the_compiler_emits_well_behaved_code_aux ae2 1)).
    rewrite -> (fold_unfold_verify_aux_cons SUB nil 2).
    rewrite -> (fold_unfold_verify_aux_nil 1).
    reflexivity.
Qed.



(* Subsidiary question:
   What is the practical consequence of this theorem?
*)

(* ********** *)

(* Task 11:

   a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   b. Write a Magritte interpreter for the target language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   c. Prove that interpreting an arithmetic expression with the Magritte source interpreter
      gives the same result as first compiling it and then executing the compiled program
      with the Magritte target interpreter over an empty data stack.

   d. Prove that the Magritte target interpreter is (essentially)
      a left inverse of the compiler, i.e., it is a decompiler.
*)

(* ********** *)

(* end of term-project.v *)
