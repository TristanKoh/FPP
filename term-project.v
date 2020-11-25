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
  intros evaluate1 evaluate2.
  unfold specification_of_evaluate.
  intros [H_eval1_Literal [[H_eval1_Plus_msg1 [H_eval1_Plus_msg2 H_eval1_Plus_nat]] [H_eval1_Minus_msg1 [H_eval1_Minus_msg2 [H_eval1_Minus_underflow H_eval1_Minus_nat]]]]] [H_eval2_Literal [[H_eval2_Plus_msg1 [H_eval2_Plus_msg2 H_eval2_Plus_nat]] [H_eval2_Minus_msg1 [H_eval2_Minus_msg2 [H_eval2_Minus_underflow H_eval2_Minus_nat]]]]].
  intro ae.
  induction ae as [n | ae1 H_eval1_ae1 ae2 H_eval1_ae2 | ae1 H_eval1_ae1 ae2 H_eval1_ae2].
  - rewrite -> (H_eval2_Literal n).
    exact (H_eval1_Literal n).
  - case (evaluate2 ae1) as [n1 | s1] eqn:H_eval2_ae1.
    + case (evaluate2 ae2) as [n2 | s2] eqn:H_eval2_ae2.
      * rewrite -> (H_eval2_Plus_nat ae1 ae2 n1 n2 H_eval2_ae1 H_eval2_ae2).
        exact (H_eval1_Plus_nat ae1 ae2 n1 n2 H_eval1_ae1 H_eval1_ae2).
      * rewrite -> (H_eval2_Plus_msg2 ae1 ae2 n1 s2 H_eval2_ae1 H_eval2_ae2).
        exact (H_eval1_Plus_msg2 ae1 ae2 n1 s2 H_eval1_ae1 H_eval1_ae2).
    + rewrite -> (H_eval2_Plus_msg1 ae1 ae2 s1 H_eval2_ae1).
      exact (H_eval1_Plus_msg1 ae1 ae2 s1 H_eval1_ae1).
  - case (evaluate2 ae1) as [n1 | s1] eqn:H_eval2_ae1.
    + case (evaluate2 ae2) as [n2 | s2] eqn:H_eval2_ae2.
      * case (n1 <? n2) eqn:H_n1_n2.
        -- rewrite -> (H_eval2_Minus_underflow ae1 ae2 n1 n2 H_eval2_ae1 H_eval2_ae2 H_n1_n2).
           exact (H_eval1_Minus_underflow ae1 ae2 n1 n2 H_eval1_ae1 H_eval1_ae2 H_n1_n2).
        -- rewrite -> (H_eval2_Minus_nat ae1 ae2 n1 n2 H_eval2_ae1 H_eval2_ae2 H_n1_n2).
           exact (H_eval1_Minus_nat ae1 ae2 n1 n2 H_eval1_ae1 H_eval1_ae2 H_n1_n2).
      * rewrite -> (H_eval2_Minus_msg2 ae1 ae2 n1 s2 H_eval2_ae1 H_eval2_ae2).
        exact (H_eval1_Minus_msg2 ae1 ae2 n1 s2 H_eval1_ae1 H_eval1_ae2).
    + rewrite -> (H_eval2_Minus_msg1 ae1 ae2 s1 H_eval2_ae1).
      exact (H_eval1_Minus_msg1 ae1 ae2 s1 H_eval1_ae1).
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
Abort.


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
  intros decode_execute1 decode_execute2.
  intros H_de1 H_de2.
  intros bcis ds.
  destruct H_de1 as [H_push1 [H_add1 H_sub1]].
  destruct H_add1 as [H_add1_nil [H_add1_n1 H_add1_n2_n1]].
  destruct H_sub1 as [H_sub1_nil [H_sub1_n2 [H_sub1_n1_n2_true H_sub1_n1_n2_false]]].
  destruct H_de2 as [H_push2 [H_add2 H_sub2]].
  destruct H_add2 as [H_add2_nil [H_add2_n1 H_add2_n2_n1]].
  destruct H_sub2 as [H_sub2_nil [H_sub2_n2 [H_sub2_n1_n2_true H_sub2_n1_n2_false]]].
  destruct bcis.
  - rewrite -> H_push1.
    rewrite -> H_push2.
    reflexivity.
  - destruct ds.
    * rewrite -> H_add1_nil.
      rewrite -> H_add2_nil.
      reflexivity.
    * destruct ds.
    + rewrite -> H_add1_n1.
      rewrite -> H_add2_n1.
      reflexivity.
    + rewrite -> H_add1_n2_n1.
      rewrite -> H_add2_n2_n1.
      reflexivity.
  - destruct ds.
    * rewrite -> H_sub1_nil.
      rewrite -> H_sub2_nil.
      reflexivity.
    * destruct ds.
    + rewrite -> H_sub1_n2.
      rewrite -> H_sub2_n2.
      reflexivity.
    + destruct (n0 <? n)eqn: H_n1_n2.
      rewrite -> H_sub1_n1_n2_true.
      rewrite -> H_sub2_n1_n2_true.
      reflexivity.
      exact H_n1_n2.
      exact H_n1_n2.
      rewrite -> H_sub1_n1_n2_false.
      rewrite -> H_sub2_n1_n2_false.
      reflexivity.
      exact H_n1_n2.
      exact H_n1_n2.
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
        ** reflexivity.
        ** intros n1 n2 ds.
           reflexivity.
    + split.
      reflexivity.
      split.
      * intro H_nat.
        reflexivity.
      * split.
        ** intros n1 n2 ds.
           intros H_n1_n2.
           rewrite H_n1_n2.
           reflexivity.
        ** intros n1 n2 ds.
           intro H_n1_n2.
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
    forall (bcis' : list byte_code_instruction)
           (ds : data_stack),
      fetch_decode_execute_loop1 bcis' ds = fetch_decode_execute_loop2 bcis' ds.
Proof.
Abort. 


Fixpoint fetch_decode_execute_loop (bcis' : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis' with
  | nil =>
    OK ds
  | bci :: bcis'' =>
    match decode_execute bci ds with
    | OK ds' =>
      fetch_decode_execute_loop bcis'' ds'
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
         (bcis'' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop (bci :: bcis'') ds =
    match decode_execute bci ds with
    | OK ds =>
      fetch_decode_execute_loop bcis'' ds
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
  intros decode_execute0 H_decode_execute.
  split.
  - intros ds.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.
  - split.
    * intros bci bcis' ds ds'.
      intro H_decode_execute_bci_ds.
      rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
      Check (there_is_at_most_one_decode_execute).
      Check (there_is_at_most_one_decode_execute
               decode_execute0
               decode_execute
               H_decode_execute
               decode_execute_satisfies_the_specification_of_decode_execute
               bci
               ds).
      rewrite -> (there_is_at_most_one_decode_execute
                    decode_execute0
                    decode_execute
                    H_decode_execute
                    decode_execute_satisfies_the_specification_of_decode_execute
                    bci
                    ds) in H_decode_execute_bci_ds.
      rewrite -> H_decode_execute_bci_ds.
      reflexivity.
    * intros bci bcis' ds s.
      intro H_decode_execute0_bci_ds.
      rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
      rewrite -> (there_is_at_most_one_decode_execute
                    decode_execute0
                    decode_execute
                    H_decode_execute
                    decode_execute_satisfies_the_specification_of_decode_execute
                    bci
                    ds) in H_decode_execute0_bci_ds.
      rewrite -> H_decode_execute0_bci_ds.
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
  intros bcis1 bcis2 ds.
  split.
  - intros ds'.
    intro H_fetch_decode_execute.
    destruct ds'.
    destruct ds.
    * Check (fold_unfold_fetch_decode_execute_loop_nil).
      
    

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

(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
*)

(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
*)

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

(*
Theorem the_compiler_emits_well_behaved_code :
  forall ae : arithmetic_expression,
    verify (compile ae) = true.
Proof.
Abort.
*)

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