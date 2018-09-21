(** **** SNU M1522.001200, 2018 Fall *)

(** Assignment 01 *)
(** Due: 2018/10/04 23:59 *)

(* Important: 
   - You are NOT allowed to use the [admit] tactic.

   - You are NOT allowed to use the following tactics.
     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.
*)

Require Import Basics.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** The following function doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Definition fst := 
  fun (p : natprod) =>
  match p with
  | (x, y) => x
  end.

Definition snd (p : natprod) : nat := 
  match p with
  | (x, y) => y
  end.

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

(*** 
   See the chapter "Lists" for explanations of the following.
 ***)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Theorem app_assoc : forall l1 l2 l3 : natlist, 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).   
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.  
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.


(*=========== 3141592 ===========*)

(** **** Problem #2: 1 star (factorial) *)
(** Recall the standard factorial function:
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. 

    Note that plus and multiplication are already defined in Coq.
    use "+" for plus and "*" for multiplication.
*)

Eval compute in 3 * 5.
Eval compute in 3+5*6.

Fixpoint factorial (n:nat) : nat := 
  FILL_IN_HERE.

Example test_factorial1:          (factorial 3) = 6.
Proof. exact FILL_IN_HERE. Qed.
Example test_factorial2:          (factorial 5) = 10 * 12.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check 
(conj test_factorial1
(test_factorial2))
:
(factorial 3) = 6 /\
(factorial 5) = 10 * 12.

(*=========== 3141592 ===========*)

(** **** Problem #3: 2 stars (blt_nat) *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Use [Fixpoint] to define it. *)

Fixpoint blt_nat (n m : nat) : bool :=
  FILL_IN_HERE.

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. exact FILL_IN_HERE. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. exact FILL_IN_HERE. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check 
(conj test_blt_nat1
(conj test_blt_nat2
(test_blt_nat3)))
:
(blt_nat 2 2) = false /\
(blt_nat 2 4) = true /\
(blt_nat 4 2) = false.

(*=========== 3141592 ===========*)

(** **** Problem #1 : 2 stars (mult_S_1) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.

(*=========== 3141592 ===========*)

(** **** Problem #2 : 1 star (zero_nbeq_plus_1) *)

(* See the base file for the definition of [beq_nat] below. *)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.

(*=========== 3141592 ===========*)

(** **** Problem #3 : 2 stars (boolean functions) *)
(** Use the tactics you have learned so far to prove the following 
    theorem about boolean functions. *)

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.

(*=========== 3141592 ===========*)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. 
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check plus_comm : forall n m : nat,
  n + m = m + n.

(*=========== 3141592 ===========*)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. 
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.

(*=========== 3141592 ===========*)

(** **** Problem : 2 stars (double_plus) *)

(* See [D.v] for the definition of [double] *)

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check double_plus : forall n, double n = n + n .

(*=========== 3141592 ===========*)

(** **** Problem : 3 stars (mult_comm) *)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.  
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).

(*=========== 3141592 ===========*)

(** **** Problem #10 : 1 star, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.  
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.

(*=========== 3141592 ===========*)

(** **** Problem #2 : 3 stars, advanced (alternate) *)
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  FILL_IN_HERE.

Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. exact FILL_IN_HERE. Qed.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
Proof. exact FILL_IN_HERE. Qed.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
Proof. exact FILL_IN_HERE. Qed.
Example test_alternate4:        alternate [] [20;30] = [20;30].
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check 
(conj test_alternate1
(conj test_alternate2
(conj test_alternate3
(test_alternate4))))
:
alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6] /\
alternate [1] [4;5;6] = [1;4;5;6] /\
alternate [1;2;3] [4] = [1;4;2;3] /\
alternate [] [20;30] = [20;30].

(*=========== 3141592 ===========*)

(** **** Problem #3 : 3 stars (list_exercises) *)
(** More practice with lists. *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
  exact FILL_IN_HERE.
Qed.  

(*-- Check --*)
Check app_nil_end : forall l : natlist, 
  l ++ [] = l.   

(*=========== 3141592 ===========*)

(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check rev_involutive : forall l : natlist,
  rev (rev l) = l.

(*=========== 3141592 ===========*)

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].

(*=========== 3141592 ===========*)

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).

