(** Mid Exam *)

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

(** Important: 

    - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.

    - You are NOT allowed to use the following tactics.

      [tauto], [intuition], [firstorder].

    - But you can use [nia], which is a powerful automation for arithmetic, better than [lia].
**)

Require Export Lia.

(**
    - you can also use classical logic.
**)

Require Export Classical.

Check classic.
Check NNPP.
Check not_and_or.
Check not_or_and.
Check not_all_ex_not.
Check not_ex_all_not.
Check not_all_not_ex.
Check not_ex_not_all.
Check imply_to_and.

(**
    - Here is the list of tactics and tacticals you have learned.

      [intros]
      [revert]
      [reflexivity]
      [simpl]
      [rewrite]
      [induction]
      [assert]
      [unfold]
      [apply] ... [with] ... [in] ...
      [destruct] ... [as] ... [eqn:] ...
      [inversion]
      [symmetry]
      [generalize dependent]
      [split]
      [exists]
      [clear]
      [subst]
      [rename] ... [into] ...
      [contradiction]
      [constructor]
      [auto]
      [repeat]
      [try]
      [remember] ... [as] ...
      [replace] ... [with] ...
      [eauto]
      [;]
**)

(* [hexploit]: A very useful tactic, developed by Gil Hur.

   Suppose we have:

     H: P1 -> ... -> Pn -> Q
     ========================
     G

   [hexploit H] turns this goal into the following (n+1) subgoals:

     H: P1 -> ... -> Pn -> Q
     =========================
     P1

     ...

     H: P1 -> ... -> Pn -> Q
     =========================
     Pn

     H: P1 -> ... -> Pn -> Q
     =========================
     Q -> G
*)

Lemma __mp__: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

Ltac hexploit H := eapply __mp__; [eapply H|].

Example hexploit_example: forall (P Q: Prop) n 
    (ASM: P /\ Q)
    (IMP: P -> Q -> n >= 5),
  n > 2.
Proof.
  intros.
  hexploit IMP.
  { destruct ASM; eauto. }
  { destruct ASM; eauto. }
  intros. nia.
Qed.  

(**
  Definition of [list] 
 **)

Require Export List.

(* Imported from the library *)

(***
Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint app (X : Type) (l1 l2 : list X)
  : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app X t l2)
  end.

Arguments app {X} l1 l2.

Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

***)

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Check (3 :: ([0; 1] ++ [])).

(**
  Definitions used in the exam problems.
 **)

Print Nat.max.

Fixpoint find_max (l: list nat) : nat :=
  match l with
  | [] => 0
  | n::tl => Nat.max (find_max tl) n
  end.

Fixpoint list_prod (l: list nat) : nat :=
  match l with
  | [] => 1
  | n :: tl => n * list_prod tl
  end.

Definition divisible d n : Prop :=
  exists q, n = d*q.

Definition prime (p: nat) : Prop :=
  (p > 1) /\
  (forall d (DIV: divisible d p), d = 1 \/ d = p).













(*=========== 3141592 ===========*)

(** Easy:
    Prove the following theorem.
 **)

Theorem disj_impl_all: forall X (P Q R: X -> Prop)
    (EX: exists x, P x \/ Q x)
    (PR: forall x, P x -> R x)
    (QR: forall x, Q x -> R x),
  exists x, R x.
Proof.
  intros.
  destruct EX as [x [EX|EX]]; eauto.
Qed.

(*-- Check --*)

Check disj_impl_all: forall X (P Q R: X -> Prop)
    (EX: exists x, P x \/ Q x)
    (PR: forall x, P x -> R x)
    (QR: forall x, Q x -> R x),
  exists x, R x.

(*=========== 3141592 ===========*)

(** Easy *)

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros. repeat rewrite H.
  destruct b; eauto.
Qed.

(*-- Check --*)

Check negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.

(*=========== 3141592 ===========*)

(** Easy:
    Define a function [sum f b n] satisfying:

      sum f b n = f(b+1) + f(b+2) + ... + f(b+n)

    Hint: Do recursion on [n].
 **)

Fixpoint sum (f: nat->nat) (b n: nat) : nat :=
  match n with
  | 0 => 0
  | S n' => f (n+b) + sum f b n'
  end.

Example sum_example1: sum (fun x => x) 2 5 = 25.
Proof. eauto. Qed.

Example sum_example2: sum (fun x => x*x) 0 10 = 385.
Proof. eauto. Qed.

Example sum_example3: sum (fun x => x*x-x) 3 4 = 104.
Proof. eauto. Qed.

(** Hard:
    Prove the following theorem.
 **)

Theorem sum_square_correct:
  forall b n (LE: n >= b),
  6 * sum (fun x => x*x) b (n-b) = n*(n+1)*(2*n+1) - b*(b+1)*(2*b+1).
Proof.
  assert (COR: forall n,
               6 * sum (fun x => x*x) 0 n = n*(n+1)*(2*n+1)).
  { induction n; eauto.
    simpl sum; nia.
  }
  assert (DIF: forall f b n, sum f b n = sum f 0 (n+b) - sum f 0 b).
  { intros. induction n; simpl; try nia.
    replace (n+b+0) with (n+b) by nia.
    assert (sum f 0 (n + b) >= sum f 0 b).
    { clear IHn. induction n; simpl; eauto; nia. }
    nia.
  }
  intros. rewrite DIF. 
  repeat rewrite <-COR.
  replace (n-b+b) with n by nia.
  nia.
Qed.

(*-- Check --*)

Check sum_example1: sum (fun x => x) 2 5 = 25.

Check sum_example2: sum (fun x => x*x) 0 10 = 385.

Check sum_example3: sum (fun x => x*x-x) 3 4 = 104.

(*-- Check --*)

Check sum_square_correct:
  forall b n (LE: n >= b),
  6 * sum (fun x => x*x) b (n-b) = n*(n+1)*(2*n+1) - b*(b+1)*(2*b+1).

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Lemma app_tail_cancel: forall X (l1 l2: list X) a b c
    (EQ: l1 ++ [a] = l2 ++ [b; c]),
  l1 = l2++[b].
Proof.
  induction l1; intros.
  - do 2 (destruct l2; try inversion EQ).
  - destruct l2.
    + inversion EQ. subst.
      destruct l1. 
      * inversion H1; subst; eauto.
      * destruct l1; inversion H1.
    + inversion EQ. subst.
      eapply IHl1 in H1. subst. eauto.
Qed.

(*-- Check --*)

Check app_tail_cancel: forall X (l1 l2: list X) a b c
    (EQ: l1 ++ [a] = l2 ++ [b; c]),
  l1 = l2++[b].

(*=========== 3141592 ===========*)

(** Medium:
    Prove the theorem [find_max_in].
 **)

(* [find_max l] finds the maximum number in the list [l].
*)

Print find_max.

(* Here is a copy of the definition of [find_max].

Fixpoint find_max (l: list nat) : nat :=
  match l with
  | [] => 0
  | n::tl => Nat.max n (find_max tl)
  end.
*)

Check In.
(* Defintion of [In] is as follows.

Fixpoint In (A: Type) (a: A) (l: list A) : Prop :=
  match l with
  | [] => False
  | b :: m => b = a \/ In A a m
  end.
*)

(* Hint: [nia] understands [Nat.max] well.
         Use [nia] to prove properties about [Nat.max].
*)

Theorem find_max_in: forall l (NotNil: l <> []), In (find_max l) l.
Proof.
  induction l; intros; simpl; eauto.
  destruct l; eauto.
  assert (MAX: a = Nat.max (find_max (n::l)) a \/
               find_max (n::l) = Nat.max (find_max (n::l)) a) by nia.
  destruct MAX; eauto.
  simpl in *. rewrite <- H.
  right. apply IHl.
  intro X. inversion X.
Qed.

(** Medium:
    Prove the correctness of [find_max].
 **)

(*-- Check --*)

Check find_max_in: forall l (NotNil: l <> []), In (find_max l) l.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the theorem [find_max_ge].
 **)

(* Hint: [nia] understands [Nat.max] well.
         Use [nia] to prove properties about [Nat.max].
*)

Theorem find_max_ge: forall n l (IN: In n l), n <= find_max l.
Proof.
  intros. generalize dependent n. 
  induction l; intros; inversion IN; subst; simpl.
  - nia.
  - apply IHl in H. nia.
Qed.

(*-- Check --*)

Check find_max_ge: forall n l (IN: In n l), n <= find_max l.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem [Forall_app].
 **)

Check Forall.
(* Definition of [Forall] is as follows.

Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
| Forall_nil : 
    Forall P [] 
| Forall_cons : 
    forall (x : A) (l : list A), 
    P x -> Forall P l -> Forall P (x :: l).
*)

Lemma Forall_app:
  forall A (l1 l2: list A) P
    (FA1: Forall P l1)
    (FA2: Forall P l2),
  Forall P (l1 ++ l2).
Proof.
  induction l1; eauto.
  intros. inversion FA1. subst.
  constructor; eauto.
Qed.

(*-- Check --*)

Check Forall_app:
  forall A (l1 l2: list A) P
    (FA1: Forall P l1)
    (FA2: Forall P l2),
  Forall P (l1 ++ l2).

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem [non_prime_divisible].
 **)

Print divisible.

Print prime.

Lemma non_prime_divisible:
  forall n (LT: n > 1) (NP: ~ prime n), 
  exists p q, n = p*q /\ 1 < p /\ 1 < q.
Proof.
  intros.
  apply not_and_or in NP.
  destruct NP as [NP|NP]; try nia.
  apply not_all_ex_not in NP.
  destruct NP as [m NP].
  apply imply_to_and in NP.
  destruct NP as [[q DIV] NP].
  subst. apply not_or_and in NP.
  destruct NP as [M1 MQ].
  exists m, q; repeat split; eauto; nia.
Qed.

(*-- Check --*)

Check non_prime_divisible:
  forall n (LT: n > 1) (NP: ~ prime n), 
  exists p q, n = p*q /\ 1 < p /\ 1 < q.

(*=========== 3141592 ===========*)

(** Hard:
    Prove the following theorem [prime_factorization].
 **)

Lemma list_prod_app:
  forall l1 l2,
  list_prod l1 * list_prod l2 = list_prod (l1 ++ l2).
Proof.
  induction l1; simpl; intros; eauto.
  rewrite <-IHl1. nia.
Qed.

Lemma prime_factorization:
  forall n (NZ: n > 0), 
  exists l, Forall prime l /\ n = list_prod l.
Proof.
  assert(GEN: 
    forall n m (LE: 0 < m <= n),
    exists l, Forall prime l /\ m = list_prod l); eauto.
  induction n; intros; try nia.
  destruct LE as [GT LE].
  assert (LEEQ: m <= n \/ m = S n) by nia.
  destruct LEEQ.
  { eapply IHn; nia. }
  subst. clear LE GT.
  destruct (classic (prime (S n))) as [|NP].
  { exists [S n]; simpl; split; eauto; nia. }
  destruct n. 
  { exists nil. split; simpl; eauto; nia. }
  apply non_prime_divisible in NP; try nia.
  destruct NP as [p [q [EQ [GP GQ]]]].
  hexploit (IHn p); try nia. intros [lp [LP LPM]].
  hexploit (IHn q); try nia. intros [lq [LQ LQM]].
  exists (lp ++ lq).
  rewrite EQ. subst.
  eauto using Forall_app, list_prod_app.
Qed.

(*-- Check --*)

Check prime_factorization:
  forall n (NZ: n > 0), 
  exists l, Forall prime l /\ n = list_prod l.
