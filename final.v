(** Final Exam *)

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

(** Important: 

    - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.

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

Export ListNotations.

Check (3 :: ([0; 1] ++ [])).


Require Export Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.Lists.List.
Require Export Permutation.
Require Export FunctionalExtensionality.

(* ################################################################# *)
(** * The Less-Than Order on the Natural Numbers *)

(** These [Check] and [Locate] commands remind us about
  _Propositional_ and the _Boolean_ less-than operators
  in the Coq standard library. *)

Check Nat.lt.        (* : nat -> nat -> Prop *)
Check lt.             (* : nat -> nat -> Prop *)
Goal Nat.lt = lt. Proof. reflexivity. Qed. (* They are the same *)
Check Nat.ltb.       (* : nat -> nat -> bool *)
Locate "_ < _".  (* "x < y" := lt x y *)
Locate "<?".     (* x <? y  := Nat.ltb x y *)

(** We write [x < y] for the Proposition that [x] _is_ less than [y],
    and we write [x <? y] for the computable _test_ that returns
    [true] or [false] depending on whether [x<y].  The theorem that
    [lt] is related in this way to [ltb] is this one: *)

Check Nat.ltb_lt.
(* : forall n m : nat, (n <? m) = true <-> n < m *)

(** For some reason, the Coq library has [ <? ] and [ <=? ]
    notations, but is missing these three: *)

Notation  "a >=? b" := (Nat.leb b a)
                          (at level 70, only parsing) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a)
                       (at level 70, only parsing) : nat_scope.
Notation " a =? b"  := (beq_nat a b)
                       (at level 70) : nat_scope.

(* ================================================================= *)
(** ** Relating [Prop] to [bool] *)

(** The [reflect] relation connects a [Proposition] to a [Boolean]. *)

Print reflect.

(* Inductive reflect (P : Prop) : bool -> Type :=  *)
(* | ReflectT : P -> reflect P true  *)
(* | ReflectF : ~ P -> reflect P false *)
(* . *)

(** That is, [reflect P b] means that [P<->True] if and only if [b=true].
     The way to use [reflect] is, for each of your operators, make a
     lemma like these next three:
*)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. 
  symmetry.  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

(** Here's an example of how you could use these lemmas.
    Suppose you have this simple program, [(if a <? 5 then a else 2)],
    and you want to prove that it evaluates to a number smaller than 6.
    You can use [blt_reflect] "by hand": *)

Example reflect_example1: forall a, (if a<?5 then a else 2) < 6.
Proof.
  intros.
  destruct (blt_reflect a 5) as [H|H].
  - (* Notice that [H] above the line has a [Prop]ositional
       fact _related_ to [a<?5]*)
    lia.
     (* omega.  (* More explanation of [omega] late *)r in this chapter. *)
  - (* Notice that [H] above the line has a a _different_
       [Prop]ositional fact. *)
    lia.
     (* apply not_lt in H.  (* This step is not necessary, *)
     (*      it just makes the hypothesis [H] look pretty *) *)
     (* omega. *)
Qed.

(** But there's another way to use [blt_reflect], etc: read on. *)

(* ================================================================= *)
(** ** Some Advanced Tactical Hacking *)
(** You may skip ahead to "Inversion/clear/subst".
     Right here, we build some machinery that you'll want to
     _use_, but you won't need to know how to _build_ it.

    Let's put several of these [reflect] lemmas into a Hint database,
    called [bdestruct] because we'll use it in our boolean-destruction
    tactic: *)

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

(** Our high-tech _boolean destruction_ tactic: *)

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(** Here's a brief example of how to use [bdestruct].  There
     are more examples later. *)

Example reflect_example2: forall a, (if a<?5 then a else 2) < 6.
Proof.
  intros.
  bdestruct (a<?5).  (* instead of: [destruct (blt_reflect a 5) as [H|H]]. *)
  * (* Notice that [H] above the line has a [Prop]ositional
       fact _related_ to [a<?5]*)
     nia.  (* More explanation of [omega] later in this chapter. *)
  * (* Notice that [H] above the line has a a _different_
       [Prop]ositional fact. We don't need to apply [not_lt],
       as [bdestruct] has already done it. *)
     nia.
Qed.

(* ================================================================= *)
(** ** [inversion] / [clear] / [subst] *)
(** Coq's [inversion H] tactic is so good at extracting information
    from the hypothesis [H] that [H] becomes completely redundant,
    and one might as well [clear] it from the goal.  Then, since the
    [inversion] typically creates some equality facts, why not then
    [subst] ?   This motivates the following useful tactic, [inv]:  *)

Ltac inv H := inversion H; clear H; subst.

Inductive sorted: list nat -> Prop := 
| sorted_nil:
    sorted nil
| sorted_1: forall x,
    sorted (x::nil)
| sorted_cons: forall x y l,
   x <= y -> sorted (y::l) -> sorted (x::y::l).
Hint Constructors sorted.

(***
  Monads
 ***)

Polymorphic Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

(* Left-to-right composition of Kleisli arrows. *)
Definition mcompose@{c d}
           {m:Type@{d}->Type@{c}}
           {M: Monad m}
           {T U V:Type@{d}}
           (f: T -> m U) (g: U -> m V): (T -> m V) :=
  fun x => bind (f x) g.

Delimit Scope monad_scope with monad.

Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 51, right associativity) : monad_scope.
Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 50, left associativity) : monad_scope.

Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity) : monad_scope.

Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
  (at level 100, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
  (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

Open Scope monad_scope.


(**
  Definitions used in the exam problems.
 **)

Fixpoint count_elmt (e: nat) (l: list nat) : nat :=
  match l with
  | [] => 0
  | hd::tl => (if hd =? e then 1 else 0) + count_elmt e tl
  end.

Fixpoint find_min_rest hd (tl: list nat) : nat * list nat :=
  match tl with
  | [] => (hd, [])
  | hd'::tl' => 
    let (min, rest) := find_min_rest hd' tl' in
    if hd <=? min then (hd, min::rest) else (min, hd::rest)
  end.

Fixpoint bubble_sort_aux (n: nat) (l: list nat) : list nat :=
  match n with
  | 0 => l
  | S n' =>
    match l with
    | [] => []
    | hd::tl =>
      let (min, rest) := find_min_rest hd tl in
      min :: bubble_sort_aux n' rest
    end
  end.

Definition bubble_sort l := bubble_sort_aux (length l) l.

Class NArray@{d c} (m : Type@{d} -> Type@{c}) `{Monad m} : Type :=
{ len : m nat
; read : forall i : nat, m nat
; write : forall i v : nat, m unit
; run : forall {T} (n v : nat) (c: m T), T
}.

Definition NA_list := fun T => list nat -> list nat * T.

Instance Monad_list : Monad NA_list :=
{ ret T x l := (l,x)
; bind T U m f l := let (l',v) := m l in f v l'
}.

Fixpoint list_update (l: list nat) i v : list nat :=
  match l with
  | [] => []
  | hd::tl => 
    match i with
    | 0 => v::tl
    | S i' => hd :: list_update tl i' v
    end
  end.

Fixpoint list_init n v : list nat :=
  match n with
  | 0 => []
  | S n' => v :: list_init n' v
  end.

Instance NArray_list : NArray (fun T => list nat -> list nat * T) :=
{ len l := (l, length l)
; read i l := (l, nth_default 0 l i)
; write i v l := (list_update l i v, tt)
; run T n v c := snd (c (list_init n v))
}.

Fixpoint NAfor {m} `{NArray m} (init cnt: nat) (body: nat -> m unit) : m unit :=
  match cnt with
  | 0 => ret tt
  | S cnt' => NAfor init cnt' body ;; body (init+cnt')
  end.

(*=========== 3141592 ===========*)

Theorem permutation_count: forall (l1 l2: list nat) e
    (PERM: Permutation l1 l2),
  count_elmt e l1 = count_elmt e l2.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check permutation_count: forall (l1 l2: list nat) e
    (PERM: Permutation l1 l2),
  count_elmt e l1 = count_elmt e l2.

(*=========== 3141592 ===========*)

Theorem Forall_perm: forall A (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check Forall_perm: forall A (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.

(*=========== 3141592 ===========*)

(* Hint: 
     The tactic [destruct (find_min_rest .. ..) eqn: ..] may be useful.
     The lemmma [Forall_impl] may be useful.
 *)
Check Forall_impl.

Theorem find_min_rest_minimum : 
  forall hd tl min rest
    (RES: find_min_rest hd tl = (min,rest)),
  Forall (fun e => min <= e) rest.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check find_min_rest_minimum : 
  forall hd tl min rest
    (RES: find_min_rest hd tl = (min,rest)),
  Forall (fun e => min <= e) rest.

(*=========== 3141592 ===========*)

(* Hint: 
     The tactic [destruct (find_min_rest .. ..) eqn: ..] may be useful.
     The lemmma [Permutation_trans] may be useful.
 *)

Theorem find_min_rest_permutation : 
  forall hd tl min rest
    (RES: find_min_rest hd tl = (min,rest)),
  Permutation (hd::tl) (min::rest).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check find_min_rest_permutation : 
  forall hd tl min rest
    (RES: find_min_rest hd tl = (min,rest)),
  Permutation (hd::tl) (min::rest).

(*=========== 3141592 ===========*)

Theorem bubble_sort_permutation : 
  forall l,
  Permutation l (bubble_sort l).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check bubble_sort_permutation : 
  forall l,
  Permutation l (bubble_sort l).

(*=========== 3141592 ===========*)

(* 20 points *)

Theorem bubble_sort_sorted : 
  forall l,
  sorted (bubble_sort l).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check bubble_sort_sorted : 
  forall l,
  sorted (bubble_sort l).

(*-- Check --*)

Check bubble_sort_sorted : 
  forall l,
  sorted (bubble_sort l).

(*=========== 3141592 ===========*)

Definition sorting {m} `{NArray m} : m unit := FILL_IN_HERE.

Example sorting_test1:
  fst (sorting ([1; 8; 3; 2])) = [1; 2; 3; 8].
Proof. (* reflexivity. *) Admitted.

Example sorting_test2:
  fst (sorting ([3; 1; 2; 1; 8; 2])) = [1; 1; 2; 2; 3; 8].
Proof. (* reflexivity. *) Admitted.

(*-- Check --*)

Check sorting_test1:
  fst (sorting ([1; 8; 3; 2])) = [1; 2; 3; 8].

Check sorting_test2:
  fst (sorting ([3; 1; 2; 1; 8; 2])) = [1; 1; 2; 2; 3; 8].

