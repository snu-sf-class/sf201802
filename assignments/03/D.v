(** **** SNU M1522.001200, 2018 Fall *)

(** Assignment 03 *)
(** Due: 2018/12/08 23:59 *)

(* Important: 
   - You are NOT allowed to use the [admit] tactic.
   - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.
*)

Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.
Require Export FunctionalExtensionality.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

(* useful tactics *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply beq_nat_true_iff.
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

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac inv H := inversion H; clear H; subst.

(* total_map *)

Definition total_map (A:Type) := nat -> A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : nat) (v : A) :=
  fun x' => if beq_nat x x' then v else m x'.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros. unfold t_update.
  extensionality x'.
  bdestruct (x =? x'); auto.
Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros.
  unfold t_update. extensionality x'.
  bdestruct (x1 =? x'); bdestruct (x2 =? x'); auto; omega.
Qed.


(* insertion sort *)

Fixpoint l_insert (i:nat) (l: list nat) := 
  match l with
  | nil => i::nil
  | h::t => if i <=? h then i::h::t else h :: l_insert i t
 end.

Fixpoint sort (l: list nat) : list nat :=
  match l with
  | nil => nil
  | h::t => l_insert h (sort t)
end.

Inductive sorted: list nat -> Prop := 
| sorted_nil:
    sorted nil
| sorted_1: forall x,
    sorted (x::nil)
| sorted_cons: forall x y l,
   x <= y -> sorted (y::l) -> sorted (x::y::l).

Definition sorted' (al: list nat) :=
 forall i j, i < j < length al -> nth i al 0 <= nth j al 0.


(* search tree *)

Parameter V : Type.
Parameter default: V.
Definition key := nat.


Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> V -> tree -> tree.

Definition example_tree (v2 v4 v5 : V) :=
   T (T E 2 v2 E) 4 v4 (T E 5 v5 E).

Definition empty_tree : tree := E.

Definition example_map (v2 v4 v5: V) : total_map V :=
  t_update (t_update (t_update (t_empty default) 2 v2) 4 v4) 5 v5.


Fixpoint lookup (x: key) (t : tree) : V :=
  match t with
  | E => default
  | T tl k v tr => if x <? k then lookup x tl
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
 match s with
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
 end.

Definition combine {A} (pivot: key) (m1 m2: total_map A) : total_map A :=
  fun x => if x <? pivot  then m1 x else m2 x.

Inductive Abs:  tree -> total_map V -> Prop :=
| Abs_E: Abs E (t_empty default)
| Abs_T: forall a b l k v r,
      Abs l a ->
      Abs r b ->
      Abs (T l k v r)  (t_update (combine k a b) k v).

Inductive SearchTree' : key -> tree -> key -> Prop :=
| ST_E : forall lo hi, lo <= hi -> SearchTree' lo E hi
| ST_T: forall lo l k v r hi,
    SearchTree' lo l k ->
    SearchTree' (S k) r hi ->
    SearchTree' lo (T l k v r) hi.

Inductive SearchTree: tree -> Prop :=
| ST_intro: forall t hi, SearchTree' 0 t hi -> SearchTree t.

Lemma SearchTree'_expand: forall t a b (HTREE:SearchTree' a t b) a' b'
    (HLEFT:a' <= a) (HRIGHT:b <= b'),
          SearchTree' a' t b'.
Proof.
  intros.
  generalize dependent a.
  generalize dependent b.
  generalize dependent a'.
  generalize dependent b'.
  induction t.
  - constructor. inv HTREE. omega.
  - intros. inv HTREE. constructor.
    + eapply IHt1 with (b := k) (a := a); try omega; auto.
    + eapply IHt2 with (b := b) (a := S k); try omega; auto.
Qed.

Lemma SearchTree'_range:
  forall lo hi t (HST':SearchTree' lo t hi),
    lo <= hi.
Proof.
  intros.
  induction HST'. auto. omega.
Qed.


(* red-black tree *)

Inductive color := Red | Black.

Inductive colored_tree  : Type :=
 | CE : colored_tree 
 | CT: color -> colored_tree -> key -> V -> colored_tree -> colored_tree.

Definition empty_colored_tree := CE.

Definition balance rb t1 k vk t2 :=
 match rb with Red => CT Red t1 k vk t2
 | _ => 
 match t1 with 
 | CT Red (CT Red a x vx b) y vy c =>
      CT Red (CT Black a x vx b) y vy (CT Black c k vk t2)
 | CT Red a x vx (CT Red b y vy c) =>
      CT Red (CT Black a x vx b) y vy (CT Black c k vk t2)
 | a => match t2 with 
            | CT Red (CT Red b y vy c) z vz d =>
	        CT Red (CT Black t1 k vk b) y vy (CT Black c z vz d)
            | CT Red b y vy (CT Red c z vz d)  =>
	        CT Red (CT Black t1 k vk b) y vy (CT Black c z vz d)
            | _ => CT Black t1 k vk t2
            end
  end
 end.

Inductive CAbs:  colored_tree -> total_map V -> Prop :=
| CAbs_E: CAbs CE (t_empty default)
| CAbs_T: forall a b c l k vk r,
      CAbs l a ->
      CAbs r b ->
      CAbs (CT c l k vk r)  (t_update (combine k a b) k vk).

Definition makeBlack (t:colored_tree) := 
  match t with 
  | CE => CE
  | CT _ a x vx b => CT Black a x vx b
  end.

Fixpoint rb_ins x vx s :=
 match s with 
 | CE => CT Red CE x vx CE
 | CT c a y vy b => if x <? y then balance c (rb_ins x vx a) y vy b
                        else if y <? x then balance c a y vy (rb_ins x vx b)
                        else CT c a x vx b
 end.

Definition rb_insert x vx s := makeBlack (rb_ins x vx s).

Inductive CSearchTree' : key -> colored_tree -> key -> Prop :=
| CST_E : forall lo hi, lo <= hi -> CSearchTree' lo CE hi
| CST_T: forall lo l k v r hi c,
    CSearchTree' lo l k ->
    CSearchTree' (S k) r hi ->
    CSearchTree' lo (CT c l k v r) hi.

Inductive CSearchTree: colored_tree -> Prop :=
| CST_intro: forall lo t hi, CSearchTree' lo t hi -> CSearchTree t.


