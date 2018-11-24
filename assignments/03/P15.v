Require Export P14.



(** **** Exercise: 4 stars (balance_relate)  *)
(** You will need proof automation for this one.  Study Redblack chapter
  and try this problem. Add one clause at a time to your [match goal]. *)

Ltac contents_equivalent_prover :=
 extensionality x; unfold t_update, combine, t_empty;
 repeat match goal with
  | |- context [if ?A then _ else _] => bdestruct A
 end;
 auto;
 omega.

Lemma CAbs_helper:
  forall m' t m, CAbs t m' ->    m' = m ->     CAbs t m.
Proof.
   intros. subst. auto.
Qed.

Lemma CSearchTree'_le:
  forall lo t hi, CSearchTree' lo t hi -> lo <= hi.
Proof.
induction 1; omega.
Qed.

Theorem balance_relate:
  forall c l k vk r m,
    CSearchTree (CT c l k vk r) ->
    CAbs (CT c l k vk r) m ->
    CAbs (balance c l k vk r) m.
Proof. exact FILL_IN_HERE. Qed.


