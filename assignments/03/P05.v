Require Export P04.



(** **** Exercise: 4 stars (l_insert_sorted)  *)
(** This one is a bit tricky.  However, there just a single induction
   right at the beginning, and you do _not_ need to use [l_insert_perm]
   or [sort_perm]. *)

Lemma l_insert_sorted:
  forall a l, sorted l -> sorted (l_insert a l).
Proof. exact FILL_IN_HERE. Qed.


