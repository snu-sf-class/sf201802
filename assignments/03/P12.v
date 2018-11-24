Require Export P11.



(** **** Exercise: 2 stars (insert_SearchTree'_noexpand)  *)
Lemma insert_SearchTree'_noexpand:
  forall t a b k v (HST':SearchTree' a t b)
         (HLT:a <= k < b),
    SearchTree' a (insert k v t) b.
Proof. exact FILL_IN_HERE. Qed.


