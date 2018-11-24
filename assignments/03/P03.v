Require Export P02.



(** **** Exercise: 3 stars (l_insert_perm)  *)
(** Prove the following auxiliary lemma, [l_insert_perm], which will be
    useful for proving [sort_perm].  Your proof will be by
    induction, but you'll need some of the permutation facts from the
    library, so first remind yourself by doing [Search]. *)

Lemma l_insert_perm: forall x l, Permutation (x::l) (l_insert x l).
Proof. exact FILL_IN_HERE. Qed.


