Require Export P12.



(** **** Exercise: 3 stars (insert_SearchTree)  *)

Check SearchTree'_range.
Check SearchTree'_expand.


Theorem insert_SearchTree:
  forall k v t,
   SearchTree t -> SearchTree (insert k v t).
Proof. exact FILL_IN_HERE. Qed.


