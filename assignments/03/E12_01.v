Require Import P12.



Check insert_SearchTree'_noexpand:
  forall t a b k v (HST':SearchTree' a t b)
         (HLT:a <= k < b),
    SearchTree' a (insert k v t) b.

