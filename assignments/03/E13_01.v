Require Import P13.



Check insert_SearchTree:
  forall k v t,
   SearchTree t -> SearchTree (insert k v t).

