Require Import P05.



Check l_insert_sorted:
  forall a l, sorted l -> sorted (l_insert a l).

