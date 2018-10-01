Require Import P10.



Check fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.

