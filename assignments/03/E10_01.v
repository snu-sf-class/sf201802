Require Import P10.



Check t_update_combine_l:
  forall k V (a b: total_map V) v0 k0 (HLT:k0 < k),
  t_update (combine k a b) k0 v0 = combine k (t_update a k0 v0) b.

