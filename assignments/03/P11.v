Require Export P10.



(** **** Exercise: 3 stars (insert_relate)  *)

Check t_update_shadow.
Check t_update_permute.

Theorem insert_relate:
 forall k v t cts,
    Abs t cts ->
    Abs (insert k v t) (t_update cts k v).
Proof. exact FILL_IN_HERE. Qed.


