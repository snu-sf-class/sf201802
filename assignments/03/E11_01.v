Require Import P11.



Check insert_relate:
 forall k v t cts,
    Abs t cts ->
    Abs (insert k v t) (t_update cts k v).

