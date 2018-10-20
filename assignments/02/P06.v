Require Export P05.



(** **** Problem #6 : 3 stars (gen_dep_practice) *)

(* Prove this by induction on l. *)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof. exact FILL_IN_HERE. Qed.

