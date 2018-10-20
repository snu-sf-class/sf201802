Require Export P02.



(** **** Problem #3 : 3 stars (map_rev) *)

(* Show that map and rev commute. You may need to define an auxiliary lemma. *)
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof. exact FILL_IN_HERE. Qed.

