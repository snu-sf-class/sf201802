Require Export P04.



(** **** Problem #5 : 1 star (inversion_ex3) *)
Example inversion_ex3 : forall (X : Type) (x y z w : X) (l j : list X),
  x :: y :: l = w :: z :: j ->
  x :: l = z :: j ->
  x = y.
Proof. exact FILL_IN_HERE. Qed.

