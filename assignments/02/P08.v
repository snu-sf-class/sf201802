Require Export P07.



(** **** Problem #8 : 2 stars (not_implies_our_not) *)

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof. exact FILL_IN_HERE. Qed.

