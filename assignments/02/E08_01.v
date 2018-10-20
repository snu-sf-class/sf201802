Require Import P08.



Check not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).

