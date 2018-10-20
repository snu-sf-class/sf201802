Require Import P11.



Check excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).

