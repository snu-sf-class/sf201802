Require Export P08.



(** **** Exercise: 2 stars (check_example_map)  *)
(** Prove that [example_map] is the right one.
     You will probably need the [bdestruct] tactic, and [omega].
     For the beginning part of the proof, you can get hints from
     SearchTree chapter *)
Lemma check_example_map:
  forall v2 v4 v5, Abs (example_tree v2 v4 v5) (example_map v2 v4 v5).
Proof. exact FILL_IN_HERE. Qed.


