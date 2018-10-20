Require Export P03.



(** **** Problem #4 : 3 stars (partition) *)

(* Use filter to write a Coq function partition.
   Given a set X, a test function of type X -> bool and a list X, partition
   should return a pair of lists. The first member of the pair is the sublist
   of the original list containing the elements that satisfy the test,
   and the second is the sublist containing those that fail the test.
   The order of elements in the two sublists should be the same as their
   order in the original list. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X := FILL_IN_HERE.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. exact FILL_IN_HERE. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. exact FILL_IN_HERE. Qed.

