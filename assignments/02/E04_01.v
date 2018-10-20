Require Import P04.



Check @partition: forall (X:Type) (test:X -> bool) (l:list X), list X * list X.
Check test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Check test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).

