Require Import P01.



Check permut_example: forall (a b: list nat),
  Permutation (5::6::a++b) ((5::b)++(6::a++[])).

