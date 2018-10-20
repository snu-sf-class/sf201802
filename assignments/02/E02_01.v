Require Import P02.



Check filter_even_gt7: list nat -> list nat.
Check test_filter_even_gt7_1:
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Check test_filter_even_gt7_2:
  filter_even_gt7 [5;2;6;19;129] = [].

