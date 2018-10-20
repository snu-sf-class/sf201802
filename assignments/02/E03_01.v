Require Import P03.



Check @map_rev: forall (X Y:Type) (f:X -> Y) (l:list X),
    map f (rev l) = rev (map f l).

