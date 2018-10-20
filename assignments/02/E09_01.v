Require Import P09.



Check In_app_iff : forall A (l:list A) (l':list A) (a:A),
  In a (l++l') <-> In a l \/ In a l'.

