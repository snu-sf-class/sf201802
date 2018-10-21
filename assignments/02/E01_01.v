Require Import P01.



Check @hd_error: forall (X:Type), list X -> option X.
Check test_hd_error1: hd_error [1;2] = Some 1.
Check test_hd_error2: hd_error [[1];[2]] = Some [1].
Check test_hd_error3: @hd_error nat [] = None.
