Require Import P15.



Check balance_relate:
  forall c l k vk r m,
    CSearchTree (CT c l k vk r) ->
    CAbs (CT c l k vk r) m ->
    CAbs (balance c l k vk r) m.