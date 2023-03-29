module Set_extended

open FStar.Set

val remove_if (#a:eqtype) (s:set a) (f:a -> bool) : set a
val remove_if_mem (#a:eqtype) (s:set a) (f:a -> bool) (x:a)
  : Lemma (ensures mem x (remove_if s f) <==> (mem x s /\ ~ (f x))) 
    [SMTPat (mem x (remove_if s f))]

val filter_s (#a:eqtype) (s:set a) (f:a -> bool) : set a
val filter_mem (#a:eqtype) (s:set a) (f:a -> bool) (x:a)
  : Lemma (ensures (mem x (filter_s s f) <==> (mem x s /\ f x)))
    [SMTPat (mem x (filter_s s f))]

val exists_s (#a:eqtype) (s:set a) (f:a -> bool) : prop
val exists_mem (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures (exists_s s f <==> (exists x. mem x s /\ f x)))
    [SMTPat (exists_s s f)]
