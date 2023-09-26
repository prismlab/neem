module Set_extended_new

val t (a:eqtype) : eqtype

val empty (#a:eqtype) : t a

val mem (#a:eqtype) (x:a) (s:t a) : bool

val mem_empty (#a:eqtype) (x:a)
  : Lemma (not (mem x empty))
          [SMTPat (mem x empty)]

val equal (#a:eqtype) (s1 s2:t a) : Type0

val equal_intro (#a:eqtype) (s1 s2:t a)
  : Lemma (requires (forall (x:a). mem x s1 == mem x s2))
          (ensures equal s1 s2)
          [SMTPat (equal s1 s2)]

val equal_elim (#a:eqtype) (s1 s2:t a)
  : Lemma (requires equal s1 s2)
          (ensures s1 == s2)
          [SMTPat (equal s1 s2)]

let equal_refl (#a:eqtype) (s1 s2:t a)
  : Lemma (requires s1 == s2)
          (ensures (forall (x:a). mem x s1 == mem x s2))
          [SMTPat (equal s1 s2)] = ()
    
// no need to define it, it is already derivable
let equal_refl1 (#a:eqtype) (s:t a)
  : Lemma (equal s s) = ()

val insert (#a:eqtype) (x:a) (s:t a) : t a

val insert_mem (#a:eqtype) (x:a) (s:t a)
  : Lemma (requires mem x s)
          (ensures insert x s == s)
          [SMTPat (mem x s); SMTPat (insert x s)]

val mem_insert_x (#a:eqtype) (x:a) (s:t a)
  : Lemma (mem x (insert x s))
          [SMTPat (mem x (insert x s))]

val mem_insert_y (#a:eqtype) (x:a) (s:t a) (y:a)
  : Lemma (requires x =!= y)
          (ensures mem y (insert x s) == mem y s)
          [SMTPat (mem y (insert x s))]

let subset (#a:eqtype) (s1:t a) (s2:t a) =
  (forall x. mem x s1 ==> mem x s2)

val mem_subset (#a:eqtype) (s1:t a) (s2:t a)
  : Lemma (requires (forall x. mem x s1 ==> mem x s2))
          (ensures (subset s1 s2))
          [SMTPat (subset s1 s2)]

val subset_mem (#a:eqtype) (s1:t a) (s2:t a)
  : Lemma (requires (subset s1 s2))
          (ensures (forall x. mem x s1 ==> mem x s2))
          [SMTPat (subset s1 s2)]
   
val union (#a:eqtype) (s1 s2:t a) : t a

val mem_union (#a:eqtype) (s1 s2:t a) (x:a)
  : Lemma (mem x (union s1 s2) <==> (mem x s1 || mem x s2))
          [SMTPat (mem x (union s1 s2))]

val intersection (#a:eqtype) (s1 s2:t a) : t a

val mem_intersection (#a:eqtype) (s1 s2:t a) (x:a)
  : Lemma (mem x (intersection s1 s2) <==> (mem x s1 /\ mem x s2))
          [SMTPat (mem x (intersection s1 s2))]

val difference (#a:eqtype) (s1 s2:t a) : t a

val mem_difference (#a:eqtype) (s1 s2:t a) (x:a)
  : Lemma (mem x (difference s1 s2) <==> (mem x s1 /\ ~ (mem x s2)))
          [SMTPat (mem x (difference s1 s2))]
     
val filter (#a:eqtype) (s:t a) (p:a -> bool) : t a

val mem_filter (#a:eqtype) (s:t a) (p:a -> bool) (x:a)
  : Lemma (mem x (filter s p) <==> (mem x s /\ p x))
          [SMTPat (mem x (filter s p))]

// we can define exists_s rather than val?
let exists_s (#a:eqtype) (s:t a) (p:a -> bool) : bool =
  not (filter s p = empty)

val exists_mem (#a:eqtype) (s:t a) (p:a -> bool)
  : Lemma (ensures ((exists_s s p = true) <==> (exists x. mem x s /\ p x)))
    [SMTPat (exists_s s p)]
    
let forall_s (#a:eqtype) (s:t a) (p:a -> bool) : bool =
  filter s p = s

val remove (#a:eqtype) (s:t a) (x:a) : t a

val remove_non_mem (#a:eqtype) (s:t a) (x:a)
  : Lemma (requires not (mem x s))
          (ensures remove s x == s)
          [SMTPat (remove s x); SMTPat (mem x s)]

val mem_remove_x (#a:eqtype) (s:t a) (x:a)
  : Lemma (not (mem x (remove s x)))
          [SMTPat (mem x (remove s x))]

val mem_remove_y (#a:eqtype) (s:t a) (x:a) (y:a)
  : Lemma (requires x =!= y)
          (ensures mem y (remove s x) == mem y s)
          [SMTPat (mem y (remove s x))]
