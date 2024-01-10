module Set_extended

val t (a:eqtype) : Type0

val empty (#a:eqtype) : t a
val singleton (#a:eqtype) (x:a) : t a
val mem (#a:eqtype) (x:a) (s:t a) : bool
val equal (#a:eqtype) (s1:t a) (s2:t a) : Type0
val union (#a:eqtype) (s1 s2:t a) : t a
val intersection (#a:eqtype) (s1 s2:t a) : t a
val complement : #a:eqtype -> (s:t a) -> t a
val difference (#a:eqtype) (s1 s2:t a) : t a
val filter (#a:eqtype) (s:t a) (p:a -> bool) : t a
val remove (#a:eqtype) (s:t a) (x:a) : t a

val mem_empty (#a:eqtype) (x:a)
  : Lemma (not (mem x empty))
          [SMTPat (mem x empty)]

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
          (ensures (forall (x:a). mem x s1 == mem x s2) /\ equal s1 s2)
          [SMTPat (equal s1 s2)] = ()

// no need to define it, it is already derivable
let equal_refl1 (#a:eqtype) (s:t a)
  : Lemma (equal s s) = ()

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
   
val mem_union (#a:eqtype) (s1 s2:t a) (x:a)
  : Lemma (mem x (union s1 s2) <==> (mem x s1 || mem x s2))
          [SMTPat (mem x (union s1 s2))]

val mem_singleton: #a:eqtype -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) = (x=y)))
   [SMTPat (mem y (singleton x))]
   
let add (#a:eqtype) (x:a) (s:t a) : t a =
  union s (singleton x)

val mem_intersection (#a:eqtype) (s1 s2:t a) (x:a)
  : Lemma (mem x (intersection s1 s2) <==> (mem x s1 /\ mem x s2))
          [SMTPat (mem x (intersection s1 s2))]

val mem_complement (#a:eqtype) (s:t a) (x:a) 
  : Lemma (mem x (complement s) = not (mem x s))
   [SMTPat (mem x (complement s))]
   
val mem_difference (#a:eqtype) (s1 s2:t a) (x:a)
  : Lemma (mem x (difference s1 s2) <==> (mem x s1 /\ ~ (mem x s2)))
          [SMTPat (mem x (difference s1 s2))]
   
val mem_filter (#a:eqtype) (s:t a) (p:a -> bool) (x:a)
  : Lemma (mem x (filter s p) <==> (mem x s /\ p x))
          [SMTPat (mem x (filter s p))]

val mem_remove_x (#a:eqtype) (s:t a) (x:a)
  : Lemma (not (mem x (remove s x)))
          [SMTPat (mem x (remove s x))]

val mem_remove_y (#a:eqtype) (s:t a) (x:a) (y:a)
  : Lemma (requires x =!= y)
          (ensures mem y (remove s x) == mem y s)
          [SMTPat (mem y (remove s x))]
          
