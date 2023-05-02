module Set_extended

val set (a:eqtype) : eqtype

val mem (#a:eqtype) (x:a) (s:set a) : Tot bool

val empty (#a:eqtype) : set a
val empty_mem (#a:eqtype) (x:a)
  : Lemma (ensures not (mem x empty))
    [SMTPat (mem x empty)]
  
val equal (#a:eqtype) (s1:set a) (s2:set a) : Type0
val equal_mem (#a:eqtype) (s1:set a) (s2:set a)
  : Lemma (ensures (equal s1 s2 <==> (forall e. mem e s1 <==> mem e s2)))
    [SMTPat (equal s1 s2)]

val singleton (#a:eqtype) (x:a) : set a
val singleton_mem (#a:eqtype) (x:a) (y:a) 
  : Lemma (ensures (mem y (singleton x) = (x=y)))
    [SMTPat (mem y (singleton x))]

val add (#a:eqtype) (ele:a) (s:set a) : set a
val add_mem (#a:eqtype) (ele:a) (s:set a) (x:a)
  : Lemma (ensures mem x (add ele s) <==> (mem x s \/ x == ele))
    [SMTPat (mem x (add ele s))]

val union (#a:eqtype) (s1:set a) (s2:set a) : set a
val union_mem (#a:eqtype) (s1:set a) (s2:set a) (x:a)
  : Lemma (ensures mem x (union s1 s2) <==> (mem x s1 \/ mem x s2))
    [SMTPat (mem x (union s1 s2))]

val intersect (#a:eqtype) (s1:set a) (s2:set a) : set a
val intersect_mem (#a:eqtype) (s1:set a) (s2:set a) (x:a)
  : Lemma (ensures mem x (intersect s1 s2) <==> (mem x s1 /\ mem x s2))
    [SMTPat (mem x (intersect s1 s2))]

val remove_if (#a:eqtype) (s:set a) (f:a -> bool) : set a
val remove_if_mem (#a:eqtype) (s:set a) (f:a -> bool) (x:a)
  : Lemma (ensures mem x (remove_if s f) <==> (mem x s /\ ~ (f x))) 
    [SMTPat (mem x (remove_if s f))]

val filter_s (#a:eqtype) (s:set a) (f:a -> bool) : set a
val filter_mem (#a:eqtype) (s:set a) (f:a -> bool) (x:a)
  : Lemma (ensures (mem x (filter_s s f) <==> (mem x s /\ f x)))
    [SMTPat (mem x (filter_s s f))]

val exists_s (#a:eqtype) (s:set a) (f:a -> bool) : bool
val exists_mem (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures ((exists_s s f = true) <==> (exists x. mem x s /\ f x)))
    [SMTPat (exists_s s f)]

val forall_s (#a:eqtype) (s:set a) (f:a -> bool) : bool
val forall_mem (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures ((forall_s s f = true) <==> (forall x. mem x s ==> f x)))
    [SMTPat (forall_s s f)]

val count (#a:eqtype) (ele:a) (s:set a) : nat
val mem_count (#a:eqtype) (ele:a) (s:set a)
  : Lemma (ensures ((mem ele s = true) <==> count ele s > 0))
    [SMTPat (count ele s)]

val count_if (#a:eqtype) (s:set a) (f:a -> bool) : nat
val mem_count_if (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures ((count_if s f > 0) <==> (filter_s s (fun e -> f e) <> empty)))
    [SMTPat (count_if s f)]

val extr (#a:eqtype) (x:option a{Some? x}) : (r:a{x = Some r})

val find_if (#a:eqtype) (s:set a) (f:a -> bool) : option a
val mem_find_if (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures (None? (find_if s f) <==> ((forall e. mem e s ==> ~ (f e)) \/ s = empty)) /\
                   (Some? (find_if s f) <==> (exists e. mem e s /\ f e)) /\
                   (Some? (find_if s f) ==> (exists e. mem e s /\ f e /\ e = extr (find_if s f)) /\ (f (extr (find_if s f)))))
    [SMTPat (find_if s f)]

val mem_find_if_exists (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (requires (exists e. mem e s /\ f e))
          (ensures (None? (find_if s f) <==> ((forall e. mem e s ==> ~ (f e)) \/ s = empty)) /\
                   (Some? (find_if s f) <==> (exists e. mem e s /\ f e)) /\
                   (Some? (find_if s f) ==> (exists e. mem e s /\ f e /\ e = extr (find_if s f)) /\ (f (extr (find_if s f)))) /\
                   (s <> empty ==> Some? (find_if s f)))
          [SMTPat (find_if s f)]

val always_min_exists (#a:eqtype) (s:set (nat * a)) 
  : Lemma (ensures (s <> empty ==> (exists (e:(nat * a)). mem e s /\ (forall (e1:(nat * a)). mem e1 s ==> fst e <= fst e1))))

val extract_s (#a:Type0) (m:option a{Some? m}) : (e:a{m == Some e})

val find_min (#a:eqtype) (s:set (nat * a)) 
  : (m:option (nat * a)
     {(Some? m <==> (exists (e:(nat * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1))) /\
            (Some? m ==> (exists (e:(nat * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1) /\ e = extract_s m)) /\
        (s = empty ==> (m = None \/ (~ (exists (e:(nat * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1))))) })

val mem_find_min (#a:eqtype) (s:set (nat * a))
  : Lemma (ensures (Some? (find_min s) <==> (exists (e:(nat * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1))) /\
            (Some? (find_min s) ==> (exists (e:(nat * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1) /\ e = extract_s (find_min s))) /\
        (s = empty ==> (find_min s = None \/ (~ (exists (e:(nat * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1)))))) 
        [SMTPat (find_min s)]

let unique_st (#a:eqtype) (s:set (nat * a)) =
  forall_s s (fun e -> not (exists_s s (fun e1 -> snd e <> snd e1 && fst e = fst e1)))

val remove_min (#a:eqtype) (s:set (nat * a)) 
  : (r:set (nat * a){(s = empty ==> r = s) /\
                   (s <> empty /\ Some? (find_min s) ==> (forall e. mem e r <==> (mem e s /\ e <> extract_s (find_min s)))) /\
                   (s <> empty /\ None? (find_min s) ==> (forall e. mem e r <==> mem e s))})

val mem_id_s (#a:eqtype) (id:nat) (s:set (nat * a)) 
  : (b:bool{b = true <==> (exists e. mem e s /\ fst e = id)})

val eq_min_same (#a:eqtype) (s1 s2:set (nat * a))
  : Lemma (requires equal s1 s2 /\ unique_st s1 /\ unique_st s2)
          (ensures find_min s1 = find_min s2)
