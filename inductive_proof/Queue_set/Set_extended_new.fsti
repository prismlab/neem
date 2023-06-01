module Set_extended_new

val set (a:eqtype) : eqtype

val mem (#a:eqtype) (x:a) (s:set a) : Tot bool

val empty (#a:eqtype) : set a

val empty_mem (#a:eqtype) (x:a)
  : Lemma (ensures not (mem x empty))
    [SMTPat (mem x empty)]
  
val equal (#a:eqtype) (s1:set a) (s2:set a) : Type0

val equal_intro (#a:eqtype) (s1 s2:set a)
  : Lemma (requires (forall x. mem x s1 = mem x s2))
          (ensures (equal s1 s2))
          [SMTPat (equal s1 s2)]

val equal_elim (#a:eqtype) (s1 s2:set a)
  : Lemma (requires (equal s1 s2))
          (ensures (s1 == s2))
          [SMTPat (equal s1 s2)]

val equal_refl (#a:eqtype) (s1 s2:set a)
  : Lemma (requires (s1 == s2))
          (ensures (equal s1 s2))
          [SMTPat (equal s1 s2)]

val add (#a:eqtype) (ele:a) (s:set a) : set a

val add_mem (#a:eqtype) (ele:a) (s:set a) (x:a)
  : Lemma (ensures (mem ele s ==> (add ele s == s)) /\
                   (not (mem ele s) ==> (mem x (add ele s) <==> (mem x s \/ x == ele))))
    [SMTPat (mem x (add ele s))]
    
val union (#a:eqtype) (s1 s2:set a) : set a

val union_mem (#a:eqtype) (s1 s2:set a) (x:a)
  : Lemma (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
    [SMTPat (mem x (union s1 s2))]

val intersect (#a:eqtype) (s1 s2:set a) : set a

val intersect_mem (#a:eqtype) (s1 s2:set a) (x:a)
  : Lemma (ensures (mem x (intersect s1 s2)) = (mem x s1 && mem x s2))
    [SMTPat (mem x (intersect s1 s2))]

val diff (#a:eqtype) (s1 s2:set a) : set a

val diff_mem (#a:eqtype) (s1 s2:set a) (x:a)
  : Lemma (ensures (mem x (diff s1 s2)) = (mem x s1 && not (mem x s2))) 
    [SMTPat (mem x (diff s1 s2))]
    
val filter_s (#a:eqtype) (s:set a) (f:a -> bool) : set a

val filter_mem (#a:eqtype) (s:set a) (f:a -> bool) (x:a)
  : Lemma (ensures ((mem x (filter_s s f)) = (mem x s && f x)))
    [SMTPat (mem x (filter_s s f))]

val exists_s (#a:eqtype) (s:set a) (f:a -> bool) : bool

val exists_mem (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures ((exists_s s f == true) == (exists x. mem x s /\ f x)))
    [SMTPat (exists_s s f)]

val forall_s (#a:eqtype) (s:set a) (f:a -> bool) : bool

val forall_mem (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures ((forall_s s f == true) == (forall x. mem x s ==> f x)))
    [SMTPat (forall_s s f)]

val extract (#a:Type0) (x:option a{Some? x}) : (r:a{x == Some r})

val find_if (#a:eqtype) (s:set a) (f:a -> bool) : option a

val mem_find_if (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures (None? (find_if s f) = (forall_s s (fun e -> not (f e)))) /\
                   (Some? (find_if s f) = (exists_s s (fun e -> f e))) /\
                   (Some? (find_if s f) ==> (exists_s s (fun e -> f e && e = extract (find_if s f))) && f (extract (find_if s f))))
    [SMTPat (find_if s f)]

type order =
  | Lt | Eq | Gt

type comparator 'a = ('a -> 'a -> order)

//sample
let pos_comparator : comparator pos = 
  (fun x y ->
    if x < y then Lt
    else if x > y then Gt
    else Eq)
    
let compare (#a:eqtype) (x y:a) (comp:comparator a) : order =
  comp x y

val le (#a:eqtype) (e e1:a) : bool
val lt (#a:eqtype) (e e1:a) : bool
val ne (#a:eqtype) (e e1:a) : bool

val always_min_exists (#a:eqtype) (s:set a)
  : Lemma (ensures (s <> empty ==> (exists e. mem e s /\ (forall e1. mem e1 s ==> le e e1))))

val find_min (#a:eqtype) (s:set a) 
  : (m:option a{(Some? m <==> (exists e. mem e s /\ (forall e1. mem e1 s ==> le e e1))) /\
         (Some? m ==> (exists e. (mem e s /\ (forall e1. (mem e1 s /\ ne e e1) ==> lt e e1) /\ e = extract m))) /\
                        (s = empty <==> m = None) /\
                        (Some? m ==> mem (extract m) s)})

(*let unique_st (#a:eqtype) (s:set a) =
  forall_s s (fun e -> not (exists_s s (fun e1 -> snd e <> snd e1 && fst e = fst e1)))*)

val remove_min (#a:eqtype) (s:set a)
  : (r:set a{(s = empty <==> r = s) /\
                   (s <> empty /\ Some? (find_min s) ==> (forall e. mem e r <==> (mem e s /\ e <> extract (find_min s)))) /\
                   (s <> empty /\ None? (find_min s) ==> (forall e. mem e r <==> mem e s))})

val mem_remove_min (#a:eqtype) (s:set a)
  : Lemma (ensures (let r = remove_min s in
                   (s = empty <==> r = s) /\
                   (s <> empty /\ Some? (find_min s) ==> (forall e. mem e r <==> (mem e s /\ e <> extract (find_min s)))) /\
                   (s <> empty /\ None? (find_min s) ==> (forall e. mem e r <==> mem e s)) /\
                   ((exists ele. (forall e. mem e s <==> e = ele)) ==> r = empty)))
    [SMTPat (remove_min s)]

(*val mem_id_s (#a:eqtype) (id:pos) (s:set (pos * a)) 
  : (b:bool{(b = true <==> (exists e. mem e s /\ fst e = id)) /\
            ((forall ele. mem (id, ele) s ==> b = true))})*)

(*val same_uni (#a:eqtype) (s1 s2:set (pos & a)) (min1:(pos & a))
  : Lemma (requires unique_st s1 /\ (forall e. mem e s2 <==> mem e s1 /\ e <> min1))
          (ensures unique_st s2)*)
