module Set_extended

open FStar.List.Tot
  
let set (a:eqtype) = list a

let mem (#a:eqtype) (x:a) (s:set a) = mem x s

let empty (#a:eqtype) = []

let empty_mem (#a:eqtype) (x:a)
  : Lemma (ensures not (mem x empty)) = ()

let equal (#a:eqtype) (s1:set a) (s2:set a) = 
  (forall e. mem e s1 <==> mem e s2)

let equal_mem (#a:eqtype) (s1:set a) (s2:set a)
  : Lemma (ensures (equal s1 s2 <==> (forall e. mem e s1 <==> mem e s2))) = ()

let singleton (#a:eqtype) (x:a) = [x]

let singleton_mem (#a:eqtype) (x:a) (y:a) 
  : Lemma (ensures (mem y (singleton x) = (x=y))) = ()

let add (#a:eqtype) (ele:a) (s:set a) = ele::s

let add_mem (#a:eqtype) (ele:a) (s:set a) (x:a) = ()

let union (#a:eqtype) (s1:set a) (s2:set a) =
  List.Tot.Base.append s1 s2

let union_mem (#a:eqtype) (s1:set a) (s2:set a) (x:a)
  : Lemma (ensures mem x (union s1 s2) <==> (mem x s1 \/ mem x s2)) =
  append_mem_forall s1 s2

let rec remove (#a:eqtype) (ele:a) (s1:set a) : (r:set a{forall e. mem e r <==> mem e s1 /\ e <> ele}) =
  match s1 with
  |[] -> []
  |x::xs -> if x = ele then remove ele xs else x::remove ele xs

let rec intersect (#a:eqtype) (s1:set a) (s2:set a) =
  match s1 with
  |[] -> []
  |x::xs -> if mem x s2 then x::intersect xs (remove x s2) else intersect xs s2
  
let rec intersect_mem (#a:eqtype) (s1:set a) (s2:set a) (x:a)
  : Lemma (ensures mem x (intersect s1 s2) <==> (mem x s1 /\ mem x s2)) 
    (decreases s1) =
  match s1 with
  |[] -> ()
  |x1::xs -> if mem x1 s2 then intersect_mem xs (remove x1 s2) x else intersect_mem xs s2 x

let rec remove_if (#a:eqtype) (s:set a) (f:a -> bool) =
  match s with
  |[] -> []
  |x::xs -> if f x then remove_if xs f else x::remove_if xs f

let rec remove_if_mem (#a:eqtype) (s:set a) (f:a -> bool) (x:a)
  : Lemma (ensures mem x (remove_if s f) <==> (mem x s /\ ~ (f x))) = 
  match s with
  |[] -> ()
  |x1::xs -> remove_if_mem xs f x

let rec filter_s (#a:eqtype) (s:set a) (f:a -> bool) =
  match s with
  |[] -> []
  |x::xs -> if f x then x::filter_s xs f else filter_s xs f
  
let rec filter_mem (#a:eqtype) (s:set a) (f:a -> bool) (x:a)
  : Lemma (ensures (mem x (filter_s s f) <==> (mem x s /\ f x))) =
  match s with
  |[] -> ()
  |x1::xs -> filter_mem xs f x

let rec exists_s (#a:eqtype) (s:set a) (f:a -> bool) =
  match s with
  |[] -> false
  |x::xs -> f x || exists_s xs f

let rec exists_mem (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures ((exists_s s f = true) <==> (exists x. mem x s /\ f x))) = 
  match s with
  |[] -> ()
  |x::xs -> exists_mem xs f

let rec forall_s (#a:eqtype) (s:set a) (f:a -> bool) =
  match s with
  |[] -> true
  |x::xs -> f x && forall_s xs f

let rec forall_mem (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures ((forall_s s f = true) <==> (forall x. mem x s ==> f x))) =
  match s with
  |[] -> ()
  |x::xs -> forall_mem xs f

let rec count (#a:eqtype) (ele:a) (s:set a) : (n:nat{(n = 0 <==> not (mem ele s)) /\
                                                   (n > 0 <==> mem ele s)}) = 
  match s with
  |[] -> 0
  |x::xs -> if x = ele then 1 + count ele xs else count ele xs

let mem_count (#a:eqtype) (ele:a) (s:set a)
  : Lemma (ensures ((mem ele s = true) <==> count ele s > 0)) = ()

let rec count_if (#a:eqtype) (s:set a) (f:a -> bool) : nat =
  match s with
  |[] -> 0
  |x::xs -> if f x then 1 + count_if xs f else count_if xs f

let rec mem_count_if (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures ((count_if s f > 0) <==> (filter_s s (fun e -> f e) <> empty))) =
  match s with
  |[] -> ()
  |x::xs -> mem_count_if xs f

let extr (#a:eqtype) (x:option a{Some? x}) : (r:a{x = Some r}) =
  let (Some a) = x in a

let rec find_if (#a:eqtype) (s:set a) (f:a -> bool) : option a =
  match s with
  |[] -> None
  |x::xs -> if f x then Some x else find_if xs f

let rec mem_find_if (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures (None? (find_if s f) <==> ((forall e. mem e s ==> ~ (f e)) \/ s = empty)) /\
                   (Some? (find_if s f) <==> (exists e. mem e s /\ f e)) /\
                   (Some? (find_if s f) ==> (exists e. mem e s /\ f e /\ e = extr (find_if s f)) /\ (f (extr (find_if s f))))) = 
  match s with
  |[] -> ()
  |x::xs -> if f x then () else mem_find_if xs f

let rec mem_find_if_exists (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (requires (exists e. mem e s /\ f e))
          (ensures (None? (find_if s f) <==> ((forall e. mem e s ==> ~ (f e)) \/ s = empty)) /\
                   (Some? (find_if s f) <==> (exists e. mem e s /\ f e)) /\
                   (Some? (find_if s f) ==> (exists e. mem e s /\ f e /\ e = extr (find_if s f)) /\ (f (extr (find_if s f)))) /\
                   (s <> empty ==> Some? (find_if s f))) = 
  match s with
  |[] -> ()
  |x::xs -> if f x then () else mem_find_if_exists xs f
