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

let add (#a:eqtype) (ele:a) (s:set a) = 
  if mem ele s then s else ele::s

let add_mem (#a:eqtype) (ele:a) (s:set a) (x:a)
  : Lemma (ensures (mem ele s ==> (add ele s = s)) /\
                   (not (mem ele s) ==> (mem x (add ele s) <==> (mem x s \/ x == ele))) /\
                   (s = empty ==> (mem x (add ele s) <==> x = ele))) = ()

let union (#a:eqtype) (s1:set a) (s2:set a) =
  List.Tot.Base.append s1 s2

let union_mem (#a:eqtype) (s1:set a) (s2:set a) (x:a)
  : Lemma (ensures (mem x (union s1 s2) <==> (mem x s1 \/ mem x s2)) /\
                   (not (mem x (union s1 s2)) <==> (not (mem x s1) /\ not (mem x s2)))) =
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

let diff (#a:eqtype) (s1 s2:set a) : set a =
  remove_if s1 (fun e -> mem e s2)

let rec diff_mem (#a:eqtype) (s1 s2:set a) (x:a)
  : Lemma (ensures mem x (diff s1 s2) <==> (mem x s1 /\ ~ (mem x s2)))  =
  match s1 with
  |[] -> ()
  |x1::xs -> diff_mem xs s2 x
  
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

let extract (#a:Type0) (x:option a{Some? x}) : (r:a{x == Some r}) =
  let (Some a) = x in a

let rec find_if (#a:eqtype) (s:set a) (f:a -> bool) : option a =
  match s with
  |[] -> None
  |x::xs -> if f x then Some x else find_if xs f

let rec mem_find_if (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (ensures (None? (find_if s f) <==> ((forall e. mem e s ==> ~ (f e)) \/ s = empty)) /\
                   (Some? (find_if s f) <==> (exists e. mem e s /\ f e)) /\
                   (Some? (find_if s f) ==> (exists e. mem e s /\ f e /\ e = extract (find_if s f)) /\ (f (extract (find_if s f))))) = 
  match s with
  |[] -> ()
  |x::xs -> if f x then () else mem_find_if xs f

let rec mem_find_if_exists (#a:eqtype) (s:set a) (f:a -> bool)
  : Lemma (requires (exists e. mem e s /\ f e))
          (ensures (None? (find_if s f) <==> ((forall e. mem e s ==> ~ (f e)) \/ s = empty)) /\
                   (Some? (find_if s f) <==> (exists e. mem e s /\ f e)) /\
                   (Some? (find_if s f) ==> (exists e. mem e s /\ f e /\ e = extract (find_if s f)) /\ (f (extract (find_if s f)))) /\
                   (s <> empty ==> Some? (find_if s f))) = 
  match s with
  |[] -> ()
  |x::xs -> if f x then () else mem_find_if_exists xs f
 
let rec always_min_exists (#a:eqtype) (s:set (pos * a)) 
  : Lemma (ensures (s <> empty ==> (exists (e:(pos * a)). mem e s /\ (forall (e1:(pos * a)). mem e1 s ==> fst e <= fst e1)))) =
  match s with
  |[] -> ()
  |x::xs -> always_min_exists xs

let find_min (#a:eqtype) (s:set (pos * a))
  : (m:option (pos * a)
           {(Some? m <==> (exists (e:(pos * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1))) /\
            (Some? m <==> (exists (e:(pos * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1) /\ e = extract m)) /\
            (s = empty <==> m = None) /\
            (Some? m ==> mem (extract m) s)}) =
  always_min_exists s;
  find_if s (fun e -> (forall_s s (fun e1 -> fst e <= fst e1)))

let mem_find_min (#a:eqtype) (s:set (pos * a))
  : Lemma (ensures (Some? (find_min s) <==> (exists (e:(pos * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1))) /\
            (Some? (find_min s) <==> (exists (e:(pos * a)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1) /\ e = extract (find_min s))) /\
            (s = empty <==> find_min s = None) /\
            (Some? (find_min s) ==> mem (extract (find_min s)) s)) = 
  always_min_exists s

let remove_min (#a:eqtype) (s:set (pos * a)) 
  : (r:set (pos * a){(s = empty <==> r = s) /\
                   (s <> empty /\ Some? (find_min s) ==> (forall e. mem e r <==> (mem e s /\ e <> extract (find_min s)))) (*/\
                   (s <> empty /\ None? (find_min s) ==> (forall e. mem e r <==> mem e s)*)}) =
  always_min_exists s;
  if s = empty then s 
  else (let m = find_min s in
        remove_if s (fun e -> e = extract (find_min s)))

let mem_remove_min (#a:eqtype) (s:set (pos * a)) 
  : Lemma (ensures (let r = remove_min s in
                   (s = empty <==> r = s) /\
                   (s <> empty /\ Some? (find_min s) ==> (forall e. mem e r <==> (mem e s /\ e <> extract (find_min s)))) /\
                   (s <> empty /\ None? (find_min s) ==> (forall e. mem e r <==> mem e s)) /\
                   ((exists ele. (forall e. mem e s <==> e = ele)) ==> r = empty))) = 
  always_min_exists s

let mem_id_s (#a:eqtype) (id:pos) (s:set (pos * a)) 
  : (b:bool{(b = true <==> (exists e. mem e s /\ fst e = id)) /\
            ((forall ele. mem (id, ele) s ==> b = true))}) =
  exists_s s (fun e -> fst e = id)

let same_uni (#a:eqtype) (s1 s2:set (pos & a)) (min1:(pos & a))
  : Lemma (requires unique_st s1 /\ (forall e. mem e s2 <==> mem e s1 /\ e <> min1))
          (ensures unique_st s2) = ()
  
let rec always_min_exists_nat (s:set nat) 
  : Lemma (ensures (s <> empty ==> (exists (e:nat). mem e s /\ (forall (e1:nat). mem e1 s ==> e <= e1)))) =
  match s with
  |[] -> ()
  |x::xs -> always_min_exists_nat xs
  
let find_min_nat (s:set nat)
  : (m:option nat
           {(Some? m <==> (exists (e:nat). mem e s /\ (forall e1. mem e1 s ==> e <= e1))) /\
            (Some? m <==> (exists (e:nat). mem e s /\ (forall e1. mem e1 s ==> e <= e1) /\ e = extract m)) /\
            (s = empty <==> m = None) /\
            (Some? m ==> mem (extract m) s)}) =
  always_min_exists_nat s;
  find_if s (fun e -> (forall_s s (fun e1 -> e <= e1)))
  
let mem_find_min_nat (s:set nat)
  : Lemma (ensures (Some? (find_min_nat s) <==> (exists (e:nat). mem e s /\ (forall e1. mem e1 s ==> e <= e1))) /\
            (Some? (find_min_nat s) <==> (exists (e:nat). mem e s /\ (forall e1. mem e1 s ==> e <= e1) /\ e = extract (find_min_nat s))) /\
            (s = empty <==> find_min_nat s = None) /\
            (Some? (find_min_nat s) ==> mem (extract (find_min_nat s)) s)) = 
  always_min_exists_nat s
        
let remove_min_nat (s:set nat)
  : (r:set nat{(s = empty <==> r = s) /\
                   (s <> empty /\ Some? (find_min_nat s) ==> (forall e. mem e r <==> (mem e s /\ e <> extract (find_min_nat s)))) (*/\
                   (s <> empty /\ None? (find_min s) ==> (forall e. mem e r <==> mem e s)*)}) =
  always_min_exists_nat s;
  if s = empty then s 
  else (let m = find_min_nat s in
        remove_if s (fun e -> e = extract (find_min_nat s)))

let mem_remove_min_nat (s:set nat)
  : Lemma (ensures (let r = remove_min_nat s in
                   (s = empty <==> r = s) /\
                   (s <> empty /\ Some? (find_min_nat s) ==> (forall e. mem e r <==> (mem e s /\ e <> extract (find_min_nat s)))) /\
                   (s <> empty /\ None? (find_min_nat s) ==> (forall e. mem e r <==> mem e s)))) = 
  always_min_exists_nat s
  
