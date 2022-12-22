module App

open FStar.Seq
open FStar.Ghost
module L = FStar.List.Tot

let rec mem_id_s (id:nat) (l:list (nat * string)) =
  match l with
  |[] -> false
  |(id1,_)::xs -> id = id1 || mem_id_s id xs

let rec pos (ele:(nat * string)) (l:list(nat * string){L.mem ele l}) =
  match l with
  |ele1::xs -> if ele1 = ele then 0 else 1 + pos ele xs
  
let rec total_order (l:list (nat * string)) =
  match l with
  |[] | [_] -> True
  |x::y::xs -> lt (fst y) (fst x) /\ total_order (y::xs)

let ord (id:(nat * string)) (id1:(nat * string)) 
        (l:list (nat * string) {L.mem id l /\ L.mem id1 l /\ total_order l}) = 
  pos id l < pos id1 l 

// the concrete state type
// It is a list of pairs of timestamp and message ordered in descending order of timestamps
type concrete_st = l:list (nat (*timestamp*) * string (*message*)) {total_order l}

//initial state
let init_st = []

// operation type
// (the only operation is append value, so string is fine)
type op_t = string

// concrete do pre-condition
let concrete_do_pre (s:concrete_st) (op:log_entry) = 
  L.length s > 0 ==> lt (fst (L.hd s)) (fst op)
 // (forall e. L.mem e s ==> lt (fst e) (fst op))

// apply an operation to a state
let do (s:concrete_st) (op:log_entry{concrete_do_pre s op}) = op::s

let rec mem_str_s (str:string) (l:list (nat * string)) =
  match l with
  |[] -> false
  |(_,m)::xs -> str = m || mem_str_s str xs
  
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = list string

// init state 
let init_st_s = []

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:log_entry) : concrete_st_s = snd op::s

//equivalence relation between the concrete states of sequential type and MRDT
let eq (st_s:concrete_st_s) (st:concrete_st) =
  (forall e. L.mem e st_s <==> mem_str_s e st)

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq st_s st /\ concrete_do_pre st op)
          (ensures eq (do_s st_s op) (do st op)) 
  = ()

////////////////////////////////////////////////////////////////

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires foldl_prop s l)
          (ensures (length l = 0 ==> (seq_foldl s l = s)) /\
                   (*length l > 0 ==> (forall id id1. mem_id id l /\ mem_id_s id1 s ==> lt id1 id)) /\*)
                    total_order (seq_foldl s l))
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

//conflict resolution
let resolve_conflict (x y:log_entry) : (l:log{forall e. mem e l <==> e = x \/ e = y}) =
  if lt (fst y) (fst x)
    then cons y (cons x empty)
      else cons x (cons y empty)

#push-options "--z3rlimit 50"
let resolve_conflict_prop (x y:log_entry)
  : Lemma (requires fst x <> fst y)
          (ensures (lt (fst y) (fst x) <==> last (resolve_conflict x y) = x) /\
                   (last (resolve_conflict x y) <> x <==> lt (fst x) (fst y)))
  = ()

let rec remove (x:(nat * string)) (s:concrete_st)
  : Pure concrete_st
    (requires L.mem x s)
    (ensures (fun r -> (forall e. L.mem e r <==> L.mem e s /\ e <> x) /\ not (mem_id_s (fst x) r) /\
                    (forall id. mem_id_s id r <==> mem_id_s id s /\ id <> fst x) /\
                    (forall e e1. L.mem e r /\ L.mem e1 r /\ lt (fst e1) (fst e) /\ ord e e1 r <==>
                             L.mem e s /\ L.mem e1 s /\ lt (fst e1) (fst e) /\ ord e e1 s /\ e <> x /\ e1 <> x))) =
  match s with
  |x1::xs -> if x = x1 then xs else x1::(remove x xs)

let rec diff_s (a:concrete_st) (l:concrete_st)
  : Pure concrete_st
    (requires (forall e. L.mem e l ==> L.mem e a))
    (ensures (fun r -> (forall e. L.mem e r <==> L.mem e a /\ not (L.mem e l)) /\
                    (forall id. mem_id_s id r <==> mem_id_s id a /\ not (mem_id_s id l)) /\
                    (forall e e1. L.mem e r /\ L.mem e1 r /\ lt (fst e1) (fst e) /\ ord e e1 r <==>
             L.mem e a /\ L.mem e1 a /\ not (L.mem e l) /\ not (L.mem e1 l) /\ lt (fst e1) (fst e) /\ ord e e1 a)))
    (decreases l) = 
  match l with
  |[] -> a
  |x::xs -> diff_s (remove x a) xs

#push-options "--z3rlimit 100"
let rec union_s (a:concrete_st) (b:concrete_st)
  : Pure concrete_st
    (requires (forall e. L.mem e a ==> not (mem_id_s (fst e) b)) /\ 
              (forall e. L.mem e b ==> not (mem_id_s (fst e) a)))
    (ensures (fun u -> (forall e. L.mem e u <==> L.mem e a \/ L.mem e b)/\
                    (forall e e1. ((L.mem e a /\ L.mem e1 a /\ lt (fst e1) (fst e) /\ ord e e1 a) \/
                              (L.mem e b /\ L.mem e1 b /\ lt (fst e1) (fst e) /\ ord e e1 b) \/
                              (L.mem e a /\ L.mem e1 b /\ lt (fst e1) (fst e)) \/
                              (L.mem e b /\ L.mem e1 a /\ lt (fst e1) (fst e))) <==>
                              (L.mem e u /\ L.mem e1 u /\ lt (fst e1) (fst e) /\ ord e e1 u)) /\
                              (forall id. mem_id_s id u <==> mem_id_s id a \/ mem_id_s id b))) =
  match a, b with
  |[], [] -> []
  |[], _ -> b
  |_, [] -> a
  |h1::t1, h2::t2 -> if lt (fst h2) (fst h1) then h1::(union_s t1 b) else h2::(union_s a t2)
#pop-options

// concrete merge pre-condition
let concrete_merge_pre lca a b = 
  forallb (fun e -> L.mem e a && L.mem e b) lca /\
  forallb (fun e -> not (mem_id_s (fst e) (diff_s b lca))) (diff_s a lca) /\
  forallb (fun e -> not (mem_id_s (fst e) (diff_s a lca))) (diff_s b lca)

// concrete merge operation
let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) 
  : (r:concrete_st{(forall e. L.mem e r <==> L.mem e s1 \/ L.mem e s2) /\
                   (forall e e1. (L.mem e r /\ L.mem e1 r /\ fst e > fst e1 /\ ord e e1 r) <==>
                            (L.mem e lca /\ L.mem e1 lca /\ fst e > fst e1 /\ ord e e1 lca) \/
                       (L.mem e (diff_s s1 lca) /\ L.mem e1 (diff_s s1 lca) /\ lt (fst e1) (fst e) /\ ord e e1 (diff_s s1 lca)) \/
                       (L.mem e (diff_s s2 lca) /\ L.mem e1 (diff_s s2 lca) /\ lt (fst e1) (fst e) /\ ord e e1 (diff_s s2 lca)) \/
                       (L.mem e (diff_s s1 lca) /\ L.mem e1 (diff_s s2 lca) /\ lt (fst e1) (fst e)) \/
                       (L.mem e (diff_s s2 lca) /\ L.mem e1 (diff_s s1 lca) /\ lt (fst e1) (fst e)) \/
                       (L.mem e (diff_s s1 lca) /\ L.mem e1 lca /\ lt (fst e1) (fst e)) \/
                       (L.mem e (diff_s s2 lca) /\ L.mem e1 lca /\ lt (fst e1) (fst e)) \/
                       (L.mem e lca /\ L.mem e1 (diff_s s1 lca) /\ lt (fst e1) (fst e)) \/
                       (L.mem e lca /\ L.mem e1 (diff_s s2 lca) /\ lt (fst e1) (fst e)))}) = 
  let la = diff_s s1 lca in
  let lb = diff_s s2 lca in
  let u = union_s la lb in 
  let r = union_s u lca in 
  r
