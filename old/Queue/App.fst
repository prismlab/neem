module App

open FStar.Seq
open FStar.Ghost
module L = FStar.List.Tot

(*let rec mem_id_s (id:nat) (l:list (nat * nat))
    : Tot (b:bool {b = true <==> (exists m. L.mem (id,m) l) /\ (exists e. L.mem e l ==> fst e = id)}) =
  match l with
  |[] -> false
  |(id1,m)::xs -> id = id1 || mem_id_s id xs*)

(*let rec unique_s (l:list nat) =
  match l with
  |[] -> true
  |id::xs -> not (L.mem id xs) && unique_s xs*)

let rec unique_s (l:list nat) =
  match l with
  |[] -> true
  |e::xs -> not (L.mem e xs) && unique_s xs
  
let rec total_order (l:list nat {unique_s l}) : prop =
  match l with
  |[] -> true
  |[_] -> true
  |x::xs -> (forall e. L.mem e xs ==> lt x e) /\ total_order xs

let rec pos (id:nat) (l:list (nat) {L.mem id l /\ unique_s l}) : Tot nat =
  match l with
  |id1::xs -> if id = id1 then 0 else 1 + pos id xs

let ord (id:(nat)) (id1:(nat) { id <>  id1})
        (l:list (nat) {L.mem id l /\ L.mem id1 l /\ unique_s l /\ total_order l})
        : Tot (b:bool {b = true <==> pos id l < pos id1 l})
    = lt (pos id l) (pos id1 l)
    
// the concrete state type
// It is a list of pairs of timestamp and message ordered in descending order of timestamps
type concrete_st = l:list (nat (*timestamp*) (* nat (*message*) *)) {unique_s l /\ total_order l}

//initial state
let init_st = []

// operation type
type op_t:eqtype = 
  |Enqueue
  |Dequeue : option nat -> op_t

(*val get_ele (op:log_entry{Enqueue? (snd op)}) : nat
let get_ele (_, Enqueue ele) = ele*)

val return (op:log_entry{Dequeue? (snd op)}) : option nat
let return (_, Dequeue r) = r
  
// concrete do pre-condition
let concrete_do_pre (s:concrete_st) (op:log_entry) : prop = 
  (forall id. L.mem id s ==> lt id (fst op)) /\
  ((Dequeue? (snd op) /\ L.length s <> 0) ==> return op = Some (L.hd s)) /\
  ((Dequeue? (snd op) /\ return op <> None) ==> s <> []) /\
  ((Dequeue? (snd op) /\ L.length s = 0) ==> return op = None) /\
  ((Dequeue? (snd op) /\ return op = None) ==> s = [])

let rear (s:concrete_st) : option nat =
  match s with
  |[] -> None
  |_ -> Some (L.last s)

let front (s:concrete_st) : option nat =
  match s with
  |[] -> None
  |_ -> Some (L.hd s)
  
#push-options "--z3rlimit 50"
let rec enqueue (s:concrete_st) (op:log_entry{Enqueue? (snd op) /\ concrete_do_pre s op}) 
  : Tot (r:concrete_st{(forall e. L.mem e r <==> L.mem e s \/ e = fst op) /\
                       (rear r = Some (fst op)) /\ L.length r = L.length s + 1 /\ L.length r > 0 /\
                       (r = s@[fst op]) /\
                       r <> []}) (decreases s) =
  match s with
  |[] -> fst op::[]
  |x::xs -> x::enqueue xs op

let dequeue (s:concrete_st) (op:log_entry{Dequeue? (snd op) /\ concrete_do_pre s op}) 
  : Tot (r:concrete_st{forall e. L.mem e r <==> L.mem e s /\ e <> (L.hd s)}) =
 if s = [] then [] else (L.tl s)
  
// apply an operation to a state
let do (s:concrete_st) (op:log_entry{concrete_do_pre s op}) 
  : (r:concrete_st{(Enqueue? (snd op) ==> (rear r = Some (fst op)) /\
                                         (forall e. L.mem e r <==> L.mem e s \/ e = fst op) /\
                                         (r = s@[fst op]) /\
                                         (L.length r = L.length s + 1) /\ L.length r > 0) /\
                   ((Dequeue? (snd op) /\ Cons? s) ==> (forall e. L.mem e r <==> L.mem e s /\ e <> L.hd s) /\
                                                     (forall e. L.mem e r \/ e = L.hd s <==> L.mem e s) /\
                                                     (r = L.tl s) /\
                                                     (L.length r = L.length s - 1)) /\
                   ((Dequeue? (snd op) /\ ~ (Cons? s)) <==> (r = s /\ L.length r = L.length s))})
  = if Enqueue? (snd op) then
       enqueue s op else
         dequeue s op

let lem_do (s:concrete_st) (op:log_entry{concrete_do_pre s op})
  : Lemma (ensures (Enqueue? (snd op) <==> (forall e. L.mem e (do s op) <==> L.mem e s \/ e = fst op)) /\
                   ((Dequeue? (snd op) /\ s <> []) ==> (forall e. L.mem e (do s op) <==> L.mem e s /\ e <> L.hd s)) /\
                   ((Dequeue? (snd op) /\ s = []) <==> do s op = s) /\
                   ((Dequeue? (snd op) /\ return op <> None) ==> s <> [])) = ()

let lem_cons (#a:eqtype) (s:list a) (op:a)
  : Lemma (ensures (forall e. L.mem e (op::s) <==> L.mem e s \/ e = op) /\
                   (L.length (op::s) = L.length s + 1)) = ()

(*let rec pos_op (e:log_entry) (l:log{mem e l}) : Tot nat (decreases length l) =
  if head l = e then 0 else 1 + pos_op e (tail l)

let order (e d:log_entry) (l:log{mem e l /\ mem d l}) =
  lt (pos_op e l) (pos_op d l)
  
let matching (e d:log_entry) (l:log) =
  mem e l && mem d l && Enqueue? (snd e) && Dequeue? (snd e) && return d = Some (fst e) && order e d l

val filter : #a:eqtype
           -> f:(a -> bool)
           -> l:seq a
           -> Tot (l1:seq a {forall e. mem e l1 <==> mem e l /\ f e}) (decreases length l)
let rec filter #a f l = 
  match length l with
  |0 -> empty
  |_ -> if f (head l) then cons (head l) (filter f (tail l)) else filter f (tail l)

val exists_op : f:(log_entry -> bool)
              -> l:log
              -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true}) (decreases length l)
let rec exists_op f l =
  match length l with
  | 0 -> false
  | _ -> if f (head l) then true else exists_op f (tail l)

let count_match (l:log) : nat =
  length (filter (fun e -> (mem e l && Enqueue? (snd e) && (exists_op (fun d -> matching e d l) l))) l)

let count_unmatch (l:log) : nat =
  length (filter (fun e -> (mem e l && Enqueue? (snd e) && not (exists_op (fun d -> matching e d l) l))) l)

let count_en (l:log) : nat =
  length (filter (fun e -> (mem e l && Enqueue? (snd e))) l)

let unmatched_en (l:log) : log =
  (filter (fun e -> (mem e l && Enqueue? (snd e) && not (exists_op (fun d -> matching e d l) l))) l)*)

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = list nat

// init state 
let init_st_s = []

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:log_entry) : concrete_st_s = admit()

//equivalence relation between the concrete states of sequential type and MRDT
let eq (st_s:concrete_st_s) (st:concrete_st) =
  st_s == st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq st_s st /\ concrete_do_pre st op)
          (ensures eq (do_s st_s op) (do st op)) 
  = admit()

////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 100"
let rec lem_foldl (x:concrete_st) (l:log)
  : Lemma (requires foldl_prop x l)
          (ensures (length l > 0 ==> (let p, last = un_snoc l in
                   foldl_prop x p /\
                   concrete_do_pre (seq_foldl x p) last /\
                   (seq_foldl x l == do (seq_foldl x p) last))) /\
                   (forall e. L.mem e (seq_foldl x l) ==> L.mem e x \/ mem_id e l))
          (decreases length l) =
  match length l with
  |0 -> ()
  |1 -> ()
  |_ -> lem_foldl (do x (head l)) (tail l)
  
(*let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires foldl_prop s l)
          (ensures (length l = 0 ==> (seq_foldl s l = s)) /\
                   (forall id. L.mem id (seq_foldl s l) <==> L.mem id s \/ mem_id id (unmatched_en l)) /\
                   (length l > 0 ==> (let p, last = un_snoc l in
                             (foldl_prop s p /\
                              concrete_do_pre (seq_foldl s p) last /\
                              (seq_foldl s l == do (seq_foldl s p) last) /\
    (Enqueue? (snd last) ==> (forall id. L.mem id (seq_foldl s l) <==> L.mem id s \/ mem_id id (unmatched_en p) \/ id = fst last)) /\
 (Dequeue? (snd last) /\ s <> [] ==> (forall id. L.mem id (seq_foldl s l) <==> L.mem id s \/ mem_id id (unmatched_en p) /\ id <> L.hd s)) /\
 (Dequeue? (snd last) /\ s = [] ==> (forall id. L.mem id (seq_foldl s l) <==> mem_id id (unmatched_en p) /\ id <> fst (head (unmatched_en p))))))))
          (decreases length l)
  = admit(); match length l with
    |0 -> ()
    |1 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)*)
#pop-options

//conflict resolution
let resolve_conflict (x y:log_entry) : (l:log{(forall e. mem e l ==> e = x \/ e = y)}) =
  match snd x, snd y with
  |Dequeue _, Enqueue -> cons x (cons y empty)
  |Enqueue, Dequeue _ -> cons y (cons x empty)
  |Enqueue, Enqueue -> if lt (fst x) (fst y) then cons x (cons y empty) else cons y (cons x empty)
  |Dequeue e, Dequeue e1 -> if e = e1 then cons x empty else cons x (cons y empty)

#push-options "--z3rlimit 50"
let resolve_conflict_prop (x y:log_entry)
  : Lemma (requires fst x <> fst y)
          (ensures ((length (resolve_conflict x y) = 2 /\ last (resolve_conflict x y) = x) <==>
                    (Enqueue? (snd x) /\ Dequeue? (snd y)) \/ 
                    (Enqueue? (snd x) /\ Enqueue? (snd y) /\ lt (fst y) (fst x))) /\
                    
                   ((length (resolve_conflict x y) = 2 /\ last (resolve_conflict x y) <> x) <==>
                     last (resolve_conflict x y) = y /\
                    ((Dequeue? (snd x) /\ Enqueue? (snd y)) \/
                     (Enqueue? (snd x) /\ Enqueue? (snd y) /\ lt (fst x) (fst y)) \/
                     (Dequeue? (snd x) /\ Dequeue? (snd y) /\ return x <> return y))) /\
                     
                   ((length (resolve_conflict x y) = 1 /\ last (resolve_conflict x y) = x) <==>
                     Dequeue? (snd x) /\ Dequeue? (snd y) /\ return x = return y))
  = ()

val filter : f:(nat -> bool)
           -> l:concrete_st
           -> Tot (l1:concrete_st {forall e. L.mem e l1 <==> L.mem e l /\ f e})
let rec filter f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter f tl) else filter f tl

let diff_s (a:concrete_st) (l:concrete_st {(forall e e1. L.mem e l /\ (L.mem e1 a /\ not (L.mem e1 l)) ==> lt e e1)})
  : Tot (r:concrete_st {(forall e. L.mem e r <==> L.mem e a /\ not (L.mem e l)) /\
                        (forall e e1. L.mem e l /\ L.mem e1 r ==> lt e e1) /\
                        (r = [] <==> ((forall e. L.mem e a ==> L.mem e l) \/ a = l))})
             (decreases %[l;a]) =
  filter (fun e -> not (L.mem e l)) a

// concrete merge pre-condition
let concrete_merge_pre l a b = 
  (forall e e1. L.mem e l /\ (L.mem e1 a /\ not (L.mem e1 l)) ==> lt e e1) /\
  (forall e e1. L.mem e l /\ (L.mem e1 b /\ not (L.mem e1 l)) ==> lt e e1) /\
  (*diff_s a l = [] ==> 
          (forall e e1. (L.mem e l /\ not (L.mem e a)) /\ (L.mem e1 a) ==> lt e e1)) /\
  (diff_s b l = [] ==> 
          (forall e e1. (L.mem e l /\ not (L.mem e b)) /\ (L.mem e1 b) ==> lt e e1)) /\*)
  //(forall e e1. L.mem e l /\ L.mem e1 (diff_s a l) ==> lt e e1) /\
  //(forall e e1. L.mem e l /\ L.mem e1 (diff_s b l) ==> lt e e1) /\
  (forall e. L.mem e (diff_s a l) ==> not (L.mem e (diff_s b l)))
  
let intersection (l:concrete_st) (a:concrete_st) (b:concrete_st{concrete_merge_pre l a b})
  : Tot (r:concrete_st {(forall e. L.mem e r <==> L.mem e l /\ L.mem e a /\ L.mem e b)}) =
  filter (fun e -> L.mem e a && L.mem e b) l

let rec union (a b:concrete_st)
  : Pure concrete_st
    (requires (forall e. L.mem e a ==> not (L.mem e b)))
    (ensures (fun r -> (forall e. L.mem e r <==> L.mem e a \/ L.mem e b))) =
  match a, b with
  |[],[] -> []
  |[],_ -> b
  |_,[] -> a
  |x::xs, y::ys -> if lt x y then x::(union xs b) else y::(union a ys)

// concrete merge operation
let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) 
  : (r:concrete_st {(forall e. L.mem e r <==> ((L.mem e lca /\ L.mem e s1 /\ L.mem e s2) \/ 
                                        (L.mem e (diff_s s1 lca)) \/ (L.mem e (diff_s s2 lca)))) /\
                    (diff_s s1 lca <> [] \/ diff_s s2 lca <> [] ==> r <> [])}) = 
  let i = intersection lca s1 s2 in
  let da = diff_s s1 lca in
  let db = diff_s s2 lca in
  union i (union da db)

#push-options "--z3rlimit 100"
let merge_inv_prop_inv1_len2_1 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    ((length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) = last1 /\
                      (Enqueue? (snd last1) /\ Dequeue? (snd last2))))))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) = 
  lem_foldl init_st (ops_of s1)

let merge_inv_prop_inv1_len2_2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    ((length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) = last1 /\
                      (Enqueue? (snd last1) /\ Enqueue? (snd last2) /\ lt (fst last2) (fst last1))))))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) = 
  lem_foldl init_st (ops_of s1)

let merge_inv_prop_inv1_len2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    ((length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) = last1))))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) = 
  let _,last1 = un_snoc (ops_of s1) in
  let _,last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  if (Enqueue? (snd last1) && Dequeue? (snd last2)) then 
    merge_inv_prop_inv1_len2_1 lca s1 s2 else
      merge_inv_prop_inv1_len2_2 lca s1 s2

let merge_inv_prop_inv2_len2_1 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) = last2 /\
                      (Dequeue? (snd last1) /\ Enqueue? (snd last2)))))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = 
  lem_foldl init_st (ops_of s2)

let merge_inv_prop_inv2_len2_2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) = last2 /\
                      (Enqueue? (snd last1) /\ Enqueue? (snd last2) /\ lt (fst last1) (fst last2)))))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = 
  lem_foldl init_st (ops_of s2)

let merge_inv_prop_inv2_len2_31 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) = last2 /\
                      (Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 <> return last2 /\ return last2 =  None))))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = 
  lem_foldl init_st (ops_of s2)
  
let merge_inv_prop_inv2_len2_32 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) = last2 /\
                      (Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 <> return last2 /\ return last2 <>  None))))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = 
  assert (forall e e1. L.mem e (v_of lca) /\ (L.mem e1 (v_of s1) /\ not (L.mem e1 (v_of lca))) ==> lt e e1); 
  lem_foldl init_st (ops_of s2); 
  assert (length (ops_of s2) > 0); 
  assume (forall e e1. L.mem e (v_of lca) /\ (L.mem e1 (v_of (inverse_st s2)) /\ not (L.mem e1 (v_of lca))) ==> lt e e1);
  assume (forall e. L.mem e (diff_s (v_of s1) (v_of lca)) ==> not (L.mem e (diff_s (v_of (inverse_st s2)) (v_of lca))));
  ()

let merge_inv_prop_inv2_len2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    ((length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) <> last1))))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = 
  let _,last1 = un_snoc (ops_of s1) in
  let _,last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  if (Dequeue? (snd last1) && Enqueue? (snd last2)) then 
    merge_inv_prop_inv2_len2_1 lca s1 s2 else
    if (Enqueue? (snd last1) && Enqueue? (snd last2) && lt (fst last1) (fst last2)) then
      merge_inv_prop_inv2_len2_2 lca s1 s2 else 
      if (Dequeue? (snd last1) && Dequeue? (snd last2) && return last1 <> return last2 && return last2 =  None) then
        merge_inv_prop_inv2_len2_31 lca s1 s2 else
          merge_inv_prop_inv2_len2_32 lca s1 s2

let merge_inv_prop_inv1_len1_1 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    ((length (resolve_conflict last1 last2) = 1 /\
                      last (resolve_conflict last1 last2) = last1 /\
                      Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 = return last2 /\ return last1 = None))))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) =
  lem_foldl init_st (ops_of s2); 
  lem_foldl init_st (ops_of s1)

let merge_inv_prop_inv1_len1_2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    ((length (resolve_conflict last1 last2) = 1 /\
                      last (resolve_conflict last1 last2) = last1 /\
                      Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 = return last2 /\ return last1 <> None))))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) =
  lem_foldl init_st (ops_of s2); 
  lem_foldl init_st (ops_of s1);
  admit()

let merge_inv_prop_inv1_len1 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    ((length (resolve_conflict last1 last2) = 1 /\
                      last (resolve_conflict last1 last2) = last1))))
         (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) =             
  let _,last1 = un_snoc (ops_of s1) in
  let _,last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  if (Dequeue? (snd last1) && Dequeue? (snd last2) && return last1 = return last2 && return last1 = None) then
    merge_inv_prop_inv1_len1_1 lca s1 s2 else
      merge_inv_prop_inv1_len1_2 lca s1 s2
                      
#push-options "--z3rlimit 100"
let merge_inv_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    ((length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) = last1) ==>
                      concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                      
                    ((length (resolve_conflict last1 last2) = 2 /\
                      last (resolve_conflict last1 last2) <> last1) ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) /\
                      
                    ((length (resolve_conflict last1 last2) = 1 /\
                      last (resolve_conflict last1 last2) = last1) ==>
                      concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) /\
                      
                    ((length (resolve_conflict last1 last2) = 1 /\
                      last (resolve_conflict last1 last2) <> last1) ==>
                      concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))))) = 
  let _,last1 = un_snoc (ops_of s1) in
  let _,last2 = un_snoc (ops_of s2) in
  if (length (resolve_conflict last1 last2) = 2 &&
      last (resolve_conflict last1 last2) = last1) then
     merge_inv_prop_inv1_len2 lca s1 s2
  else if (length (resolve_conflict last1 last2) = 2 &&
      last (resolve_conflict last1 last2) <> last1) then
     merge_inv_prop_inv2_len2 lca s1 s2 
  else if (length (resolve_conflict last1 last2) = 1 &&
      last (resolve_conflict last1 last2) = last1) then
     merge_inv_prop_inv1_len1 lca s1 s2
  else ()

let rec remove_ele (ele:nat) (a:concrete_st)
  : Pure concrete_st
    (requires (L.mem ele a))
    (ensures (fun r -> (forall e. L.mem e r <==> L.mem e a /\ e <> ele))) =
  match a with
  |ele1::xs -> if ele = ele1 then xs else ele1::(remove_ele ele xs)

let rec lem_length (a b:concrete_st) 
  : Lemma (requires (forall e. L.mem e a <==> L.mem e b))
          (ensures (List.Tot.length a = List.Tot.length b)) (decreases %[a;b]) =
  match a,b with
  |[],[] -> ()
  |x::xs,_ -> lem_length xs (remove_ele x b)
  |[],_ -> ()
  
let rec lem_equal (a b:concrete_st)
  : Lemma (requires (forall e. L.mem e a <==> L.mem e b) /\
                    (List.Tot.length a = List.Tot.length b))
          (ensures a = b) =
  match a,b with
  |[],[] -> ()
  |x::xs, y::ys -> lem_equal xs ys

let lem_same_op (l1:log) (l2:log{l1 = l2})
  : Lemma (ensures (forall s. foldl_prop s l1 /\ foldl_prop s l2 ==> seq_foldl s l1 = seq_foldl s l2)) = ()

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
          (ensures v_of s2 == concrete_merge (v_of lca) (v_of s1) (v_of s2)) = 
  lem_length (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  lem_equal (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))

let linearizable_s2_0 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                ops_of s2 = ops_of lca /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
       (ensures v_of s1 == concrete_merge (v_of lca) (v_of s1) (v_of s2)) = 
  lem_length (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  lem_equal (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))

#pop-options

let rec lem_lt (a:nat) (b:list nat) (n:nat)
  : Lemma (requires (forall e. L.mem e b ==> a < e) /\ b <> [] /\
                    (forall e. L.mem e b ==> e < n))
          (ensures (a < n)) (decreases b) = 
 ()

#push-options "--z3rlimit 50"
let rec lem_lt1 (a b:concrete_st) (n:nat)
  : Lemma (requires (forall e. L.mem e b ==> lt e n) /\
                    (forall e. L.mem e a ==> not (L.mem e b)) /\ b <> [] /\
                    (forall e e1. L.mem e a /\ L.mem e1 b ==> lt e e1))
          (ensures (forall e. L.mem e a ==> lt e n)) = 
  match a,b with
  |[],[] -> ()
  |x::xs,[] -> ()
  |[],x::xs -> ()
  |x::xs,y::ys -> lem_lt1 xs b n

let rec list_lt (e:nat) (b:concrete_st{not (L.mem e b)}) : Tot prop (decreases b) =
  match b with
  |[] -> True
  |x::xs -> (lt e x) /\ list_lt e xs

let linearizable_gt0_inv1_len2_do_pre (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2))) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) = admit();
  let _,last1 = un_snoc (ops_of s1) in
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  assume (forall id. L.mem id (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) ==> lt id (fst last1));() //todo

let lem_merge (l:concrete_st) (a:concrete_st) (b:concrete_st{concrete_merge_pre l a b})
  : Lemma (ensures (forall e. L.mem e (concrete_merge l a b) <==> 
                      ((L.mem e l /\ L.mem e a /\ L.mem e b) \/ 
                       (L.mem e (diff_s a l)) \/ (L.mem e (diff_s b l))))) = ()

let lem_merge_invab (l:concrete_st) (a:concrete_st) (b:concrete_st{concrete_merge_pre l a b})
                    (ia:concrete_st) (ib:concrete_st{concrete_merge_pre l ia ib}) (n:nat)
  : Lemma (requires (forall e. L.mem e a <==> (L.mem e ia /\ e <> n)) /\
                    (forall e. L.mem e b <==> (L.mem e ib /\ e <> n)) /\
                    (forall e. L.mem e (diff_s a l) <==> (L.mem e (diff_s ia l) /\ e <> n)) /\
                    (forall e. L.mem e (diff_s b l) <==> (L.mem e (diff_s ib l) /\ e <> n)) /\
                    (forall e. (L.mem e l /\ L.mem e a /\ L.mem e b) <==>
                          (L.mem e l /\ L.mem e ia /\ L.mem e ib /\ e <> n)))
    (ensures (*forall e. (L.mem e (concrete_merge l ia ib) /\ e <> n) <==> 
                      ((L.mem e l /\ L.mem e ia /\ L.mem e ib /\ e <> n) \/ 
                       (L.mem e (diff_s ia l) /\ e <> n) \/ (L.mem e (diff_s ib l) /\ e <> n))) /\*)
             (forall e. L.mem e (concrete_merge l a b) <==>
                   (L.mem e (concrete_merge l ia ib) /\ e <> n))) = ()

let lem_merge_inva (l a b ia:concrete_st) (n:nat)
  : Lemma (requires (forall e. L.mem e a <==> L.mem e ia \/ e = n) /\
                    concrete_merge_pre l a b /\ concrete_merge_pre l ia b /\
                    (forall e. L.mem e (diff_s a l) <==> (L.mem e (diff_s ia l) \/ e = n)))
          (ensures (forall e. (L.mem e l /\ L.mem e a /\ L.mem e b) <==> (L.mem e l /\ L.mem e ia /\ L.mem e b)) /\
                   (forall e. L.mem e (concrete_merge l a b) <==> L.mem e (concrete_merge l ia b) \/ e = n)) = ()

let lem_merge_invb (l a b ib:concrete_st) (n:nat)
  : Lemma (requires (forall e. L.mem e b <==> L.mem e ib \/ e = n) /\
                    concrete_merge_pre l a b /\ concrete_merge_pre l a ib /\
                    (forall e. L.mem e (diff_s b l) <==> (L.mem e (diff_s ib l) \/ e = n)))
          (ensures (forall e. (L.mem e l /\ L.mem e a /\ L.mem e b) <==> (L.mem e l /\ L.mem e a /\ L.mem e ib)) /\
                   (forall e. L.mem e (concrete_merge l a b) <==> L.mem e (concrete_merge l a ib) \/ e = n)) = ()
                   
let lem_diff_inv (l a ia:concrete_st) (n:nat)
  : Lemma (requires (forall e. L.mem e a <==> (L.mem e ia \/ e = n)) /\
                    (not (L.mem n l)) /\
                    (forall e e1. L.mem e l /\ (L.mem e1 a /\ not (L.mem e1 l)) ==> lt e e1) /\
                    (forall e e1. L.mem e l /\ (L.mem e1 ia /\ not (L.mem e1 l)) ==> lt e e1))
          (ensures (forall e. L.mem e (diff_s a l) <==> (L.mem e (diff_s ia l) \/ e = n))) = ()

#push-options "--z3rlimit 200"
let linearizable_gt0_inv1_len2_11 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                       (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                       Enqueue? (snd last1) /\ Dequeue? (snd last2) /\
                       concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                          L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)))) =
  let p1, last1 = un_snoc (ops_of s1) in
  lem_foldl init_st (ops_of s1);
  lem_do (v_of (inverse_st s1)) last1; 
  assert (forall e. L.mem e (v_of s1) <==> (L.mem e (v_of (inverse_st s1)) \/ e = fst last1));
  assume (not (L.mem (fst last1) (v_of lca))); //todo
  //lem_diff_inv (v_of lca) (v_of s1) (v_of (inverse_st s1)) (fst last1);
  //assert (forall e. L.mem e (diff_s (v_of s1) (v_of lca)) <==> (L.mem e (diff_s (v_of (inverse_st s1)) (v_of lca)) \/ e = fst last1)); 
  lem_merge_inva (v_of lca) (v_of s1) (v_of s2) (v_of (inverse_st s1)) (fst last1);
  //assert (forall e. (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) <==>
            //   (L.mem e (v_of lca) /\ L.mem e (v_of (inverse_st s1)) /\ L.mem e (v_of s2)));
  //assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==> 
             //  (L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) \/ e = fst last1));*)
  lem_do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1;
  //assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) \/ e = fst last1) <==>
   //            L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)); 
  ()

let linearizable_gt0_inv1_len2_1 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                       Enqueue? (snd last1) /\ Dequeue? (snd last2))) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) =
  let _, last1 = un_snoc (ops_of s1) in
  linearizable_gt0_inv1_len2_do_pre lca s1 s2;
  linearizable_gt0_inv1_len2_11 lca s1 s2;
  lem_length (concrete_merge (v_of lca) (v_of s1) (v_of s2))
             (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1);
  lem_equal (concrete_merge (v_of lca) (v_of s1) (v_of s2))
            (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)                        

let linearizable_gt0_inv1_len2_21 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                       Enqueue? (snd last1) /\ Enqueue? (snd last2) /\ lt (fst last2) (fst last1) /\
                       concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                          L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)))) =
  let p1, last1 = un_snoc (ops_of s1) in
  lem_foldl init_st (ops_of s1);
  lem_do (v_of (inverse_st s1)) last1; 
  //assert (forall e. L.mem e (v_of s1) <==> (L.mem e (v_of (inverse_st s1)) \/ e = fst last1));
  assume (not (L.mem (fst last1) (v_of lca)));
  //lem_diff_inv (v_of lca) (v_of s1) (v_of (inverse_st s1)) (fst last1);
  //assert (forall e. L.mem e (diff_s (v_of s1) (v_of lca)) <==> (L.mem e (diff_s (v_of (inverse_st s1)) (v_of lca)) \/ e = fst last1));
  lem_merge_inva (v_of lca) (v_of s1) (v_of s2) (v_of (inverse_st s1)) (fst last1);
  //assert (forall e. (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) <==>
              // (L.mem e (v_of lca) /\ L.mem e (v_of (inverse_st s1)) /\ L.mem e (v_of s2)));
  //assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==> 
              //  (L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) \/ e = fst last1)); 
  lem_do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1; 
  //assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) \/ e = fst last1) <==>
             //  L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)); 
  ()

let linearizable_gt0_inv1_len2_2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                       Enqueue? (snd last1) /\ Enqueue? (snd last2) /\ lt (fst last2) (fst last1))) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) =
  let _, last1 = un_snoc (ops_of s1) in
  linearizable_gt0_inv1_len2_do_pre lca s1 s2;
  linearizable_gt0_inv1_len2_21 lca s1 s2;
  lem_length (concrete_merge (v_of lca) (v_of s1) (v_of s2))
             (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1);
  lem_equal (concrete_merge (v_of lca) (v_of s1) (v_of s2))
            (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)  

let linearizable_gt0_inv2_len2_do_pre (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in  
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) = admit();
  let _,last2 = un_snoc (ops_of s2) in
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  assume (forall id. L.mem id (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) ==> lt id (fst last2));() //todo
  
let linearizable_gt0_inv2_len2_11 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Enqueue? (snd last2) /\
                       concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                          L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) =
  let p2, last2 = un_snoc (ops_of s2) in
  lem_foldl init_st (ops_of s2);
  lem_do (v_of (inverse_st s2)) last2; 
  //assert (forall e. L.mem e (v_of s2) <==> (L.mem e (v_of (inverse_st s2)) \/ e = fst last2));
  assume (not (L.mem (fst last2) (v_of lca))); //todo
  //assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==> (L.mem e (diff_s (v_of (inverse_st s2)) (v_of lca)) \/ e = fst last2));
  //lem_diff_inv (v_of lca) (v_of s2) (v_of (inverse_st s2)) (fst last2);
  lem_merge_invb (v_of lca) (v_of s1) (v_of s2) (v_of (inverse_st s2)) (fst last2);
  //assert (forall e. (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) <==>
          //     (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of (inverse_st s2))));
  //assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==> 
            //   (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) \/ e = fst last2)); 
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2;
  //assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) \/ e = fst last2) <==>
             //   L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)); 
 ()

let linearizable_gt0_inv2_len2_1 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Enqueue? (snd last2))) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) =
  let _, last2 = un_snoc (ops_of s2) in
  linearizable_gt0_inv2_len2_do_pre lca s1 s2;
  linearizable_gt0_inv2_len2_11 lca s1 s2;
  lem_length (concrete_merge (v_of lca) (v_of s1) (v_of s2))
             (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2);
  lem_equal (concrete_merge (v_of lca) (v_of s1) (v_of s2))
            (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)       

let linearizable_gt0_inv2_len2_21 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                       Enqueue? (snd last1) /\ Enqueue? (snd last2) /\ lt (fst last1) (fst last2) /\
                       concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                          L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) =
  let p2, last2 = un_snoc (ops_of s2) in
  lem_foldl init_st (ops_of s2);
  lem_do (v_of (inverse_st s2)) last2; 
  assume (not (L.mem (fst last2) (v_of lca))); //todo
  lem_merge_invb (v_of lca) (v_of s1) (v_of s2) (v_of (inverse_st s2)) (fst last2);
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2

let linearizable_gt0_inv2_len2_2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                       Enqueue? (snd last1) /\ Enqueue? (snd last2) /\ lt (fst last1) (fst last2))) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) =
  let _, last2 = un_snoc (ops_of s2) in
  linearizable_gt0_inv2_len2_do_pre lca s1 s2;
  linearizable_gt0_inv2_len2_21 lca s1 s2;
  lem_length (concrete_merge (v_of lca) (v_of s1) (v_of s2))
             (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2);
  lem_equal (concrete_merge (v_of lca) (v_of s1) (v_of s2))
            (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)

let linearizable_gt0_inv2_len2_311 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 <> return last2 /\ return last2 = None /\
                       concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                          L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) =
  let p2, last2 = un_snoc (ops_of s2) in
  lem_foldl init_st (ops_of s2);
  lem_do (v_of (inverse_st s2)) last2;
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2

let linearizable_gt0_inv2_len2_31 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 <> return last2 /\ return last2 = None)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                    concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                    do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) =
  let p2, last2 = un_snoc (ops_of s2) in
  linearizable_gt0_inv2_len2_do_pre lca s1 s2;
  linearizable_gt0_inv2_len2_311 lca s1 s2;
  lem_length (concrete_merge (v_of lca) (v_of s1) (v_of s2))
             (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2);
  lem_equal (concrete_merge (v_of lca) (v_of s1) (v_of s2))
            (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)

let linearizable_gt0_inv2_len2_321 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 <> return last2 /\ return last2 <> None /\
                       concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                          L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) =admit();
  let p2, last2 = un_snoc (ops_of s2) in
  lem_foldl init_st (ops_of s2);
  lem_do (v_of (inverse_st s2)) last2;
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2

let linearizable_gt0_inv2_len2_32 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 <> return last2 /\ return last2 <> None)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                    concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                    do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) =
  let p2, last2 = un_snoc (ops_of s2) in
  linearizable_gt0_inv2_len2_do_pre lca s1 s2;
  linearizable_gt0_inv2_len2_321 lca s1 s2;
  lem_length (concrete_merge (v_of lca) (v_of s1) (v_of s2))
             (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2);
  lem_equal (concrete_merge (v_of lca) (v_of s1) (v_of s2))
            (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
            
let linearizable_gt0_inv2_len2_3 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 2 /\
                       last (resolve_conflict last1 last2) = last2 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 <> return last2)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) =
  let _, last2 = un_snoc (ops_of s2) in
  if return last2 = None then
    linearizable_gt0_inv2_len2_31 lca s1 s2 else
      linearizable_gt0_inv2_len2_32 lca s1 s2

let linearizable_gt0_inv1_len1_do_pre (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                      (length (resolve_conflict last1 last2) = 1 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in  
                    concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)) = admit()

let linearizable_gt0_inv1_len1_11 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                       (length (resolve_conflict last1 last2) = 1 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 = return last2 /\ return last1 = None /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                       L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)))) =
  let p1, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  lem_do (v_of (inverse_st s1)) last1;
  lem_do (v_of (inverse_st s2)) last2;
  lem_do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1

let linearizable_gt0_inv1_len1_1 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                       (length (resolve_conflict last1 last2) = 1 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 = return last2 /\ return last1 = None)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1 /\
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)) =
  let p1, last1 = un_snoc (ops_of s1) in
  linearizable_gt0_inv1_len1_do_pre lca s1 s2;
  linearizable_gt0_inv1_len1_11 lca s1 s2;
  lem_length (concrete_merge (v_of lca) (v_of s1) (v_of s2))
             (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1);
  lem_equal (concrete_merge (v_of lca) (v_of s1) (v_of s2))
            (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)  

let linearizable_gt0_inv1_len1_21 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                       (length (resolve_conflict last1 last2) = 1 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 = return last2 /\ return last1 <> None /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                       L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)))) =
  let p1, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  lem_do (v_of (inverse_st s1)) last1;
  lem_do (v_of (inverse_st s2)) last2;
  
  (*lem_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2));
  assume (forall e. L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) <==> 
                      ((L.mem e (v_of lca) /\ L.mem e (v_of (inverse_st s1)) /\ L.mem e (v_of (inverse_st s2))) \/ 
                       L.mem e (diff_s (v_of (inverse_st s1)) (v_of lca)) \/ 
                       L.mem e (diff_s (v_of (inverse_st s2)) (v_of lca))));
 
  assume (Dequeue? (snd last1) /\ v_of (inverse_st s1) <> []); 
  assume (forall e. L.mem e (v_of s1) <==> (L.mem e (v_of (inverse_st s1)) /\ e <> L.hd (v_of (inverse_st s1))));
  assume (forall e. L.mem e (v_of s2) <==> (L.mem e (v_of (inverse_st s2)) /\ e <> L.hd (v_of (inverse_st s2)))); 
  assume (forall e. L.mem e (diff_s (v_of s1) (v_of lca)) <==> 
               (L.mem e (diff_s (v_of (inverse_st s1)) (v_of lca)) /\ e <> L.hd (v_of (inverse_st s1))));
  assume (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==> 
               (L.mem e (diff_s (v_of (inverse_st s2)) (v_of lca)) /\ e <> L.hd (v_of (inverse_st s1))));
  assume (forall e. (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) <==>
               ((L.mem e (v_of lca) /\ L.mem e (v_of (inverse_st s1)) /\ L.mem e (v_of (inverse_st s2))) /\
                 e <> L.hd (v_of (inverse_st s1))));
  assume (L.hd (v_of (inverse_st s1)) = L.hd (v_of (inverse_st s2)));

  lem_merge_invab (v_of lca) (v_of s1) (v_of s2) (v_of (inverse_st s1)) (v_of (inverse_st s2)) (L.hd (v_of (inverse_st s1)));*)
  assume (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==> 
               (L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) /\ 
                 e <> L.hd (v_of (inverse_st s1))));       
  //lem_do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1;
  assume (forall e. (L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) /\ 
              e <> L.hd (v_of (inverse_st s1))) <==>
              L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)); ()

let linearizable_gt0_inv1_len1_2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                       (length (resolve_conflict last1 last2) = 1 /\
                       last (resolve_conflict last1 last2) = last1 /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                       is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
                       Dequeue? (snd last1) /\ Dequeue? (snd last2) /\ return last1 = return last2 /\ return last1 <> None)) /\
                           
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1 /\
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)) =
  let p1, last1 = un_snoc (ops_of s1) in
  linearizable_gt0_inv1_len1_do_pre lca s1 s2;
  linearizable_gt0_inv1_len1_21 lca s1 s2;
  lem_length (concrete_merge (v_of lca) (v_of s1) (v_of s2))
             (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1);
  lem_equal (concrete_merge (v_of lca) (v_of s1) (v_of s2))
            (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1) 
            

#push-options "--z3rlimit 50"
let lem_mem (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\ 
                    //(exists atr. foldl_prop lca atr /\ s1 = seq_foldl lca atr) /\
                    //Enqueue? (snd o) /\
                    concrete_do_pre lca o /\
                    concrete_do_pre s1 o /\ s1' = do s1 o /\
                   // (forall e. L.mem e lca ==> e <> fst o) /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures (forall e. L.mem e (concrete_merge lca s1' s2) <==>
                         L.mem e (concrete_merge s1 (concrete_merge lca s1 s2) s1'))) 
  = ()
  
  
  (*match (diff_s s1 lca) with
    |[] -> assert (forall e. L.mem e s1 ==> lt e (fst o));
          assert (forall e. L.mem e lca <==> (L.mem e s1 \/ (L.mem e lca /\ not (L.mem e s1))));
          assume (forall e. (L.mem e lca /\ not (L.mem e s1)) ==> not (L.mem e s1)); 
          assume (forall e. (L.mem e lca /\ not (L.mem e s1)) ==> list_lt e s1); 
          //assert (forall e. L.mem e lca /\ not (L.mem e s1)  ==> lt e (fst o));
          (*assume (forall e. L.mem e (diff_s s1 lca) <==> L.mem e s1 /\ not (L.mem e lca)); 
          assume (forall e. L.mem e (diff_s s1 lca) ==> lt e (fst o)); 
          assume (forall e. L.mem e s1 /\ not (L.mem e lca) ==> lt e (fst o)); 
          assume (forall e. L.mem e s1 /\ (L.mem e lca) ==> lt e (fst o));
          assume (forall e. L.mem e lca /\ L.mem e s1 ==> lt e (fst o));
          assume (forall e. L.mem e lca ==> not (L.mem e (diff_s s1 lca))); 
          assume (forall e e1. L.mem e lca /\ L.mem e1 (diff_s s1 lca) ==> lt e e1 /\ lt e1 (fst o) /\ lt e (fst o));
          assume (forall e. L.mem e (diff_s s1 lca) ==> lt e (fst o)); 
          assume (lca = s1 ==> (forall e. L.mem e lca ==> lt e (fst o)));
          assume (forall e. L.mem e lca /\ not (L.mem e s1) ==> lt e (fst o)); *)
          (*assert ((forall e. L.mem e s1 ==> L.mem e lca) ==> (forall e. L.mem e lca ==> lt e (fst o)));
          assert (forall e e1. (L.mem e lca /\ not (L.mem e s1)) /\ (L.mem e1 lca /\ L.mem e1 s1) ==> lt e e1);
          assert (forall e. L.mem e lca /\ not (L.mem e s1) ==> lt e (fst o));
          admit();*)
          ()
    |_ -> lem_lt1 lca (diff_s s1 lca) (fst o)*)

let convergence1 (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre lca o /\
                    concrete_do_pre s1 o /\ s1' = do s1 o /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures concrete_merge lca s1' s2 == concrete_merge s1 (concrete_merge lca s1 s2) s1') =
  lem_mem lca s1 s2 s1' o;
  lem_length (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1');
  lem_equal (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1')
