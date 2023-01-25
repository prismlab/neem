module App_weak

open FStar.Seq
open FStar.Ghost
module L = FStar.List.Tot

#set-options "--query_stats"

val mem_id_s : id:nat 
             -> l:list (nat * nat)
             -> Tot (b:bool{(exists n. L.mem (id,n) l) <==> b=true})
let rec mem_id_s n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || mem_id_s n xs

val mem_ele : ele:nat 
             -> l:list (nat * nat)
             -> Tot (b:bool{(exists n. L.mem (n,ele) l) <==> b=true})
let rec mem_ele ele l =
  match l with
  |[] -> false
  |(_,ele1)::xs -> (ele = ele1) || mem_ele ele xs

val unique_s : l:list (nat * nat)
             -> Tot bool
let rec unique_s l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (mem_id_s id xs) && unique_s xs
  
// the concrete state type
type concrete_st:eqtype = l:list (nat (*unique id*) * nat (*element*)) {unique_s l}

// init state
let init_st = []

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  (forall ele. L.mem ele a <==> L.mem ele b)

// few properties of equivalence relation
let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a = b)
          (ensures eq a b) = ()

// operation type
type op_t:eqtype =
  |Add : nat -> op_t
  |Rem : nat -> op_t

let get_ele (o:log_entry) : nat =
  match snd o with
  |Add e -> e
  |Rem e -> e

let rec mem_id_ele_l (id:nat) (ele:nat) (l:log) 
  : Tot (b:bool{b = true <==> (exists e. mem e l /\ fst e = id /\ get_ele e = ele)}) (decreases length l) =
  match length l with
  |0 -> false
  |_ -> (fst (head l) = id && get_ele (head l) = ele) || mem_id_ele_l id ele (tail l)

val filter : f:((nat * nat) -> bool)
           -> l:concrete_st
           -> Tot (l1:concrete_st {(forall e. L.mem e l1 /\ mem_id_s (fst e) l1 <==> L.mem e l /\ mem_id_s (fst e) l /\ f e)})
let rec filter f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter f tl) else filter f tl

// concrete do pre-condition
let concrete_do_pre (s:concrete_st) (op:log_entry) : prop =
  ~ (mem_id_s (fst op) s)

// apply an operation to a state
let do (s:concrete_st) (o:log_entry{concrete_do_pre s o}) 
    : (r:concrete_st{(Add? (snd o) ==> (forall ele. mem_ele ele r <==> (mem_ele ele s \/ ele = get_ele o)) /\
                                      (forall e. L.mem e r <==> (L.mem e s \/ (e = (fst o, get_ele o)))) /\
                                      (forall id. mem_id_s id r <==> (mem_id_s id s \/ id = fst o))) /\
                     (Rem? (snd o) ==> (forall ele. mem_ele ele r <==> (mem_ele ele s /\ ele <> get_ele o)) /\
                                      (forall e. L.mem e r <==> (L.mem e s /\ snd e <> get_ele o)) /\
                                      (forall id. mem_id_s id r ==> mem_id_s id s))}) =
  match o with
  |(id, Add e) -> (id, e)::s
  |(id, Rem e) -> filter (fun ele -> snd ele <> e) s

let do_prop (s:concrete_st) (o:log_entry{concrete_do_pre s o}) 
  : Lemma (ensures (Add? (snd o) ==> ((forall e. L.mem e (do s o) <==> (L.mem e s \/ e = (fst o, get_ele o))) /\
                                    (forall id. mem_id_s id (do s o) <==> (mem_id_s id s \/ id = fst o)))) /\
                   (Rem? (snd o) ==> ((forall e. L.mem e (do s o) <==> (L.mem e s /\ snd e <> get_ele o)) /\
                                    (forall id. mem_id_s id (do s o) ==> mem_id_s id s)))) = ()

let lem_do (a b:concrete_st) (op:log_entry)
   : Lemma (requires concrete_do_pre a op /\ eq a b)
           (ensures concrete_do_pre b op /\ eq (do a op) (do b op)) = ()
           
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
let concrete_st_s = list nat

// init state 
let init_st_s = []

val filter_seq : f:(nat -> bool)
               -> l:concrete_st_s
               -> Tot (l1:concrete_st_s {(forall e. L.mem e l1 <==> L.mem e l /\ f e)})
let rec filter_seq f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter_seq f tl) else filter_seq f tl
  
// apply an operation to a state 
let do_s (st_s:concrete_st_s) (o:log_entry) 
  : (r:concrete_st_s{(Add? (snd o) ==> (forall e. L.mem e r <==> L.mem e st_s \/ e = get_ele o)) /\
                     (Rem? (snd o) ==> (forall e. L.mem e r <==> L.mem e st_s /\ e <> get_ele o))}) =
  match snd o with
  |(Add e) -> e::st_s
  |(Rem e) -> filter_seq (fun ele -> ele <> e) st_s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  (forall e. L.mem e st_s <==> mem_ele e st)

//initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq_sm st_s st /\ concrete_do_pre st op)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////

val exists_op : f:(log_entry -> bool)
              -> l:log
              -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true}) (decreases length l)
let rec exists_op f l =
  match length l with
  | 0 -> false
  | _ -> if f (head l) then true else exists_op f (tail l)
  
#push-options "--z3rlimit 50"
let rec get_ele_l (l:log{(*distinct_ops l /\*) (forall e. mem e l ==> Add? (snd e))})
  : Tot (r:list (nat * nat){(forall e. L.mem e r <==> mem_id_ele_l (fst e) (snd e) l) /\
                        (forall id. mem_id_s id r <==> mem_id id l)}) (decreases length l) =
  match length l with
  |0 -> []
  |_ -> (fst (head l), get_ele (head l))::get_ele_l (tail l)

#push-options "--z3rlimit 100"
let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires foldl_prop s l)
          (ensures (length l = 0 ==> s = seq_foldl s l) /\
                   (length l > 0 ==> (let p,last = un_snoc l in
                           (foldl_prop s p /\
                           concrete_do_pre (seq_foldl s p) (last) /\
                           (seq_foldl s l = do (seq_foldl s p) (last)) /\
             (Add? (snd last) ==> (forall e. L.mem e (seq_foldl s l) <==> L.mem e (seq_foldl s p) \/ e = (fst last, get_ele last))) /\
             (Rem? (snd last) ==> (forall e. L.mem e (seq_foldl s l) <==> L.mem e (seq_foldl s p) /\ snd e <> get_ele last))))) /\
             (forall id. mem_id_s id (seq_foldl s l) ==> mem_id_s id s \/ mem_id id l) (*/\
             (forall e. L.mem e (seq_foldl s l) <==> L.mem e s \/ L.mem e (get_ele_l (unmatched_add l))*))
          (decreases length l)
  = match length l with
    |0 -> ()
    |1 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

//operations x and y are commutative
let commutative (x y:log_entry) =
  not (((Add? (snd x) && Rem? (snd y) && get_ele x = get_ele y) ||
        (Add? (snd y) && Rem? (snd x) && get_ele x = get_ele y)))

// if x and y are commutative ops, applying them in any order should give equivalent results
let commutative_prop (x y:log_entry) 
  : Lemma (requires commutative x y /\ (forall s. foldl_prop s (cons x (cons y empty)) /\
                                            foldl_prop s (cons y (cons x empty))))
          (ensures (forall s. eq (seq_foldl s (cons x (cons y empty))) (seq_foldl s (cons y (cons x empty))))) = ()
                   
//conflict resolution
let resolve_conflict (x y:log_entry) : (l:log{(*Seq.length l = 1 \/*) Seq.length l = 2 /\ (forall e. mem e l <==> e = x \/ e = y)}) =
  if (get_ele x = get_ele y && Add? (snd x) && Rem? (snd y)) then 
    cons y (cons x empty) else
      cons x (cons y empty)

let resolve_conflict_prop (x y:log_entry) 
  : Lemma (requires fst x <> fst y)
          (ensures Seq.length (resolve_conflict x y) = 2 /\
                   (last (resolve_conflict x y) = x <==> (Add? (snd x) /\ Rem? (snd y) /\ get_ele x = get_ele y)) /\
                   (last (resolve_conflict x y) <> x <==> last (resolve_conflict x y) = y) /\
                   (last (resolve_conflict x y) = y <==> ((Add? (snd x) /\ Rem? (snd y) /\ get_ele x <> get_ele y) \/
                                                        (Add? (snd x) /\ Add? (snd y)) \/
                                                        (Rem? (snd x) /\ Rem? (snd y)) \/
                                                        (Rem? (snd x) /\ Add? (snd y)))))
  = ()

// remove ele from l
let rec remove (l:concrete_st) (ele:(nat * nat){L.mem ele l})
  : Tot (res:concrete_st{(forall e. L.mem e res <==> L.mem e l /\ e <> ele) /\
                         (forall id. mem_id_s id res <==> mem_id_s id l /\ id <> fst ele)}) =
  match l with
  |[] -> []
  |x::xs -> if x = ele then xs else x::remove xs ele

// a - l
let diff_s (a l:concrete_st) 
  : Tot (d:concrete_st{(forall e. L.mem e d <==> (L.mem e a /\ not (L.mem e l)))}) =
  filter (fun e -> not (L.mem e l)) a

// concrete merge pre-condition
let concrete_merge_pre (lca a b:concrete_st) : prop =
  (forall id. mem_id_s id (diff_s a lca) ==> not (mem_id_s id b)) 

let lem_merge_pre (lca a b:concrete_st)
  : Lemma (concrete_merge_pre lca a b <==> 
          (forall id. mem_id_s id (diff_s a lca) ==> not (mem_id_s id b))) = ()

#push-options "--z3rlimit 100"
val concrete_merge1 (l a b:concrete_st)
           : Pure concrete_st
             (requires concrete_merge_pre l a b)
             (ensures (fun res -> (forall e. L.mem e res <==> (L.mem e l /\ L.mem e a /\ L.mem e b) \/ 
                                                    (L.mem e (diff_s a l)) \/ (L.mem e (diff_s b l))) (*/\
                               (forall id. mem_id_s id res <==> (mem_id_s id l /\ mem_id_s id a /\ mem_id_s id b) \/ 
                                                    (mem_id_s id (diff_s a l)) \/ (mem_id_s id (diff_s b l))*)))
                               (decreases %[l;a;b])
let rec concrete_merge1 l a b =
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> if (L.mem x a && L.mem x b) then x::(concrete_merge1 xs (remove a x) (remove b x)) 
                 else if (L.mem x a) then (concrete_merge1 xs (remove a x) b)
                   else if (L.mem x b) then (concrete_merge1 xs a (remove b x))
                     else (concrete_merge1 xs a b)
  |[],x::xs,_ -> x::(concrete_merge1 [] xs b)
  |[],[],x::xs -> b
#pop-options

// concrete merge operation
let concrete_merge (l:concrete_st) (a:concrete_st) (b:concrete_st{concrete_merge_pre l a b}) 
    : Tot (res:concrete_st {(forall e. L.mem e res <==> (L.mem e l /\ L.mem e a /\ L.mem e b) \/ 
                                                 (L.mem e (diff_s a l)) \/ (L.mem e (diff_s b l)))})  =
 concrete_merge1 l a b

let rec lem_seq_foldl_op (x:concrete_st) (l:log) (op:log_entry)
  : Lemma (requires distinct_ops l /\ mem op l /\ foldl_prop x l /\
                    (let _, suf = pre_suf l op in commutative_seq op suf))
          (ensures (let p,s = pre_suf l op in
                      foldl_prop x (p ++ s) /\ 
                      concrete_do_pre (seq_foldl x (p ++ s)) op /\
                      eq (seq_foldl x l) (do (seq_foldl x (p ++ s)) op)))
          (decreases length l) = 
  match length l with
  |0 -> ()
  |_ -> admit()

type common_pre (lca s1 s2:st) =
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
  Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
  concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))
  
#push-options "--z3rlimit 300"
let merge_inv_prop_inv2' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    exists_triple last1 (diff (ops_of s2) (ops_of lca))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                       suf2 = snd (pre_suf (ops_of s2) op2) /\
                       (let inv2 = inverse_st_op s2 op2 in
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2))))) =
  let _, last1 = un_snoc (ops_of s1) in
  let (pre, op, suf) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  lem_suf_equal (ops_of lca) (ops_of s2) op;
  assert (suf = snd (pre_suf (ops_of s2) op));
  lem_inverse_op (ops_of lca) (ops_of s2) op; 
  assert (commutative_seq op suf);  
  assert (last (resolve_conflict last1 op) = op); 
  lastop_diff (ops_of lca) (ops_of s1);
  assert (fst last1 <> fst op);
  resolve_conflict_prop last1 op;
  assert (Add? (snd op) /\ Rem? (snd last1) /\ get_ele last1 = get_ele op);
  let inv2 = inverse_st_op s2 op in 
  do_prop (v_of inv2) op;
  assert (forall e. (L.mem e (v_of inv2) \/ e = (fst op, get_ele op)) <==> L.mem e (v_of s2));
  assert (forall id. (mem_id_s id (v_of inv2) \/ id = fst op) <==> mem_id_s id (v_of s2));  
  assert (forall id. mem_id_s id (v_of inv2) ==> mem_id_s id (v_of s2)); 
  lem_merge_pre (v_of lca) (v_of s1) (v_of inv2)
                    
let merge_inv_prop_inv1' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                    exists_triple last2 (diff (ops_of s1) (ops_of lca))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                       suf1 = snd (pre_suf (ops_of s1) op1) /\
                       (let inv1 = inverse_st_op s1 op1 in
                       concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2))))) = admit()
                       
let merge_inv_prop_inv1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last1))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) = 
  let p1, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  resolve_conflict_prop last1 last2; 
  assert (Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last2 = get_ele last1);
  let inv1 = inverse_st s1 in
  lem_foldl init_st (ops_of s1);
  
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s1); 
  inverse_diff_id (ops_of lca) (ops_of s1) (ops_of s2);
  lem_foldl init_st (ops_of inv1); 
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of inv1);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of inv1) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))

let merge_inv_prop_inv2_c2_c4 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last2 /\
                     Add? (snd last2)))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2); 
  inverse_diff_id (ops_of lca) (ops_of s1) (ops_of s2);
  lem_foldl init_st (ops_of inv2); 
  lem_foldl init_st (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of inv2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of inv2) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

let merge_inv_prop_inv2_c3 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last2 /\
                     Rem? (snd last1) /\ Rem? (snd last2)))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = admit()
  
let merge_inv_prop_inv2_c1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last2 /\
                     Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 <> get_ele last2))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = admit()

let merge_inv_prop (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2)
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==> 
                      (let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                        suf2 = snd (pre_suf (ops_of s2) op2) /\
                        concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st_op s2 op2)))) /\
                        
                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==> 
                      (let (pre1, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                        suf1 = snd (pre_suf (ops_of s1) op1) /\
                        concrete_merge_pre (v_of lca) (v_of (inverse_st_op s1 op1)) (v_of s2))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  if exists_triple last1 (diff (ops_of s2) (ops_of lca)) 
    then merge_inv_prop_inv2' lca s1 s2
  else if exists_triple last2 (diff (ops_of s1) (ops_of lca)) 
    then merge_inv_prop_inv1' lca s1 s2
  else if last (resolve_conflict last1 last2) = last1
    then merge_inv_prop_inv1 lca s1 s2
  else 
    match snd last1, snd last2 with
    |_, Add _ -> merge_inv_prop_inv2_c2_c4 lca s1 s2
    |Add _, Rem _ -> merge_inv_prop_inv2_c1 lca s1 s2
    |Rem _, Rem _ -> merge_inv_prop_inv2_c3 lca s1 s2

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()
  
let linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    ops_of s2 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

#push-options "--z3rlimit 200"
let linearizable_gt0_pre (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                     (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                        suf2 = snd (pre_suf (ops_of s2) op2) /\
                        (let inv2 = inverse_st_op s2 op2 in
                        concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)))) /\

                      ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                        exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                        suf1 = snd (pre_suf (ops_of s1) op1) /\
                        (let inv1 = inverse_st_op s1 op1 in
                        concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2)))) /\

                     ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                     (last (resolve_conflict last1 last2) = last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                           concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                           
                     (last (resolve_conflict last1 last2) <> last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                           concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                       (let inv2 = inverse_st_op s2 op2 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                       (let inv1 = inverse_st_op s1 op1 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                    
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1) /\
                       
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) = admit()

let trans_op (a b c:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. L.mem e a <==> (L.mem e b \/ e = ele)) /\
                    (forall e. (L.mem e b \/ e = ele) <==> L.mem e c))
          (ensures eq a c) = ()

let trans_op_ele (a b c:concrete_st) (ele:nat)
  : Lemma (requires (forall e. L.mem e a <==> (L.mem e b /\ snd e <> ele)) /\
                    (forall e. (L.mem e b /\ snd e <> ele) <==> L.mem e c))
          (ensures eq a c) = ()

let trans_op_not (a b c:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. L.mem e a <==> (L.mem e b /\ e <> ele)) /\
                    (forall e. (L.mem e b /\ e <> ele) <==> L.mem e c))
          (ensures eq a c) = ()

let lem_diff_s (l s1 inv1:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. L.mem e inv1 \/ e = ele <==> L.mem e s1) /\
                    (forall e. L.mem e inv1 <==> L.mem e s1 /\ e <> ele) /\
                    (forall e. L.mem e (diff_s inv1 l) <==> L.mem e (diff_s s1 l) /\ e <> ele) /\
                    (forall e. L.mem e s1 <==> L.mem e (diff_s s1 l) \/ L.mem e l) /\
                    (forall e. L.mem e inv1 <==> L.mem e (diff_s inv1 l) \/ L.mem e l))
          (ensures (forall e. L.mem e (diff_s inv1 l) \/ e = ele <==> L.mem e (diff_s s1 l))) = ()
  
let lem_merge_inv2 (l s1 s2 inv2:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. (L.mem e (diff_s inv2 l) \/ e = ele) <==> (L.mem e (diff_s s2 l))) /\
                     concrete_merge_pre l s1 inv2 /\ concrete_merge_pre l s1 s2 /\
                    (forall e. L.mem e (concrete_merge l s1 inv2) <==> (L.mem e (concrete_merge l s1 s2) /\ e <> ele)))
          (ensures (forall e. (L.mem e (concrete_merge l s1 inv2) \/ e = ele) <==> L.mem e (concrete_merge l s1 s2))) = ()

let lem_merge_inv1 (l s1 s2 inv1:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. (L.mem e (diff_s inv1 l) \/ e = ele) <==> (L.mem e (diff_s s1 l))) /\
                     concrete_merge_pre l inv1 s2 /\ concrete_merge_pre l s1 s2 /\
                    (forall e. L.mem e (concrete_merge l inv1 s2) <==> (L.mem e (concrete_merge l s1 s2) /\ e <> ele)))
          (ensures (forall e. (L.mem e (concrete_merge l inv1 s2) \/ e = ele) <==> L.mem e (concrete_merge l s1 s2))) = ()

let lemma1 (a b:concrete_st) (ele:(nat * nat))
  : Lemma (requires L.mem ele b /\ (forall e. L.mem e a <==> L.mem e b /\ e <> ele))
          (ensures (forall e. L.mem e a \/ e = ele <==> L.mem e b)) = ()
            
#push-options "--z3rlimit 500"
let linearizable_gt0_inv2' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                   (let _, last1 = un_snoc (ops_of s1) in
                    exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\
                   (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    suf2 = snd (pre_suf (ops_of s2) op2) /\
                   (let inv2 = inverse_st_op s2 op2 in
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2) /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let inv2 = inverse_st_op s2 op2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))  = 
  let _, last1 = un_snoc (ops_of s1) in
  let (pre, op, suf) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  lem_inverse_op (ops_of lca) (ops_of s2) op;
  assert (commutative_seq op suf); 
  assert (last (resolve_conflict last1 op) = op); 
  lastop_diff (ops_of lca) (ops_of s1);
  //assert (mem_id (fst last1) (diff (ops_of s1) (ops_of lca))); 
  //assert (mem_id (fst op) (diff (ops_of s2) (ops_of lca)));
  assert (fst last1 <> fst op); 
  resolve_conflict_prop last1 op;
  assert (Add? (snd op) /\ Rem? (snd last1) /\ get_ele last1 = get_ele op);
  let inv2 = inverse_st_op s2 op in
  do_prop (v_of inv2) op;
  assert (forall e. (L.mem e (v_of inv2) \/ e = (fst op, get_ele op)) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (v_of inv2) <==> (L.mem e (v_of s2) /\ e <> (fst op, get_ele op)));
  assert (forall e. L.mem e (diff_s (v_of inv2) (v_of lca)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)) /\ e <> (fst op, get_ele op));
  assume (L.mem (fst op, get_ele op) (diff_s (v_of s2) (v_of lca))); //todo
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst op, get_ele op)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)));         
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst op, get_ele op))); 

  lemma1 (diff_s (v_of inv2) (v_of lca)) (diff_s (v_of s2) (v_of lca)) (fst op, get_ele op);
  assert (forall e. (L.mem e (diff_s (v_of inv2) (v_of lca)) \/ e = (fst op, get_ele op)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)));   

  lem_merge_inv2 (v_of lca) (v_of s1) (v_of s2) (v_of inv2) (fst op, get_ele op); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst op, get_ele op)));

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst op, get_ele op)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op));

  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
           (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op)
           (fst op, get_ele op);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

let linearizable_gt0_inv1' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     exists_triple last2 (diff (ops_of s1) (ops_of lca)) /\
                    (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                     suf1 = snd (pre_suf (ops_of s1) op1) /\
                    (let inv1 = inverse_st_op s1 op1 in
                     concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    let inv1 = inverse_st_op s1 op1 in
                    eq (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last2 = un_snoc (ops_of s2) in
  let (pre, op, suf) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  lem_inverse_op (ops_of lca) (ops_of s1) op;
  assert (commutative_seq op suf); 
  assert (last (resolve_conflict last2 op) = op); 
  lastop_diff (ops_of lca) (ops_of s2);
  //assert (mem_id (fst last2) (diff (ops_of s2) (ops_of lca)));
  //assert (mem_id (fst op) (diff (ops_of s1) (ops_of lca)));
  assert (fst last2 <> fst op); 
  resolve_conflict_prop last2 op;
  assert (Add? (snd op) /\ Rem? (snd last2) /\ get_ele last2 = get_ele op); 
  let inv1 = inverse_st_op s1 op in
  do_prop (v_of inv1) op;
  assert (forall e. (L.mem e (v_of inv1) \/ e = (fst op, get_ele op)) <==> L.mem e (v_of s1));
  assert (forall e. L.mem e (v_of inv1) <==> (L.mem e (v_of s1) /\ e <> (fst op, get_ele op))); 
  assert (forall e. L.mem e (diff_s (v_of inv1) (v_of lca)) <==>
               L.mem e (diff_s (v_of s1) (v_of lca)) /\ e <> (fst op, get_ele op)); 
  assume (L.mem (fst op, get_ele op) (diff_s (v_of s1) (v_of lca))); //todo
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst op, get_ele op)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of inv1) /\ L.mem e (v_of s2)));    
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst op, get_ele op)));  

  lemma1 (diff_s (v_of inv1) (v_of lca)) (diff_s (v_of s1) (v_of lca)) (fst op, get_ele op);
  assert (forall e. (L.mem e (diff_s (v_of inv1) (v_of lca)) \/ e = (fst op, get_ele op)) <==>
               L.mem e (diff_s (v_of s1) (v_of lca)));   

  lem_merge_inv1 (v_of lca) (v_of s1) (v_of s2) (v_of inv1) (fst op, get_ele op); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) \/ e = (fst op, get_ele op))); 

  do_prop (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) \/ e = (fst op, get_ele op)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op));  

  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of inv1) (v_of s2))
           (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op)
           (fst op, get_ele op);
  assert (eq (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

let linearizable_gt0_inv1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last1 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                     concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let p1, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2);
  resolve_conflict_prop last1 last2; 
  assert (Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last2 = get_ele last1);
  let inv1 = inverse_st s1 in
  lem_foldl init_st (ops_of s1);
  assert (forall e. (L.mem e (v_of inv1) \/ e = (fst last1, get_ele last1)) <==> L.mem e (v_of s1));
  assert (forall e. L.mem e (v_of inv1) <==> (L.mem e (v_of s1) /\ e <> (fst last1, get_ele last1)));
  assert (forall e. L.mem e (diff_s (v_of inv1) (v_of lca)) <==>
               L.mem e (diff_s (v_of s1) (v_of lca)) /\ e <> (fst last1, get_ele last1));
  assume (L.mem (fst last1, get_ele last1) (diff_s (v_of s1) (v_of lca))); //todo
  lemma1 (diff_s (v_of inv1) (v_of lca)) (diff_s (v_of s1) (v_of lca)) (fst last1, get_ele last1);
  assert (forall e. (L.mem e (diff_s (v_of inv1) (v_of lca)) \/ e = (fst last1, get_ele last1)) <==>
               L.mem e (diff_s (v_of s1) (v_of lca)));
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst last1, get_ele last1)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of inv1) /\ L.mem e (v_of s2))); 
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst last1, get_ele last1)));
  
  lem_merge_inv1 (v_of lca) (v_of s1) (v_of s2) (v_of inv1) (fst last1, get_ele last1); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) \/ e = (fst last1, get_ele last1)));
  
  do_prop (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) last1;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) \/ e = (fst last1, get_ele last1)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) last1));
  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of inv1) (v_of s2))
           (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) last1)
           (fst last1, get_ele last1)

let linearizable_gt0_inv2_c2 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Add? (snd last1) /\ Add? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2);
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) \/ e = (fst last2, get_ele last2)) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (v_of inv2) <==> (L.mem e (v_of s2) /\ e <> (fst last2, get_ele last2)));
  assert (forall e. L.mem e (diff_s (v_of inv2) (v_of lca)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)) /\ e <> (fst last2, get_ele last2)); 
  assume (L.mem (fst last2, get_ele last2) (diff_s (v_of s2) (v_of lca))); //todo
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst last2, get_ele last2)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)));         
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst last2, get_ele last2))); 

  lemma1 (diff_s (v_of inv2) (v_of lca)) (diff_s (v_of s2) (v_of lca)) (fst last2, get_ele last2);
  assert (forall e. (L.mem e (diff_s (v_of inv2) (v_of lca)) \/ e = (fst last2, get_ele last2)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)));   

  lem_merge_inv2 (v_of lca) (v_of s1) (v_of s2) (v_of inv2) (fst last2, get_ele last2); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst last2, get_ele last2)));

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst last2, get_ele last2)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
           (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
           (fst last2, get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

let linearizable_gt0_inv2_c4 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Rem? (snd last1) /\ Add? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2);
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) \/ e = (fst last2, get_ele last2)) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (v_of inv2) <==> (L.mem e (v_of s2) /\ e <> (fst last2, get_ele last2)));
  assert (forall e. L.mem e (diff_s (v_of inv2) (v_of lca)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)) /\ e <> (fst last2, get_ele last2)); 
  assume (L.mem (fst last2, get_ele last2) (diff_s (v_of s2) (v_of lca))); //todo
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst last2, get_ele last2)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)));         
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst last2, get_ele last2))); 

  lemma1 (diff_s (v_of inv2) (v_of lca)) (diff_s (v_of s2) (v_of lca)) (fst last2, get_ele last2);
  assert (forall e. (L.mem e (diff_s (v_of inv2) (v_of lca)) \/ e = (fst last2, get_ele last2)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)));   

  lem_merge_inv2 (v_of lca) (v_of s1) (v_of s2) (v_of inv2) (fst last2, get_ele last2); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst last2, get_ele last2)));

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst last2, get_ele last2)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
           (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
           (fst last2, get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

let linearizable_gt0_inv2_c3 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Rem? (snd last1) /\ Rem? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2);
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) /\ snd e <> get_ele last2) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==>
               L.mem e (diff_s (v_of inv2) (v_of lca)) /\ snd e <> get_ele last2); 
  assume (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca)))); //todo
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)) /\ snd e <> get_ele last2) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)));   
  
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2));  

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
               (get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

let linearizable_gt0_inv2_c1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2);
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) /\ snd e <> get_ele last2) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==>
               L.mem e (diff_s (v_of inv2) (v_of lca)) /\ snd e <> get_ele last2); 
  assume (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca)))); //todo
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)) /\ snd e <> get_ele last2) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)));   
  
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2));  

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
               (get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

#push-options "--z3rlimit 500"
let linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                     (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                        suf2 = snd (pre_suf (ops_of s2) op2) /\
                        (let inv2 = inverse_st_op s2 op2 in
                        concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)))) /\

                      ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                        exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                        suf1 = snd (pre_suf (ops_of s1) op1) /\
                        (let inv1 = inverse_st_op s1 op1 in
                        concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2)))) /\

                     ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                     (last (resolve_conflict last1 last2) = last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                           concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                           
                     (last (resolve_conflict last1 last2) <> last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                           concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                       (let inv2 = inverse_st_op s2 op2 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2 /\
                       eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)
                          (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                       (let inv1 = inverse_st_op s1 op1 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1 /\
                       eq (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
                          (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                    
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                      eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))) /\
                       
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                      eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2)))))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  linearizable_gt0_pre lca s1 s2;
  if exists_triple last1 (diff (ops_of s2) (ops_of lca)) 
     then linearizable_gt0_inv2' lca s1 s2
  else if exists_triple last2 (diff (ops_of s1) (ops_of lca)) 
     then (assert (not (exists_triple last1 (diff (ops_of s2) (ops_of lca)))); linearizable_gt0_inv1' lca s1 s2)
  else if last (resolve_conflict last1 last2) = last1
     then (assert (not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                   not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))); linearizable_gt0_inv1 lca s1 s2)
  else (assert (not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                last (resolve_conflict last1 last2) = last2);
    match snd last1, snd last2 with
    |Add _, Add _ -> linearizable_gt0_inv2_c2 lca s1 s2
    |Add _, Rem _ -> linearizable_gt0_inv2_c1 lca s1 s2
    |Rem _, Add _ -> linearizable_gt0_inv2_c4 lca s1 s2
    |Rem _, Rem _ -> linearizable_gt0_inv2_c3 lca s1 s2)
                
let convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre lca o /\
                    concrete_do_pre s1 o /\ s1' = do s1 o /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures eq (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1')) = ()
          


