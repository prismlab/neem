module App

open FStar.Seq
open FStar.Ghost
module L = FStar.List.Tot

let rec unique_s (l:list nat) =
  match l with
  |[] -> true
  |id::xs -> not (L.mem id xs) && unique_s xs

type gset_st = l:list nat{unique_s l}

let rec mem_k (k:nat) (l:list (nat * gset_st)) : (b:bool{(exists e. L.mem e l /\ fst e = k) /\ (exists s. L.mem (k,s) l) <==> b = true}) =
  match l with
  |[] -> false
  |(k1,s)::xs -> k1 = k || mem_k k xs

let rec unique_k (l:list (nat * gset_st)) =
  match l with
  |[] -> true
  |(x,s)::xs -> not (mem_k x xs) && unique_k xs

// the concrete state type
// It is a list of unique elements
type concrete_st = l:list (nat * gset_st){unique_k l}

let rec mem_kv (k v:nat) (l:concrete_st) 
  : (b:bool{b = true <==> ((exists e. L.mem e l /\ fst e = k /\ L.mem v (snd e)) /\ mem_k k l /\
                         (exists s. L.mem (k,s) l))}) =
  match l with
  |[] -> false
  |x::xs -> (k = fst x && L.mem v (snd x)) || mem_kv k v xs

let rec get_set (k:nat) (st:concrete_st{mem_k k st}) 
    : (r:gset_st{L.mem (k,r) st /\ (forall e. L.mem e r <==> mem_kv k e st)}) =
  match st with
  |[] -> []
  |(x,s)::xs -> if x = k then s else get_set k xs

//initial state
let init_st = []

let eq (a b:concrete_st) =
  (forall k v. mem_kv k v a <==> mem_kv k v b)

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
// (the only operation is Add, so nat * nat is fine)
type op_t = nat * nat

let key (op:log_entry) = fst (snd op)

let value (op:log_entry) = snd (snd op)

// concrete do pre-condition
let concrete_do_pre _ _ = true

#push-options "--z3rlimit 100"
let rec add_v (k v:nat) (s:concrete_st)
  : Pure concrete_st 
    (requires mem_k k s)
    (ensures (fun r -> (forall k1. mem_k k1 r <==> mem_k k1 s) /\
                    (forall e. L.mem e r /\ fst e <> k <==> L.mem e s /\ fst e <> k) /\
                    (forall (e1 e2:nat * gset_st). L.mem e1 s /\ L.mem e2 r /\ fst e1 = k /\ fst e2 = k ==> 
                               (forall e3. L.mem e3 (snd e1) \/ e3 = v <==> L.mem e3 (snd e2))) /\
                    (forall k1 v1. mem_kv k1 v1 r <==> mem_kv k1 v1 s \/ (k1 = k /\ v1 = v)))) =
  match s with
  |x::xs -> if k = fst x && L.mem v (snd x) then s
             else if k = fst x then ((k, (v::(snd x)))::xs)
               else (x::add_v k v xs)

let do (s:concrete_st) (op:log_entry) 
  : (r:concrete_st{(forall k. mem_k k r <==> mem_k k s \/ k = key op) /\
                   (forall k v. mem_kv k v r <==> mem_kv k v s \/ (k = key op /\ v = value op)) /\
                   (forall e. L.mem e r /\ fst e <> key op <==> L.mem e s /\ fst e <> key op)}) = 
  match s with
  |[] -> [key op, [value op]]
  |x::xs -> if mem_k (key op) s then add_v (key op) (value op) s 
             else  ((key op, [value op])::s)

let lem_do (a b:concrete_st) (op:log_entry)
   : Lemma (requires concrete_do_pre a op /\ eq a b)
           (ensures concrete_do_pre b op /\ eq (do a op) (do b op)) =
   assert (forall k v. mem_kv k v (do b op) <==> mem_kv k v a \/ (k = key op /\ v = value op)); ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = concrete_st

// init state 
let init_st_s = []

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:log_entry) : concrete_st_s = 
  do s op

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) 
  = assert (forall k v. mem_kv k v (do_s st_s op) <==> mem_kv k v st \/ (k = key op /\ v = value op)); ()

////////////////////////////////////////////////////////////////

let rec mem_kv_l (k v:nat) (l:log) 
  : Tot (b:bool{b = true <==> (exists e. mem e l /\ key e = k /\ value e = v)}) (decreases length l) =
  match length l with
  |0 -> false
  |_ -> (k = key (head l) && v = value (head l)) || mem_kv_l k v (tail l)

let rec mem_k_l (k:nat) (l:log) : Tot (b:bool{(exists e. mem e l /\ key e = k) <==> b = true}) (decreases length l) =
  match length l with
  |0 -> false
  |_ -> key (head l) = k || mem_k_l k (tail l)

#push-options "--z3rlimit 100"
let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires foldl_prop s l)
          (ensures (length l = 0 ==> s = seq_foldl s l) /\
                   (forall k. mem_k k (seq_foldl s l) <==> mem_k k s \/ mem_k_l k l) /\
                   (forall k v. mem_kv k v (seq_foldl s l) <==> mem_kv k v s \/ mem_kv_l k v l) /\
                   (length l > 0 ==>
                     (let p,last = un_snoc l in
                      foldl_prop s p /\
                      (forall k. mem_k k (seq_foldl s l) <==> mem_k k (seq_foldl s p) \/ k = key last) /\
                      (forall k v. mem_kv k v (seq_foldl s l) <==> mem_kv k v (seq_foldl s p) \/ (k = key last /\ v = value last)) /\
                      concrete_do_pre (seq_foldl s p) (last) /\
                      (seq_foldl s l = do (seq_foldl s p) (last)))))
          (decreases length l)
  = match length l with
    |0 -> ()
    |1 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)
#pop-options

//conflict resolution
let resolve_conflict (x y:log_entry) : log =
  cons x (cons y empty)

let resolve_conflict_prop (x y:log_entry)
  : Lemma (requires fst x <> fst y)
          (ensures last (resolve_conflict x y) <> x)
  = ()

let rec rem_k (k:nat) (l:concrete_st)
    : Tot (r:concrete_st{(forall e. L.mem e r <==> L.mem e l /\ fst e <> k) /\
                         (forall k1 v1. mem_kv k1 v1 r <==> mem_kv k1 v1 l /\ k1 <> k)}) = 
  match l with
  |[] -> []
  |(x,s)::xs -> if k = x then xs else (x,s)::rem_k k xs

let concrete_merge_pre_g (lca a b:gset_st) : prop = 
  (forall e. L.mem e lca ==> L.mem e a /\ L.mem e b)

// concrete merge operation
let rec concrete_merge1_g (lca:gset_st) (s1:gset_st)
  : Pure gset_st (requires true)
                     (ensures (fun r -> (forall e. L.mem e r <==> L.mem e lca \/ L.mem e s1))) 
                     (decreases %[lca;s1]) =
  match lca, s1 with
  |[],[] -> []
  |x::xs,_ -> if L.mem x s1 then concrete_merge1_g xs s1 else x::concrete_merge1_g xs s1
  |[],_ -> s1

let concrete_merge_g (lca:gset_st) (s1:gset_st) (s2:gset_st{concrete_merge_pre_g lca s1 s2})
  : (r:gset_st{(forall e. L.mem e r <==> L.mem e lca \/ L.mem e s1 \/ L.mem e s2)})=
  concrete_merge1_g s1 s2

// concrete merge pre-condition
let concrete_merge_pre lca a b : prop = 
  (forall k v. mem_kv k v lca ==> mem_kv k v a /\ mem_kv k v b) 

let rec concrete_merge1 (lca:concrete_st) (s1:concrete_st) (s2:concrete_st)
  : Pure concrete_st (requires concrete_merge_pre lca s1 s2)
                     (ensures (fun r -> (forall k. mem_k k r <==> mem_k k lca \/ mem_k k s1 \/ mem_k k s2) /\
                                     (forall k v. mem_kv k v r <==> mem_kv k v lca \/ mem_kv k v s1 \/ mem_kv k v s2)))
                     (decreases %[lca;s1; s2]) =
  match lca, s1, s2 with
  |[],[],[] -> []
  |(k,s)::xs,_,_ -> if mem_k k s1 && mem_k k s2 then
                    (k, concrete_merge_g s (get_set k s1) (get_set k s2))::concrete_merge1 xs (rem_k k s1) (rem_k k s2)
                  else if mem_k k s1 then
                    (k, concrete_merge_g s (get_set k s1) [])::concrete_merge1 xs (rem_k k s1) s2
                  else if mem_k k s2 then
                    (k, concrete_merge_g s [] (get_set k s2))::concrete_merge1 xs s1 (rem_k k s2)
                  else (k,s)::concrete_merge1 xs s1 s2
  |[],(k,s)::xs,_ -> if mem_k k s2 then (k, concrete_merge_g [] s (get_set k s2))::concrete_merge1 [] xs (rem_k k s2)
                   else (k,s)::concrete_merge1 [] xs s2
  |[],[],_ -> s2

let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2})
  : (r:concrete_st{(forall k. mem_k k r <==> mem_k k lca \/ mem_k k s1 \/ mem_k k s2) /\
                   (forall k v. mem_kv k v r <==> mem_kv k v lca \/ mem_kv k v s1 \/ mem_kv k v s2)})=
  concrete_merge1 lca s1 s2

#push-options "--z3rlimit 200"
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
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  lem_foldl init_st (ops_of s1);
  lem_inverse (ops_of lca) (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of (inverse_st s2));
  lem_foldl (v_of lca) (diff (ops_of (inverse_st s2)) (ops_of lca))
  
let linearizable_s1_0 (lca s1 s2:st)
  : Lemma 
      (requires is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                ops_of s1 = ops_of lca /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
      (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_s2_0 (lca s1 s2:st)
  : Lemma 
      (requires is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                ops_of s2 = ops_of lca /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
      (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let lem_do_op (a:concrete_st) (op:log_entry)
  : Lemma (requires concrete_do_pre a op)
          (ensures (forall k v. mem_kv k v (do a op) <==> mem_kv k v a \/ (k = key op /\ v = value op))) = ()

let lem_trans (a b c:concrete_st) (op:log_entry)
  : Lemma (requires (forall k v. mem_kv k v a <==> mem_kv k v b \/ (k = key op /\ v = value op)) /\
                    (forall k v. mem_kv k v b \/ (k = key op /\ v = value op) <==> mem_kv k v c))
          (ensures (forall k v. mem_kv k v a <==> mem_kv k v c)) = ()

let linearizable_s2_gt0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                   eq (concrete_merge (v_of lca) (v_of s1) (v_of s2))
                      (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_foldl init_st (ops_of s2); 
  assert (concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2); 
  assert (forall k. mem_k k (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               mem_k k (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) \/ (k = key last2));
  assert (forall k v. mem_kv k v (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                 mem_kv k v (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) \/ (k = key last2 /\ v = value last2));
  lem_do_op (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2;             
  assert (forall k v. mem_kv k v (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2) <==>
                 mem_kv k v (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) \/ (k = key last2 /\ v = value last2));
  lem_trans (concrete_merge (v_of lca) (v_of s1) (v_of s2)) (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) 
            (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2) last2;
  assert (forall k v. mem_kv k v (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                 mem_kv k v (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2));
  ()
  
let linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     (last (resolve_conflict last1 last2) = last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                           concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                     (last (resolve_conflict last1 last2) <> last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                           concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                      eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                      eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) =
  let _,last1 = un_snoc (ops_of s1) in
  let p2,last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  linearizable_s2_gt0 lca s1 s2

let convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ eq s1' (do s1 o) /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures eq (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1')) = ()
#pop-options 

