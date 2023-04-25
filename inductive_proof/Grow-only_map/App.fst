module App

module L = FStar.List.Tot

#set-options "--query_stats"
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
type app_op_t = nat * nat

let key (op:op_t) = fst (snd op)

let value (op:op_t) = snd (snd op)

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

let do (s:concrete_st) (op:op_t) 
  : (r:concrete_st{(forall k. mem_k k r <==> mem_k k s \/ k = key op) /\
                   (forall k v. mem_kv k v r <==> mem_kv k v s \/ (k = key op /\ v = value op)) /\
                   (forall e. L.mem e r /\ fst e <> key op <==> L.mem e s /\ fst e <> key op)}) = 
  match s with
  |[] -> [key op, [value op]]
  |x::xs -> if mem_k (key op) s then add_v (key op) (value op) s 
             else  ((key op, [value op])::s)

let do_prop (s:concrete_st) (op:op_t) 
  : Lemma (ensures (forall k v. mem_kv k v (do s op) <==> mem_kv k v s \/ (k = key op /\ v = value op))) = ()

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) =
   do_prop a op;
   do_prop b op

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res = First_then_second

// concrete merge operation
let rec concrete_merge_g (lca s1 s2:gset_st)
  : Pure gset_st (requires true)
                     (ensures (fun r -> (forall e. L.mem e r <==> L.mem e lca \/ L.mem e s1 \/ L.mem e s2)))
                     (decreases %[lca;s1;s2]) =
  match lca, s1, s2 with
  |[],[],[] -> []
  |x::xs,_,_ -> if L.mem x s1 || L.mem x s2 then concrete_merge_g xs s1 s2 else x::concrete_merge_g xs s1 s2
  |[],x::xs,_ -> if L.mem x s2 then concrete_merge_g [] xs s2 else x::(concrete_merge_g [] xs s2)
  |[],[],x::xs -> x::concrete_merge_g [] [] xs

let rec rem_k (k:nat) (l:concrete_st)
    : Tot (r:concrete_st{(forall e. L.mem e r <==> L.mem e l /\ fst e <> k) /\
                         (forall k1 v1. mem_kv k1 v1 r <==> mem_kv k1 v1 l /\ k1 <> k)}) = 
  match l with
  |[] -> []
  |(x,s)::xs -> if k = x then xs else (x,s)::rem_k k xs

#push-options "--z3rlimit 500 --fuel 2 --ifuel 2"
let rec concrete_merge1 (lca:concrete_st) (s1:concrete_st) (s2:concrete_st)
  : Pure concrete_st (requires true)
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
#pop-options

// concrete merge operation
let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  concrete_merge1 lca s1 s2

let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    (exists l1 l2. apply_log (v_of lca) l1 == (v_of s1) /\ apply_log (v_of lca) l2 == (v_of s2)))
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = ()
                       
let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    consistent_branches l' s1' s2'' /\
                    is_prefix (ops_of l') (snoc (ops_of s2'') last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let inv2 = inverse_st s2' in
                    consistent_branches lca s1 inv2 /\
                    is_prefix (ops_of lca) (snoc (ops_of inv2) last2) /\
                    (exists l2. do (v_of inv2) last2 == apply_log (v_of lca) l2) /\
                    (exists l2. do (v_of s2') last2 == apply_log (v_of lca) l2) /\                    
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = 
  do_prop (v_of s2') last2
          
let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires (exists l1. v_of s1 == apply_log (v_of lca) l1) /\
                    (exists l2. v_of s2 == apply_log (v_of lca) l2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)))
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = 
  do_prop (v_of s1) last1;
  do_prop (v_of s2) last2

#push-options "--z3rlimit 50"
let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (let s2' = inverse_st s2 in
                    (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2)) /\
                    (exists l2. (v_of s2' == apply_log (v_of lca) l2)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    consistent_branches lca s1 s2'))
       
          (ensures (let s2' = inverse_st s2 in
                   ((First_then_second? (resolve_conflict last1 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = 
  do_prop (v_of s1) last1;
  do_prop (v_of s2) last2
                       
let linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches_s1_gt0 lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (let s1' = inverse_st s1 in
                    (exists l1. (do (v_of s1') last1 == apply_log (v_of lca) l1)) /\
                    (exists l1. (v_of s1' == apply_log (v_of lca) l1)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    consistent_branches lca s1' s2))
        
          (ensures (let s1' = inverse_st s1 in
                   ((ops_of s2 = ops_of lca /\
                   First_then_second? (resolve_conflict last1 last2) /\
                   eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = 
  do_prop (v_of s1) last1;
  do_prop (v_of s2) last2
#pop-options

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = concrete_st

// init state 
let init_st_s = []

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = 
  do s op

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) 
  = do_prop st op
  
////////////////////////////////////////////////////////////////
