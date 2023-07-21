module App_do_pre_first
  
open FStar.Seq
open FStar.Ghost
open SeqUtils

#set-options "--query_stats"

// the concrete state type
val concrete_st : Type0

// init state
val init_st : concrete_st

// equivalence between 2 concrete states
val eq (a b:concrete_st) : Type0

val symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a)

val transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c)

val eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b)

// operation type
val app_op_t : eqtype

type timestamp_t = pos

type op_t = timestamp_t & app_op_t

type log = seq op_t

unfold
let ( ++ ) (l1 l2:log) = Seq.append l1 l2

unfold
let count_id (id:timestamp_t) (l:log) = count_assoc_fst id l

unfold
let mem_id (id:timestamp_t) (l:log) : bool =
  mem_assoc_fst id l
  
unfold
let distinct_ops (l:log) = distinct_assoc_fst l

type st0 = concrete_st & erased log
  
let v_of (s:st0) : concrete_st = fst s
let ops_of (s:st0) : GTot log = snd s

// concrete do pre-condition
val do_pre (_:concrete_st) (_:op_t) : prop

// apply an operation to a state
val do (s:concrete_st) (o:op_t{do_pre s o}) : concrete_st

val lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b /\ do_pre a op)
           (ensures do_pre b op /\ eq (do a op) (do b op))

let rec do_pre_prop (x:concrete_st) (l:log) : Tot prop (decreases length l) =
  match length l with
  |0 -> True
  |_ -> do_pre x (head l) /\ do_pre_prop (do x (head l)) (tail l)
  
// applying a log of operations to a concrete state
let rec apply_log (x:concrete_st) (l:log{do_pre_prop x l}) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |1 -> do x (head l)
  |_ -> apply_log (do x (head l)) (tail l)                   

// property of apply_log
let rec lem_apply_log (x:concrete_st) (l:log)
  : Lemma (requires do_pre_prop x l)
          (ensures (length l > 0 ==> do_pre_prop x (fst (un_snoc l)) /\
                           do_pre (apply_log x (fst (un_snoc l))) (last l) /\
                           (apply_log x l == do (apply_log x (fst (un_snoc l))) (last l))))
          (decreases length l) =
  match length l with
  |0 -> ()
  |1 -> ()
  |_ -> lem_apply_log (do x (head l)) (tail l)

type st1 = s:st0{do_pre_prop init_st (ops_of s) /\ (v_of s == apply_log init_st (ops_of s))}

let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  do_pre_prop init_st (ops_of s) /\ 
  (v_of s == apply_log init_st (ops_of s))

type st = s:st0{valid_st s}

type resolve_conflict_res =
  | First_then_second //consider both op1 & op2 but apply op1 at the end
  | Second_then_first //consider both op1 & op2 but apply op2 at the end
  | First //apply only op1

val resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res

// concrete merge pre-condition
val merge_pre (lca a b:concrete_st) : prop

// concrete merge operation
val concrete_merge (lca s1:concrete_st) (s2:concrete_st{merge_pre lca s1 s2}) : Tot concrete_st

let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{do_pre (v_of i) (last (ops_of s)) /\
               (v_of s == do (v_of i) (last (ops_of s))) /\
               (ops_of i = fst (un_snoc (ops_of s))) /\
               (ops_of s = snoc (ops_of i) (last (ops_of s))) /\
               is_prefix (ops_of i) (ops_of s) /\
               (forall id. mem_id id (ops_of i) <==> mem_id id (ops_of s) /\ id <> fst (last (ops_of s)))}) =
  lem_apply_log init_st (ops_of s);
  let p,_ = un_snoc (ops_of s) in
  let r = apply_log init_st p in
  let p, l = un_snoc (ops_of s) in
  let r = apply_log init_st p in
  lemma_split (ops_of s) (length (ops_of s) - 1); 
  lemma_append_count_assoc_fst p (snd (split (ops_of s) (length (ops_of s) - 1))); 
  distinct_invert_append p (snd (split (ops_of s) (length (ops_of s) - 1)));
  (r, hide p)

//currently present in App.fsti as Log MRDT needs it
let rec inverse_helper (s:concrete_st) (l':log) (op:op_t)
  : Lemma (requires do_pre_prop s l' /\ do_pre (apply_log s l') op)
          (ensures (let l = Seq.snoc l' op in 
                   do_pre_prop s l /\ 
                   (apply_log s l == do (apply_log s l') op)))
          (decreases length l') // [SMTPat (do_pre_prop s l' /\ do_pre (apply_log s l') op)] 
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |_ -> inverse_helper (do s (head l')) (tail l') op

//currently present in App.fsti as Log MRDT needs it
let rec split_prefix (s:concrete_st) (l:log) (a:log)
  : Lemma (requires is_prefix l a /\ do_pre_prop s a)
          (ensures do_pre_prop s l /\ do_pre_prop (apply_log s l) (diff a l) /\ 
                   (apply_log s a == apply_log (apply_log s l) (diff a l)) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) == (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |_ -> split_prefix (do s (head l)) (tail l) (tail a)

let consistent_branches (lca s1 s2:st1) =
  distinct_ops (ops_of lca) /\ distinct_ops (ops_of s1) /\ distinct_ops (ops_of s2) /\
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\ 
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))

let consistent_branches_s1_gt0 (lca s1 s2:st1) =
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca)

let consistent_branches_s2_gt0 (lca s1 s2:st1) =
  consistent_branches lca s1 s2 /\
  length (ops_of s2) > length (ops_of lca)

let consistent_branches_s1s2_gt0 (lca s1 s2:st1) =
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca) /\
  length (ops_of s2) > length (ops_of lca)

let do_st (s:st1) (o:op_t{do_pre (v_of s) o}) : st1 =
  inverse_helper init_st (ops_of s) o;
  split_prefix init_st (ops_of s) (snoc (ops_of s) o); 
  (do (v_of s) o, hide (snoc (ops_of s) o))

// Prove that merge is commutative
val merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures merge_pre (v_of lca) (v_of s2) (v_of s1) /\
                   (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) 

val linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))

val linearizable_s1_0''_base_do_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\ 
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    fst last2 > 0 /\
                    length (ops_of s2') > 0)
          (ensures do_pre (v_of (inverse_st s2')) last2)

val linearizable_s1_0''_base_merge_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\ 
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    fst last2 > 0 /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    length (ops_of s2') > 0 /\
                    do_pre (v_of (inverse_st s2')) last2)

          (ensures (let l' = inverse_st lca in
                    merge_pre (v_of l') (v_of l') (do (v_of l') last2)))

val linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    do_pre (v_of s2'') last2 /\ 
                    consistent_branches l' s1' (do_st s2'' last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    merge_pre (v_of l') (v_of s1') (do (v_of s2'') last2) /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))

val linearizable_s1_0''_do_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    ops_of s1 = ops_of lca /\                    
                    fst last2 > 0 /\
                    length (ops_of s2') > length (ops_of lca))
         
          (ensures do_pre (v_of (inverse_st s2')) last2)

val linearizable_s1_0''_merge_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    do_pre (v_of inv2) last2 /\
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2)))
         
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of (inverse_st s2')) last2))
                    
val linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    do_pre (v_of inv2) last2 /\
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of inv2) last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))

val linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))
          
val linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                      do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second_then_first? (resolve_conflict last1 last2) ==>
                      merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                      do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))                 

val linearizable_gt0_s2'_do_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2)) 
         
          (ensures (length (ops_of s2) > length (ops_of lca) ==> do_pre (v_of (inverse_st s2)) last2) /\
                   (length (ops_of s1) > length (ops_of lca) ==> do_pre (v_of (inverse_st s1)) last1))

val linearizable_gt0_s2'_merge_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) 
         
          (ensures (length (ops_of s1) > length (ops_of lca) /\ do_pre (v_of (inverse_st s1)) last1 ==>
                      merge_pre (v_of lca) (do (v_of (inverse_st s1)) last1) (do (v_of s2) last2)) /\
                   (length (ops_of s2) > length (ops_of lca) /\ do_pre (v_of (inverse_st s2)) last2 ==>
                      merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of (inverse_st s2)) last2)))
                   
val linearizable_gt0_s1'_do_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2)) 
          (ensures (length (ops_of s2) > length (ops_of lca) ==> do_pre (v_of (inverse_st s2)) last2) /\
                   (length (ops_of s1) > length (ops_of lca) ==> do_pre (v_of (inverse_st s1)) last1))

val linearizable_gt0_s1'_merge_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
          (ensures (length (ops_of s1) > length (ops_of lca) /\ do_pre (v_of (inverse_st s1)) last1 ==>
                      merge_pre (v_of lca) (do (v_of (inverse_st s1)) last1) (do (v_of s2) last2)) /\
                   (length (ops_of s2) > length (ops_of lca) /\ do_pre (v_of (inverse_st s2)) last2 ==>
                      merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of (inverse_st s2)) last2)))
                   
val linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
       
          (ensures (let s2' = inverse_st s2 in
                   do_pre (v_of s2') last2 /\
                   ((First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                     do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                     eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2') /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                     do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))))
                       
val linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
                           
          (ensures (let s1' = inverse_st s1 in
                   do_pre (v_of s1') last1 /\
                   ((ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1' (do_st s2 last2) /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1') (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                       
                   (merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   ((Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                
                   (merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\    
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))))

val linearizable_gt0_s1s2 (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\
                    consistent_branches lca (inverse_st s1) (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    First? (resolve_conflict last1 last2)) /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
                    do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) 
                       
val fts_merge_pre (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     First_then_second? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2))

val stf_merge_pre (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Second_then_first? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))

val first_merge_pre (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     First? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
          
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
val concrete_st_s : Type0

// init state 
val init_st_s : concrete_st_s

// apply an operation to a state 
val do_s (st_s:concrete_st_s) (_:op_t) : concrete_st_s

//equivalence relation between the concrete states of sequential type and MRDT
val eq_sm (st_s:concrete_st_s) (st:concrete_st) : prop

//initial states are equivalent
val initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st)

//equivalence between states of sequential type and MRDT at every operation
val do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st /\ do_pre st op)
          (ensures eq_sm (do_s st_s op) (do st op))

////////////////////////////////////////////////////////////////




(*val convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ eq s1' (do s1 o) /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures eq (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1'))*)
