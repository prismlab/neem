module App

open SeqUtils

#set-options "--query_stats"
// the concrete state type
// It is a sequence of pairs of timestamp and message.
// As the sequence is sorted based on timestamps we ignore the message
type concrete_st = seq (pos & string)

// init state
let init_st = empty

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  a == b

// few properties of equivalence relation
let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b) = ()

// operation type
// (the only operation is write a message)
type app_op_t:eqtype = string

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
  cons (fst op, snd op) s 

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()
           
//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if lt (fst y) (fst x) then First_then_second else Second_then_first

//#push-options "--z3rlimit 50"
let rec union_s (l1 l2:concrete_st) 
  : Tot (u:concrete_st{forall e. mem e u <==> mem e l1 \/ mem e l2}) 
  (decreases %[length l1; length l2]) =
  match length l1, length l2 with
  |0, 0 -> empty
  |0, _ -> l2
  |_, 0 -> l1
  |_, _ ->  if (fst (head l1) >= fst (head l2) )
             then (mem_cons (head l1) (union_s (tail l1) l2);
                   cons (head l1) (union_s (tail l1) l2))
             else (mem_cons (head l2) (union_s l1 (tail l2));
                   cons (head l2) (union_s l1 (tail l2)))

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (length l = 0 ==> (apply_log s l = s)) /\
                   (is_suffix s (apply_log s l)) /\
                   (length l > 0 ==> length (apply_log s l) > length s) /\
                   (forall id. mem_assoc_fst id (apply_log s l) <==> mem_assoc_fst id s \/ mem_id id l))
          (decreases length l)
          [SMTPat (is_suffix s (apply_log s l))]
  = match length l with
    |0 -> ()
    |_ -> assert (is_suffix s (do s (head l)));
         lem_foldl (do s (head l)) (tail l)

let lem_foldl_forall (s:concrete_st) 
  : Lemma (ensures (forall l. (is_suffix s (apply_log s l)))) = ()

let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun m -> (lca == s1 ==> m == s2) /\ (lca == s2 ==> m == s1))) =
  let la = diff_suf s1 lca in
  let lb = diff_suf s2 lca in
  let u = union_s la lb in 
  lemma_mem_append u lca;
  Seq.append u lca

let rec lem_union_comm (l1 l2:concrete_st) 
  : Lemma (requires (forall id. mem_assoc_fst id l1 ==> not (mem_assoc_fst id l2)))
          (ensures eq (union_s l1 l2) (union_s l2 l1)) 
          (decreases %[length l1; length l2]) =
  match length l1, length l2 with
  |0, 0 -> ()
  |0, _ -> ()
  |_, 0 -> ()
  |_, _ ->  if (fst (head l1) > fst (head l2) )
             then (mem_cons (head l1) (union_s (tail l1) l2);
                   lem_union_comm (tail l1) l2)
             else (mem_cons (head l2) (union_s l1 (tail l2));
                   lem_union_comm l1 (tail l2))

let do_is_unique (s:concrete_st) (op:op_t) 
  : Lemma (requires distinct_assoc_fst s /\ (not (mem_assoc_fst (fst op) s)))
          (ensures distinct_assoc_fst (do s op) /\ length (do s op) = length s + 1) =
  assert (distinct_assoc_fst s);
  assert (distinct_assoc_fst (create 1 (fst op, snd op))); 
  distinct_append (create 1 (fst op, snd op)) s

#push-options "--z3rlimit 100"
let rec lem_foldl_uni (s:concrete_st) (l:log)
  : Lemma (requires distinct_assoc_fst s /\ distinct_ops l /\
                    (forall id. mem_assoc_fst id s ==> not (mem_id id l)))
          (ensures distinct_assoc_fst (apply_log s l) /\ length (apply_log s l) = length s + length l)
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> mem_cons (head l) (tail l);
       distinct_invert_append (create 1 (head l)) (tail l);
       do_is_unique s (head l); 
       lemma_append_count_assoc_fst (create 1 (fst (head l), snd (head l))) s;
       lem_foldl_uni (do s (head l)) (tail l)
#pop-options

let valid_is_unique (s:st0) 
  : Lemma (requires distinct_ops (ops_of s) /\ v_of s == apply_log init_st (ops_of s))
          (ensures distinct_assoc_fst (v_of s) /\ length (v_of s) = length (ops_of s)) =
  lem_foldl_uni init_st (ops_of s)

let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = 
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  let la = diff_suf (v_of s1) (v_of lca) in
  let lb = diff_suf (v_of s2) (v_of lca) in
  let da = (diff (ops_of s1) (ops_of lca)) in
  let db = (diff (ops_of s2) (ops_of lca)) in
  let u1 = union_s la lb in 
  let u2 = union_s lb la in
  valid_is_unique lca;
  valid_is_unique s1;
  valid_is_unique s2;
  lem_diff_suf_uni (v_of s1) (v_of lca);
  lem_diff_suf_uni (v_of s2) (v_of lca); 
  assert (forall id. mem_assoc_fst id (v_of lca) <==> mem_id id (ops_of lca));
  assert (forall id. mem_assoc_fst id (v_of s1) <==> mem_assoc_fst id (v_of lca) \/ mem_id id da);
  assert (forall id. mem_assoc_fst id (v_of s2) <==> mem_assoc_fst id (v_of lca) \/ mem_id id db);
  assert (forall id. mem_assoc_fst id (v_of s1) <==> mem_assoc_fst id (v_of lca) \/ mem_assoc_fst id (diff_suf (v_of s1) (v_of lca)));
  assert (forall id. mem_assoc_fst id (v_of s2) <==> mem_assoc_fst id (v_of lca) \/ mem_assoc_fst id (diff_suf (v_of s2) (v_of lca)));
  assert (forall id. (mem_assoc_fst id (v_of s1) /\ not (mem_assoc_fst id (v_of lca))) <==> (mem_assoc_fst id la)); 
  assert (forall id. (mem_assoc_fst id (v_of s2) /\ not (mem_assoc_fst id (v_of lca))) <==> (mem_assoc_fst id lb));
  lem_diff (ops_of s1) (ops_of lca);
  lem_diff (ops_of s2) (ops_of lca);
  lem_foldl_uni (v_of lca) da;
  lem_foldl_uni (v_of lca) db;
  assert (forall id. mem_assoc_fst id la <==> mem_id id da);
  assert (forall id. mem_assoc_fst id lb <==> mem_id id db);
  assert (forall id. mem_assoc_fst id la <==> mem_id id da); 
  assert (forall id. mem_assoc_fst id lb <==> mem_id id db);
  assert (forall id. mem_id id da ==> not (mem_id id db));
  lem_not_mem_id la lb da db; 
  assert (forall id. mem_assoc_fst id la ==> not (mem_assoc_fst id lb));  
  lem_union_comm la lb;
  assert (union_s la lb == union_s lb la);
  ()

let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0)
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    consistent_branches l' s1' (do_st s2'' last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

#push-options "--z3rlimit 10"
let linearizable_gt0_base_last1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  let l1 = (fst last1, snd last1) in
  let l2 = (fst last2, snd last2) in
  assert (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 ==
          cons l1 (cons l2 (v_of lca)));
  lemma_mem_append (create 1 l2) (v_of lca);
  append_assoc (create 1 l1) (create 1 l2) (v_of lca);
  assert (cons l1 (cons l2 (v_of lca)) == Seq.append (cons l1 (cons l2 empty)) (v_of lca));
  ()

let linearizable_gt0_base_last2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  let l1 = (fst last1, snd last1) in
  let l2 = (fst last2, snd last2) in
  assert (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 ==
          cons l2 (cons l1 (v_of lca)));
  lemma_mem_append (create 1 l1) (v_of lca);
  append_assoc (create 1 l2) (create 1 l1) (v_of lca);
  assert (cons l2 (cons l1 (v_of lca)) == Seq.append (cons l2 (cons l1 empty)) (v_of lca));
  ()
#pop-options

let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2)
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second_then_first? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = 
  if First_then_second? (resolve_conflict last1 last2) then
    linearizable_gt0_base_last1 lca s1 s2 last1 last2
  else linearizable_gt0_base_last2 lca s1 s2 last1 last2

let lem_unionb (a b:concrete_st)
  : Lemma (requires length a > 0 /\ length b > 0 /\
                    lt (fst (head a)) (fst (head b)))
          (ensures union_s a b == cons (fst (head b), snd (head b)) (union_s a (tail b))) = ()

let lem_uniona (a b:concrete_st)
  : Lemma (requires length a > 0 /\ length b > 0 /\
                    lt (fst (head b)) (fst (head a)))
          (ensures union_s a b == cons (fst (head a), snd (head a)) (union_s (tail a) b)) = ()

#push-options "--z3rlimit 50"
let linearizable_gt0_ind_c2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  let s1v = do (v_of s1) last1 in
  let s2v = do (v_of s2) last2 in
  let da = (diff_suf s1v (v_of lca)) in
  let db = (diff_suf s2v (v_of lca)) in
  let db' = (diff_suf (v_of s2) (v_of lca)) in
  let da' = (diff_suf (v_of s1) (v_of lca)) in
  let l1 = (fst last1, snd last1) in
  let l2 = (fst last2, snd last2) in 
  lemma_tl l2 (v_of s2);
  lem_diff_suf s2v (v_of lca); 
  lemma_tl l1 (v_of s1);
  lem_diff_suf s1v (v_of lca);  
  assert (lt (fst last1) (fst (last2))); 
  assert (lt (fst (head da)) (fst (head db))); 
  lem_unionb da db;
  append_assoc (create 1 l2) (union_s da db') (v_of lca)
  
let linearizable_gt0_ind1_c11 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2))
        
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  let s1v = do (v_of s1) last1 in
  let s2v = do (v_of s2) last2 in
  let da = (diff_suf s1v (v_of lca)) in
  let db = (diff_suf s2v (v_of lca)) in
  let da' = (diff_suf (v_of s1) (v_of lca)) in
  let db' = (diff_suf (v_of s2) (v_of lca)) in
  let l1 = (fst last1, snd last1) in
  let l2 = (fst last2, snd last2) in
  lemma_tl l1 (v_of s1);
  lem_diff_suf s1v (v_of lca);
  lemma_tl l2 (v_of s2);
  lem_diff_suf s2v (v_of lca);
  assert (lt (fst last2) (fst (last1)));
  assert (lt (fst (head db)) (fst (head da)));
  lem_uniona da db; 
  append_assoc (create 1 l1) (union_s da' db) (v_of lca)
#pop-options

let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2)
       
          (ensures (let s2' = inverse_st s2 in
                   ((First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()

let linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2)
                           
          (ensures (let s1' = inverse_st s1 in
                   ((ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1' (do_st s2 last2) /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                       
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   ((Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                       
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = seq string

// init state 
let init_st_s = empty

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = cons (snd op) s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  length st_s = length st /\
  (forall (i:nat). i < length st_s ==> index st_s i == snd (index st i))

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()
  
////////////////////////////////////////////////////////////////
