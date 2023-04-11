module App

#set-options "--query_stats"
// the concrete state type
// It is a sequence of pairs of timestamp and message.
// As the sequence is sorted based on timestamps we ignore the message
type concrete_st = seq nat

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
// (the only operation is append, so unit is fine)
type app_op_t:eqtype = unit

let is_prefix_s (p l:concrete_st) : Tot prop =
  Seq.length l >= Seq.length p /\ Seq.equal p (Seq.slice l 0 (Seq.length p))

let is_suffix_s (s l:concrete_st) : Tot prop =
  Seq.length l >= Seq.length s /\ Seq.equal s (Seq.slice l (Seq.length l - Seq.length s) (Seq.length l))

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
  cons (fst op) s 

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()
           
//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if lt (fst y) (fst x) then First else Second

let rec union_s (l1 l2:concrete_st) 
  : Tot (u:concrete_st{forall e. mem e u <==> mem e l1 \/ mem e l2}) 
  (decreases %[length l1; length l2]) =
  match length l1, length l2 with
  |0, 0 -> empty
  |0, _ -> l2
  |_, 0 -> l1
  |_, _ ->  if (head l1 >= head l2) 
             then (mem_cons (head l1) (union_s (tail l1) l2);
                   cons (head l1) (union_s (tail l1) l2))
             else (mem_cons (head l2) (union_s l1 (tail l2));
                   cons (head l2) (union_s l1 (tail l2)))

let diff_s (s1:concrete_st) (lca:concrete_st{is_suffix_s lca s1}) 
  : Tot (d:concrete_st{s1 == Seq.append d lca}) =
  let s = fst (split s1 (length s1 - length lca)) in
  lemma_split s1 (length s1 - length lca);
  lemma_mem_append s lca;
  s

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (length l = 0 ==> (apply_log s l = s)) /\
                   (is_suffix_s s (apply_log s l)) /\
                   (length l > 0 ==> length (apply_log s l) > length s))
          (decreases length l)
          [SMTPat (is_suffix_s s (apply_log s l))]
  = match length l with
    |0 -> ()
    |1 -> ()
    |_ -> assert (is_suffix_s s (do s (head l)));
         lem_foldl (do s (head l)) (tail l)

let lem_foldl_forall (s:concrete_st) 
  : Lemma (ensures (forall l. (is_suffix_s s (apply_log s l)))) = ()

let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  //lem_foldl_forall lca;
  let la = diff_s s1 lca in
  let lb = diff_s s2 lca in
  let u = union_s la lb in 
  lemma_mem_append u lca;
  Seq.append u lca

let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

#push-options "--z3rlimit 50"
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
#pop-options

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
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires (exists l1. v_of s1 == apply_log (v_of lca) l1) /\
                    (exists l2. v_of s2 == apply_log (v_of lca) l2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()
          
let linearizable_s2_0''_base_base (lca s1' s2:st) (last1:op_t)
  : Lemma (requires consistent_branches lca s1' s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()

#push-options "--z3rlimit 50"
let linearizable_s2_0''_base_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires consistent_branches lca s1' s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let l' = inverse_st lca in
                    let s1'' = inverse_st s1' in
                    let s2' = inverse_st s2 in
                    consistent_branches l' s1'' s2' /\
                    is_prefix (ops_of l') (snoc (ops_of s1'') last1) /\
                    ops_of s1'' = ops_of l' /\ ops_of s2' = ops_of l' /\
                    eq (do (v_of s1'') last1) (concrete_merge (v_of l') (do (v_of s1'') last1) (v_of s2'))))

          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()
#pop-options

let linearizable_s2_0''_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires consistent_branches_s1_gt0 lca s1' s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s2 = ops_of lca /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let inv1 = inverse_st s1' in
                    consistent_branches lca inv1 s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of inv1) last1) /\
                    (exists l1. (do (v_of inv1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l1. (do (v_of s1') last1 == apply_log (v_of lca) l1)) /\
                    eq (do (v_of inv1) last1) (concrete_merge (v_of lca) (do (v_of inv1) last1) (v_of s2))))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()

#push-options "--z3rlimit 50"
let linearizable_gt0_base_last1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    First? (resolve_conflict last1 last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  assert (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 ==
          cons (fst last1) (cons (fst last2) (v_of lca)));
  lemma_mem_append (create 1 (fst last2)) (v_of lca);
  append_assoc (create 1 (fst last1)) (create 1 (fst last2)) (v_of lca);
  assert (cons (fst last1) (cons (fst last2) (v_of lca)) ==
          Seq.append (cons (fst last1) (cons (fst last2) empty)) (v_of lca));
  ()

let linearizable_gt0_base_last2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    Second? (resolve_conflict last1 last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  assert (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 ==
          cons (fst last2) (cons (fst last1) (v_of lca)));
  lemma_mem_append (create 1 (fst last1)) (v_of lca);
  append_assoc (create 1 (fst last2)) (create 1 (fst last1)) (v_of lca);
  assert (cons (fst last2) (cons (fst last1) (v_of lca)) ==
          Seq.append (cons (fst last2) (cons (fst last1) empty)) (v_of lca));
  ()
  
let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)))
         
          (ensures (First? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) =
  if First? (resolve_conflict last1 last2) then
    linearizable_gt0_base_last1 lca s1 s2 last1 last2
  else linearizable_gt0_base_last2 lca s1 s2 last1 last2

(*let lem_diff (s1 l:log)
  : Lemma (requires distinct_ops s1 /\ is_prefix l s1)
          (ensures distinct_ops (diff s1 l) /\ (forall id. mem_id id (diff s1 l) <==> mem_id id s1 /\ not (mem_id id l)) /\
                   (forall id. mem_id id s1 <==> mem_id id l \/ mem_id id (diff s1 l)) /\
                   (Seq.length s1 > Seq.length l ==> (last s1 == last (diff s1 l) /\ Seq.length (diff s1 l) > 0) /\
                     (let _, l1 = un_snoc s1 in
                      let _, ld = un_snoc (diff s1 l) in
                      l1 = ld) /\
                     (let s1',lastop = un_snoc s1 in 
                       diff s1' l == fst (un_snoc (diff s1 l)))))
  = let s = snd (split s1 (length l)) in
    lemma_split s1 (length l);
    lemma_append_count_assoc_fst l s

let rec split_prefix (s:concrete_st) (l:log) (a:log)
  : Lemma (requires is_prefix l a)
          (ensures (apply_log s a == apply_log (apply_log s l) (diff a l)) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) == (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |1 -> ()
    |_ -> split_prefix (do s (head l)) (tail l) (tail a)*)

let lem_diff_s (s1 l:concrete_st)
  : Lemma (requires is_suffix_s l s1)
          (ensures (Seq.length s1 > Seq.length l ==> (head s1 == head (diff_s s1 l) /\ Seq.length (diff_s s1 l) > 0) /\
                     (let h1 = head s1 in
                      let hd = head (diff_s s1 l) in
                      h1 = hd) /\
                     (let s1' = tail s1 in 
                       is_suffix_s l s1' /\
                       diff_s s1' l == tail (diff_s s1 l))))
  = let s = fst (split s1 (length s1 - length l)) in
    lemma_split s1 (length s1 - length l);
    lemma_mem_append s l

let lem_unionb (a b:concrete_st)
  : Lemma (requires length a > 0 /\ length b > 0 /\
                    head b > head a)
          (ensures union_s a b == cons (head b) (union_s a (tail b))) = ()

let lem_uniona (a b:concrete_st)
  : Lemma (requires length a > 0 /\ length b > 0 /\
                    head a > head b)
          (ensures union_s a b == cons (head a) (union_s (tail a) b)) = ()

#push-options "--z3rlimit 20"
let linearizable_gt0_ind_c2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    ops_of s1 = ops_of lca /\
                    Second? (resolve_conflict last1 last2) /\
                    (//let s2' = inverse_st s2 in
                  //  (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2)) /\
                   // (exists l2. (v_of s2' == apply_log (v_of lca) l2)) /\
                  //  (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2))
                    (*consistent_branches lca s1 s2' /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)*)))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  assert (fst last2 > fst last1); 
  let s1v = do (v_of s1) last1 in
  let s2v = do (v_of s2) last2 in
  let da = (diff_s s1v (v_of lca)) in
  let db = (diff_s s2v (v_of lca)) in
  let db' = (diff_s (v_of s2) (v_of lca)) in
  let s1op = (snoc (ops_of s1) last1) in
  let s2op = (snoc (ops_of s2) last2) in
  lem_diff s1op (ops_of lca);
  split_prefix init_st (ops_of lca) s1op;
  lem_foldl (v_of lca) (diff s1op (ops_of lca));
  assert (length da > 0);
  lem_diff s2op (ops_of lca);
  split_prefix init_st (ops_of lca) s2op;
  lem_foldl (v_of lca) (diff s2op (ops_of lca));
  assert (length db > 0);
  
  assert (s1v == cons (fst last1) (v_of s1));
  assert (s2v == cons (fst last2) (v_of s2));
  lemma_tl (fst last2) (v_of s2);
  assert (v_of s2 == tail s2v);
  assert (concrete_merge (v_of lca) s1v s2v == Seq.append (union_s da db) (v_of lca)); 
  lem_diff_s s2v (v_of lca);
  assert (head db = fst last2); 
  lem_diff_s s1v (v_of lca);
  assert (head da = fst last1); 
  assert (head db > head da); 
  lem_unionb da db; 
  assert (union_s da db == cons (fst last2) (union_s da db')); 
  assert (do (concrete_merge (v_of lca) s1v (v_of s2)) last2 ==
          cons (fst last2) (Seq.append (union_s da db') (v_of lca)));
  append_assoc (create 1 (fst last2)) (union_s da db') (v_of lca)

#push-options "--z3rlimit 100"
let linearizable_gt0_ind_c1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    First? (resolve_conflict last1 last2) /\
                    (let s2' = inverse_st s2 in
                    (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2)) /\
                    (exists l2. (v_of s2' == apply_log (v_of lca) l2)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    (consistent_branches lca s1 s2' /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)))))
       
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  assert (fst last1 > fst last2); 
  let s1v = do (v_of s1) last1 in
  let s2v = do (v_of s2) last2 in
  let da = (diff_s s1v (v_of lca)) in
  let db = (diff_s s2v (v_of lca)) in
  let da' = (diff_s (v_of s1) (v_of lca)) in
  let s1op = (snoc (ops_of s1) last1) in
  let s2op = (snoc (ops_of s2) last2) in
  lem_diff s2op (ops_of lca); 
  split_prefix init_st (ops_of lca) s2op;
  lem_foldl (v_of lca) (diff s2op (ops_of lca));
  assert (length db > 0);
  lem_diff s1op (ops_of lca);
  split_prefix init_st (ops_of lca) s1op;
  lem_foldl (v_of lca) (diff s1op (ops_of lca));
  assert (length da > 0); 
  
  assert (s1v == cons (fst last1) (v_of s1));
  assert (s2v == cons (fst last2) (v_of s2));
  lemma_tl (fst last1) (v_of s1);
  assert (v_of s1 == tail s1v);
  assert (concrete_merge (v_of lca) s1v s2v == Seq.append (union_s da db) (v_of lca)); 
  lem_diff_s s2v (v_of lca);
  assert (head db = fst last2); 
  lem_diff_s s1v (v_of lca);
  assert (head da = fst last1); 
  assert (head da > head db); 
  lem_uniona da db; 
  assert (union_s da db == cons (fst last1) (union_s da' db)); 
  assert (do (concrete_merge (v_of lca) (v_of s1) s2v) last1 ==
          cons (fst last1) (Seq.append (union_s da' db) (v_of lca)));
  append_assoc (create 1 (fst last1)) (union_s da' db) (v_of lca)
                        
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
                   ((First? (resolve_conflict last1 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    Second? (resolve_conflict last1 last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()
  
let linearizable_gt0_ind1_c2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches_s1_gt0 lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\ 
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    Second? (resolve_conflict last1 last2) /\
                    (let s1' = inverse_st s1 in
                    (exists l1. (do (v_of s1') last1 == apply_log (v_of lca) l1)) /\
                    (exists l1. (v_of s1' == apply_log (v_of lca) l1)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    consistent_branches lca s1' s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
        
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 
          [SMTPat (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] =
  assert (fst last2 > fst last1); 
  let s1v = do (v_of s1) last1 in
  let s2v = do (v_of s2) last2 in
  let da = (diff_s s1v (v_of lca)) in
  let db = (diff_s s2v (v_of lca)) in
  let db' = (diff_s (v_of s2) (v_of lca)) in
  let s1op = (snoc (ops_of s1) last1) in
  let s2op = (snoc (ops_of s2) last2) in
  split_prefix init_st (ops_of lca) s1op;
  lem_foldl (v_of lca) (diff s1op (ops_of lca));
  assert (length da > 0);
  lem_diff s2op (ops_of lca);
  split_prefix init_st (ops_of lca) s2op;
  lem_foldl (v_of lca) (diff s2op (ops_of lca));
  assert (length db > 0);
  
  assert (s1v == cons (fst last1) (v_of s1));
  assert (s2v == cons (fst last2) (v_of s2));
  lemma_tl (fst last2) (v_of s2);
  assert (v_of s2 == tail s2v); 
  assert (concrete_merge (v_of lca) s1v s2v == Seq.append (union_s da db) (v_of lca)); 
  lem_diff_s s2v (v_of lca);
  assert (head db = fst last2); 
  lem_diff_s s1v (v_of lca);
  assert (head da = fst last1); 
  assert (head db > head da); 
  lem_unionb da db; 
  assert (union_s da db == cons (fst last2) (union_s da db')); 
  assert (do (concrete_merge (v_of lca) s1v (v_of s2)) last2 ==
          cons (fst last2) (Seq.append (union_s da db') (v_of lca)));
  append_assoc (create 1 (fst last2)) (union_s da db') (v_of lca)

let linearizable_gt0_ind1_c1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches_s1_gt0 lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\ 
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    ops_of s2 = ops_of lca /\
                    First? (resolve_conflict last1 last2) /\
                    (//let s1' = inverse_st s1 in
                   // (exists l1. (do (v_of s1') last1 == apply_log (v_of lca) l1)) /\
                   // (exists l1. (v_of s1' == apply_log (v_of lca) l1)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) 
                   // (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    (*consistent_branches lca s1' s2 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)*)))
        
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  assert (fst last1 > fst last2); 
  let s1v = do (v_of s1) last1 in
  let s2v = do (v_of s2) last2 in
  let da = (diff_s s1v (v_of lca)) in
  let db = (diff_s s2v (v_of lca)) in
  let da' = (diff_s (v_of s1) (v_of lca)) in
  let s1op = (snoc (ops_of s1) last1) in
  let s2op = (snoc (ops_of s2) last2) in
  lem_diff s2op (ops_of lca); 
  split_prefix init_st (ops_of lca) s2op;
  lem_foldl (v_of lca) (diff s2op (ops_of lca));
  assert (length db > 0); 
  lem_diff s1op (ops_of lca);
  split_prefix init_st (ops_of lca) s1op;
  lem_foldl (v_of lca) (diff s1op (ops_of lca));
  assert (length da > 0);
   
  assert (s1v == cons (fst last1) (v_of s1));
  assert (s2v == cons (fst last2) (v_of s2));
  lemma_tl (fst last1) (v_of s1);
  assert (v_of s1 == tail s1v);
  assert (concrete_merge (v_of lca) s1v s2v == Seq.append (union_s da db) (v_of lca)); 
  lem_diff_s s2v (v_of lca);
  assert (head db = fst last2); 
  lem_diff_s s1v (v_of lca);
  assert (head da = fst last1); 
  assert (head da > head db); 
  lem_uniona da db; 
  assert (union_s da db == cons (fst last1) (union_s da' db)); 
  assert (do (concrete_merge (v_of lca) (v_of s1) s2v) last1 ==
          cons (fst last1) (Seq.append (union_s da' db) (v_of lca)));
  append_assoc (create 1 (fst last1)) (union_s da' db) (v_of lca)
                       
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
                   First? (resolve_conflict last1 last2) /\
                   eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   ((Second? (resolve_conflict last1 last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = seq nat

// init state 
let init_st_s = empty

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = cons (fst op) s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) 
  = ()

////////////////////////////////////////////////////////////////

(*let unique_st (s:concrete_st) = forall e.{:pattern count e s} count e s <= 1

let concrete_st_u = s:concrete_st{unique_st s} 

let distinct_append (a b:concrete_st)
  : Lemma (requires unique_st a /\ unique_st b /\
                    (forall e. mem e a ==> not (mem e b)))
          (ensures (unique_st (Seq.append a b)) /\
                   (forall e. mem e (Seq.append a b) <==> mem e a \/ mem e b)) =
  lemma_append_count a b
  
let rec apply_unique_st (s:concrete_st_u) (l:log)
  : Lemma (requires distinct_ops l /\ (forall id. mem_id id l ==> not (mem id s)))
          (ensures unique_st (apply_log s l))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> distinct_append (create 1 (fst (head l))) s;
       assert (unique_st (do s (head l)));
       mem_cons (fst (head l)) s; // (forall e. mem e (do s (head l)) ==> not (mem_id e (tail l)));
       mem_cons (head l) (tail l);
       distinct_invert_append (create 1 (head l)) (tail l); // distinct_ops (tail l)
       apply_unique_st (do s (head l)) (tail l)

let st_is_unique (lca:st) 
  : Lemma (ensures unique_st (v_of lca)) =
  apply_unique_st init_st (ops_of lca)*)

(*
#push-options "--z3rlimit 20"
let linearizable_gt0_s2 (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    Second? (resolve_conflict last1 last2) /\
                    (exists l2. (v_of (inverse_st s2) == apply_log (v_of lca) l2)) /\
                    (exists l2. (v_of s2) == apply_log (v_of lca) l2) /\
                    (exists l1. (v_of s1) == apply_log (v_of lca) l1)))
          (ensures (let pre2, last2 = un_snoc (ops_of s2) in                   
                   eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  assert (fst last2 > fst last1);
  let s1' = inverse_st s1 in
  let s2' = inverse_st s2 in
  let da = (diff_s (v_of s1) (v_of lca)) in
  let db = (diff_s (v_of s2) (v_of lca)) in
  let db' = (diff_s (v_of s2') (v_of lca)) in
  lem_diff (ops_of s1) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  assert (length (diff_s (v_of s1) (v_of lca)) > 0);
  lem_diff (ops_of s2) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  assert (length (diff_s (v_of s2) (v_of lca)) > 0); 
  assert (v_of s1 == cons (fst last1) (v_of s1'));
  assert (v_of s2 == cons (fst last2) (v_of s2'));
  lemma_tl (fst last2) (v_of s2');
  assert (v_of s2' == tail (v_of s2)); 
  assert (concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
          Seq.append (union_s da db) (v_of lca)); 
  lem_diff_s (v_of s2) (v_of lca);
  assert (head db = fst last2); 
  lem_diff_s (v_of s1) (v_of lca);
  assert (head da = fst last1); 
  assert (head db > head da); 
  lem_unionb da db; 
  assert (union_s da db == cons (fst last2) (union_s da db')); 
  assert (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 ==
          cons (fst last2) (Seq.append (union_s da db') (v_of lca)));
  append_assoc (create 1 (fst last2)) (union_s da db') (v_of lca)

let linearizable_gt0_s1 (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    First? (resolve_conflict last1 last2) /\
                    (exists l1. (v_of (inverse_st s1) == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2) == apply_log (v_of lca) l2) /\
                    (exists l1. (v_of s1) == apply_log (v_of lca) l1)))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  assert (fst last1 > fst last2);
  let s1' = inverse_st s1 in
  let s2' = inverse_st s2 in
  let da = (diff_s (v_of s1) (v_of lca)) in
  let db = (diff_s (v_of s2) (v_of lca)) in
  let da' = (diff_s (v_of s1') (v_of lca)) in
  lem_diff (ops_of s1) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  assert (length (diff_s (v_of s1) (v_of lca)) > 0);
  lem_diff (ops_of s2) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  assert (length (diff_s (v_of s2) (v_of lca)) > 0); 
  assert (v_of s1 == cons (fst last1) (v_of s1'));
  assert (v_of s2 == cons (fst last2) (v_of s2'));
  lemma_tl (fst last1) (v_of s1');
  assert (v_of s1' == tail (v_of s1)); 
  assert (concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
          Seq.append (union_s da db) (v_of lca)); 
  lem_diff_s (v_of s2) (v_of lca);
  assert (head db = fst last2); 
  lem_diff_s (v_of s1) (v_of lca);
  assert (head da = fst last1); 
  assert (head db < head da); 
  lem_uniona da db; 
  assert (union_s da db == cons (fst last1) (union_s da' db)); 
  assert (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 ==
          cons (fst last1) (Seq.append (union_s da' db) (v_of lca)));
  append_assoc (create 1 (fst last1)) (union_s da' db) (v_of lca)
#pop-options

*)
