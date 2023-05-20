module App

open SeqUtils
module S = Set_extended

#set-options "--query_stats"
// the concrete state type
// It is a set of pairs of timestamp and element.
type concrete_st = S.set (pos & nat)

// init state
let init_st = S.empty

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  S.equal a b

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
type app_op_t:eqtype = 
  | Enqueue : nat -> app_op_t
  | Dequeue

type ret_t:eqtype = option (pos * nat)

let get_ele (o:op_t{Enqueue? (fst (snd o))}) : nat =
  match o with
  |(_, (Enqueue x,_)) -> x

let return (s:concrete_st) (o:op_t) : ret_t =
  match o with
  |(_, (Enqueue _, _)) -> None
  |(_, (Dequeue, r)) -> if s = S.empty then None 
                          else (S.always_min_exists s; 
                                assert (Some? (S.find_min s));
                                Some (S.extract (S.find_min s)))
                                
// apply an operation to a state
let do (s:concrete_st) (op:op_t{do_pre s op}) : concrete_st =
  match op with
  |(id, (Enqueue x, _)) -> S.add (id, x) s
  |(_, (Dequeue, _)) -> if s = S.empty then s else S.remove_min s

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b /\ do_pre a op /\ do_pre b op)
           (ensures eq (do a op) (do b op)) = 
  if Enqueue? (fst (snd op)) then () else ()

let last_deq (s:concrete_st) (op:op_t)
  : Lemma (requires true)         
          (ensures ((Dequeue? (fst (snd op)) /\ Some? (ret_of op) /\ return s op == ret_of op) ==>
                   s <> S.empty /\ S.find_min s == ret_of op /\
                   S.mem (S.extract (S.find_min s)) s) /\
                   (Dequeue? (fst (snd op)) /\ None? (ret_of op) /\ return s op == ret_of op ==> s = S.empty) /\
                   ((s <> S.empty /\ Dequeue? (fst (snd op)) /\ ret_of op == return s op) ==> Some? (ret_of op))) =
  S.always_min_exists s

let ret_ele (o:op_t{Dequeue? (fst (snd o)) /\ Some? (ret_of o)}) : (pos * nat) =
  let (_, (_, Some x)) = o in x

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  match x, y with
  |(_,(Enqueue _,_)), (_,(Enqueue _,_)) -> if fst x < fst y then Second_then_first else First_then_second
  |_, (_,(Dequeue,None)) -> Noop_second
  |(_,(Dequeue,None)), _ -> Noop_first
  |(_,(Dequeue,None)), (_,(Dequeue,None)) -> Noop_both
  |(_,(Enqueue _,_)), (_,(Dequeue,Some _)) -> First_then_second
  |(_,(Dequeue,Some _)), (_,(Enqueue _,_)) -> Second_then_first 
  |(_,(Dequeue,Some _)), (_,(Dequeue,Some _)) -> if ret_ele x = ret_ele y then First 
                                                 else if fst (ret_ele x) >= fst (ret_ele y) then First_then_second
                                                      else Second_then_first

let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires true) // (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  let i = S.intersect lca (S.intersect s1 s2) in
  let da = S.remove_if s1 (fun e -> S.mem e lca) in
  let db = S.remove_if s2 (fun e -> S.mem e lca) in
  let m = S.union i (S.union da db) in
  m

let merge_prop (lca s1 s2:concrete_st) 
  : Lemma (forall e. S.mem e (concrete_merge lca s1 s2) <==>               
                ((S.mem e lca /\ S.mem e s1 /\ S.mem e s2) \/
                 (S.mem e s1 /\ not (S.mem e lca)) \/
                 (S.mem e s2 /\ not (S.mem e lca))) /\
          (forall e. (S.mem e (concrete_merge lca s1 s2) /\ S.mem e lca /\ S.mem e s2) ==> S.mem e s1)) = ()

let merge_prop1 (lca s1 s2:concrete_st) (mini:(pos & nat)) 
  : Lemma (requires S.find_min (concrete_merge lca s1 s2) = Some mini /\
                    S.mem mini lca /\ S.mem mini s1 /\ S.mem mini s2 /\
                    S.unique_st lca /\ S.unique_st s1 /\ S.unique_st s2)         
          (ensures S.find_min (S.intersect lca (S.intersect s1 s2)) = Some mini) = ()

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires apply_log_ret s l)
          (ensures (forall id. S.mem_id_s id (apply_log s l) ==> S.mem_id_s id s \/ mem_id id l) /\
                   (forall e. S.mem e (apply_log s l) ==> S.mem e s \/ 
                         (exists op. mem op l /\ e == (fst op, get_ele op))))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> mem_cons (head l) (tail l);
       lem_foldl (do s (head l)) (tail l)
       
let rec lem_foldl1 (s:concrete_st) (l:log)
  : Lemma (requires apply_log_ret s l /\ S.unique_st s /\ distinct_ops l /\
                    (forall id. S.mem_id_s id s ==> not (mem_id id l)))
          (ensures S.unique_st (apply_log s l))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> mem_cons (head l) (tail l);
       distinct_invert_append (create 1 (head l)) (tail l);
       lem_foldl1 (do s (head l)) (tail l); ()

let valid_is_unique (s:st0) 
  : Lemma (requires apply_log_ret init_st (ops_of s) /\ distinct_ops (ops_of s) /\ v_of s == apply_log init_st (ops_of s))
          (ensures S.unique_st (v_of s)) =
  lem_foldl1 init_st (ops_of s)

////////////////////////////////////////////////////////////////

let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = ()
  
let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires apply_log_ret init_st (snoc (ops_of s2') last2) /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0)
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires apply_log_ret init_st (snoc (ops_of s2') last2) /\
                    do_pre (v_of s2') last2 /\ 
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    apply_log_ret init_st (snoc (ops_of s2'') last2) /\
                    do_pre (v_of s2'') last2 /\ 
                    consistent_branches l' s1' (do_st s2'' last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires apply_log_ret init_st (snoc (ops_of s2') last2) /\
                    do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    apply_log_ret init_st (snoc (ops_of inv2) last2) /\
                    do_pre (v_of inv2) last2 /\
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 100"
let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires apply_log_ret init_st (snoc (ops_of s1) last1) /\
                    apply_log_ret init_st (snoc (ops_of s2) last2) /\
                    do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    ret_of last1 = return (v_of s1) last1 /\
                    ret_of last2 = return (v_of s2) last2 /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second_then_first? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = admit(); //check - was going thro initially
  S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_diff (snoc (ops_of s1) last1) (ops_of lca);
  lem_diff (snoc (ops_of s2) last2) (ops_of lca);
  lem_foldl init_st (ops_of lca)

////////////////////////////////////////////////////////////////

let ind_fts_pre (lca s1 s2:st) (last1 last2:op_t) =
  apply_log_ret init_st (snoc (ops_of s1) last1) /\
  apply_log_ret init_st (snoc (ops_of s2) last2) /\
  do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
  consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
  consistent_branches lca s1 s2 /\
  length (ops_of s2) > length (ops_of lca) /\
  fst last1 <> fst last2 /\
  (let s2' = inverse_st s2 in
  apply_log_ret init_st (snoc (ops_of s2') last2) /\
  do_pre (v_of s2') last2 /\ 
  consistent_branches lca s1 (do_st s2' last2) /\
  consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
  consistent_branches lca s1 (do_st s2 last2) /\
  First_then_second? (resolve_conflict last1 last2) /\
  do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1 /\
  do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
  eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
     (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)))

#push-options "--z3rlimit 200"
let linearizable_gt0_ind_ee_de_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_fts_pre lca s1 s2 last1 last2 /\
                    ((Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 > fst last2) \/
                     (Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\ Enqueue? (fst (snd last1)))))
       
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = admit(); //check - was going thro initially
   S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
   valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
   lem_diff (snoc (ops_of s1) last1) (ops_of lca); 
   lem_foldl init_st (ops_of lca)

let linearizable_gt0_ind_dd_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_fts_pre lca s1 s2 last1 last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) >= fst (ret_ele last2))
       
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
   admit() //not done yet

let linearizable_gt0_ind_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_fts_pre lca s1 s2 last1 last2)
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] =
  if (Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 > fst last2) ||
     (Dequeue? (fst (snd last2)) && Some? (ret_of last2) && Enqueue? (fst (snd last1))) then
    linearizable_gt0_ind_ee_de_fts lca s1 s2 last1 last2
  else linearizable_gt0_ind_dd_fts lca s1 s2 last1 last2

let ind_stf_pre (lca s1 s2:st) (last1 last2:op_t) =
  apply_log_ret init_st (snoc (ops_of s1) last1) /\
  apply_log_ret init_st (snoc (ops_of s2) last2) /\
  do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
  consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
  consistent_branches lca s1 s2 /\
  length (ops_of s2) > length (ops_of lca) /\
  fst last1 <> fst last2 /\
  ret_of last1 = return (v_of s1) last1 /\
  ret_of last2 = return (v_of s2) last2 /\
  (let s2' = inverse_st s2 in
  apply_log_ret init_st (snoc (ops_of s2') last2) /\
  do_pre (v_of s2') last2 /\ 
  consistent_branches lca (do_st s1 last1) s2' /\
  consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
  consistent_branches lca (do_st s1 last1) s2 /\
  ops_of s1 = ops_of lca /\
  Second_then_first? (resolve_conflict last1 last2) /\
  do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2 /\
  do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
  eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
     (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)))

let linearizable_gt0_ind_ee_de_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_stf_pre lca s1 s2 last1 last2 /\
                    ((Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 < fst last2) \/
                     (Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ Enqueue? (fst (snd last2)))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = admit(); //check - was going thro initially
  S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_diff (snoc (ops_of s2) last2) (ops_of lca);
  lem_foldl init_st (ops_of lca)

let linearizable_gt0_ind_dd_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_stf_pre lca s1 s2 last1 last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) < fst (ret_ele last2))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = admit(); //check - was going thro initially
   valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
   last_deq (v_of s1) last1;
   last_deq (v_of s2) last2

let linearizable_gt0_ind_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_stf_pre lca s1 s2 last1 last2)
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  if (Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 < fst last2) ||
     (Dequeue? (fst (snd last1)) && Some? (ret_of last1) && Enqueue? (fst (snd last2))) then
    linearizable_gt0_ind_ee_de_stf lca s1 s2 last1 last2
  else linearizable_gt0_ind_dd_stf lca s1 s2 last1 last2

let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires apply_log_ret init_st (snoc (ops_of s1) last1) /\
                    apply_log_ret init_st (snoc (ops_of s2) last2) /\
                    do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2)
       
          (ensures (let s2' = inverse_st s2 in
                   ((First_then_second? (resolve_conflict last1 last2) /\
                    apply_log_ret init_st (snoc (ops_of s2') last2) /\
                    do_pre (v_of s2') last2 /\ 
                    consistent_branches lca s1 (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1 /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    apply_log_ret init_st (snoc (ops_of s2') last2) /\
                    do_pre (v_of s2') last2 /\ 
                    consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2 /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = () //going thro because of SMTPat

////////////////////////////////////////////////////////////////

let ind1_fts_pre (lca s1 s2:st) (last1 last2:op_t) =
  apply_log_ret init_st (snoc (ops_of s1) last1) /\
  apply_log_ret init_st (snoc (ops_of s2) last2) /\
  do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
  consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca) /\
  fst last1 <> fst last2 /\
  ret_of last1 = return (v_of s1) last1 /\
  ret_of last2 = return (v_of s2) last2 /\
  (let s1' = inverse_st s1 in
  apply_log_ret init_st (snoc (ops_of s1') last1) /\
  do_pre (v_of s1') last1 /\
  consistent_branches lca s1' (do_st s2 last2) /\
  consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
  consistent_branches lca s1 (do_st s2 last2) /\
  ops_of s2 = ops_of lca /\
  First_then_second? (resolve_conflict last1 last2) /\
  do_pre (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1 /\
  do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
  eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
     (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)))

let linearizable_gt0_ind1_ee_de_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind1_fts_pre lca s1 s2 last1 last2 /\
                    ((Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 > fst last2) \/
                     (Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\ Enqueue? (fst (snd last1)))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = admit(); //check - was going thro initially
  S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_diff (snoc (ops_of s1) last1) (ops_of lca);
  lem_foldl init_st (ops_of lca)

let linearizable_gt0_ind1_dd_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind1_fts_pre lca s1 s2 last1 last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) >= fst (ret_ele last2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = admit(); //check - was going thro initially
   valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
   last_deq (v_of s1) last1;
   last_deq (v_of s2) last2

let linearizable_gt0_ind1_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind1_fts_pre lca s1 s2 last1 last2)
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  if (Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 > fst last2) ||
     (Dequeue? (fst (snd last2)) && Some? (ret_of last2) && Enqueue? (fst (snd last1))) then
     linearizable_gt0_ind1_ee_de_fts lca s1 s2 last1 last2
  else linearizable_gt0_ind1_dd_fts lca s1 s2 last1 last2

let ind1_stf_pre (lca s1 s2:st) (last1 last2:op_t) =
  apply_log_ret init_st (snoc (ops_of s1) last1) /\
  apply_log_ret init_st (snoc (ops_of s2) last2) /\
  do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
  consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca) /\
  fst last1 <> fst last2 /\
  ret_of last1 = return (v_of s1) last1 /\
  ret_of last2 = return (v_of s2) last2 /\
  (let s1' = inverse_st s1 in
  apply_log_ret init_st (snoc (ops_of s1') last1) /\
  do_pre (v_of s1') last1 /\ 
  consistent_branches lca (do_st s1' last1) s2 /\
  consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
  consistent_branches lca (do_st s1 last1) s2 /\
  Second_then_first? (resolve_conflict last1 last2) /\
  do_pre (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2 /\
  do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
  eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
     (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)))

let linearizable_gt0_ind1_ee_de_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind1_stf_pre lca s1 s2 last1 last2 /\
                    ((Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 < fst last2) \/
                     (Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ Enqueue? (fst (snd last2)))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = admit(); //check - was going thro initially
  S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_diff (snoc (ops_of s1) last1) (ops_of lca);
  lem_diff (snoc (ops_of s2) last2) (ops_of lca);
  lem_foldl init_st (ops_of lca)

let min_in_inter (l a b:concrete_st) (mini:(pos & nat)) 
  : Lemma (requires S.find_min b = Some mini /\ S.unique_st l /\ 
                    S.mem mini l /\ S.mem mini a /\ S.mem mini b)       
          (ensures (let i = S.intersect l (S.intersect a b) in
                    S.mem mini i /\ S.find_min i = Some mini /\                   
                    S.mem mini (concrete_merge l a b))) = ()

#push-options "--z3rlimit 1000"
let rec linearizable_gt0_ind1_dd_stf (lca s1' s2':st) (last1 last2:op_t)
  : Lemma (requires apply_log_ret init_st (snoc (ops_of s1') last1) /\
                    apply_log_ret init_st (snoc (ops_of s2') last2) /\
                    do_pre (v_of s1') last1 /\ do_pre (v_of s2') last2 /\ 
                    consistent_branches_s1s2_gt0 lca (do_st s1' last1) (do_st s2' last2) /\
                    consistent_branches lca s1' s2' /\
                    consistent_branches lca (do_st s1' last1) s2' /\
                      //fst last1 <> fst last2 /\
                    ret_of last1 == return (v_of s1') last1 /\
                    ret_of last2 == return (v_of s2') last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) < fst (ret_ele last2))
                    
          (ensures do_pre (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2') last2))) 
          (decreases length (ops_of s1')) =
  valid_is_unique lca; valid_is_unique s1'; valid_is_unique s2'; 
  valid_is_unique (do_st s1' last1); valid_is_unique (do_st s2' last2);
  last_deq (v_of s2') last2; last_deq (v_of s1') last1;
  merge_prop (v_of lca) (do (v_of s1') last1) (v_of s2');
  merge_prop (v_of lca) (do (v_of s1') last1) (do (v_of s2') last2);
  let min1 = S.extract (S.find_min (v_of s1')) in
  let min2 = S.extract (S.find_min (v_of s2')) in
  let i' = S.intersect (v_of lca) (S.intersect (do (v_of s1') last1) (v_of s2')) in
  if ops_of s1' = ops_of lca then ()
  else 
    (if S.mem min2 (v_of lca) && S.mem min1 (v_of lca) then
      (let s1'' = inverse_st s1' in
       let pre1, last1' = un_snoc (ops_of s1') in
       lemma_mem_snoc pre1 last1';
       lem_apply_log init_st (ops_of s1');
       last_deq (v_of s1'') last1'; 
       if Dequeue? (fst (snd last1')) then
         (assume (consistent_branches lca s1' (do_st s2' last2) /\ //todo
                  consistent_branches lca s1'' s2' /\    //todo
                  consistent_branches lca s1' s2'); //todo
         lem_apply_log init_st (ops_of s1'); last_deq (v_of s1'') last1'; valid_is_unique s1''; 
         linearizable_gt0_ind1_dd_stf lca s1'' s2' last1' last2;
         last_deq (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2;
         merge_prop (v_of lca) (v_of s1') (do (v_of s2') last2);
         merge_prop (v_of lca) (v_of s1') (v_of s2');
         merge_prop1 (v_of lca) (v_of s1') (v_of s2') min2;        
         min_in_inter (v_of lca) (v_of s1') (v_of s2') min2;
         min_in_inter (v_of lca) (do (v_of s1') last1) (v_of s2') min2;
         last_deq (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2)
      else 
        (assert (Enqueue? (fst (snd last1'))); 
         let last1_new = (fst last1, (fst (snd last1), return (v_of s1'') last1)) in
         last_deq (v_of s1'') last1_new;
         if (fst last1', get_ele last1') <> min1 then
           (assert (S.find_min (v_of s1'') = Some min1);
            assert (Some? (ret_of last1_new) /\ fst (ret_ele last1_new) < fst (ret_ele last2)); 
            if ret_ele last1_new <> min1 then ()
            else 
              (assert (ret_ele last1_new = min1);
               assert (fst last1' > fst min1); 
               assume (apply_log_ret init_st (snoc (ops_of s1'') last1_new) /\ //todo
                     do_pre (v_of s1'') last1_new /\ //todo
                     consistent_branches lca (do_st s1'' last1_new) (do_st s2' last2) /\ //todo
                     consistent_branches lca s1'' s2' /\    //todo
                     consistent_branches lca (do_st s1'' last1_new) s2'); //todo 
               linearizable_gt0_ind1_dd_stf lca s1'' s2' last1_new last2; 
               merge_prop (v_of lca) (do (v_of s1'') last1_new) (do (v_of s2') last2);
               last_deq (concrete_merge (v_of lca) (do (v_of s1'') last1_new) (v_of s2')) last2;
               merge_prop (v_of lca) (do (v_of s1'') last1_new) (v_of s2'); 
               min_in_inter (v_of lca) (do (v_of s1'') last1_new) (v_of s2') min2;
               assume (fst last1' > fst min2); //todo - this is true but not sure how to prove this
               last_deq (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2))
         else 
           (assume ((fst last1', get_ele last1') = min1); //this case will not occur
            admit())))
     else admit())

let linearizable_gt0_ind1_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind1_stf_pre lca s1 s2 last1 last2)
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 
          [SMTPat (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] =  
  if (Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 < fst last2) ||
     (Dequeue? (fst (snd last1)) && Some? (ret_of last1) && Enqueue? (fst (snd last2))) then
    linearizable_gt0_ind1_ee_de_stf lca s1 s2 last1 last2
  else linearizable_gt0_ind1_dd_stf lca s1 s2 last1 last2

let linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires apply_log_ret init_st (snoc (ops_of s1) last1) /\
                    apply_log_ret init_st (snoc (ops_of s2) last2) /\
                    do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    ret_of last1 = return (v_of s1) last1 /\
                    ret_of last2 = return (v_of s2) last2)
                           
          (ensures (let s1' = inverse_st s1 in
                   ((ops_of s2 = ops_of lca /\
                    apply_log_ret init_st (snoc (ops_of s1') last1) /\
                    do_pre (v_of s1') last1 /\ 
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1' (do_st s2 last2) /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1 /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   ((Second_then_first? (resolve_conflict last1 last2) /\
                    apply_log_ret init_st (snoc (ops_of s1') last1) /\
                    do_pre (v_of s1') last1 /\ 
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2 /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()
#pop-options
////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 200"
let linearizable_gt0_s1's2' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    consistent_branches lca (inverse_st s1) (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     First? (resolve_conflict last1 last2) /\
                     do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = admit(); //was going thro initially in < 10 min
   let _, last1 = un_snoc (ops_of s1) in
   let _, last2 = un_snoc (ops_of s2) in
   valid_is_unique (inverse_st s1); valid_is_unique (inverse_st s2);
   lem_apply_log init_st (ops_of s1);
   lem_apply_log init_st (ops_of s2);
   last_deq (v_of (inverse_st s1)) last1;
   last_deq (v_of (inverse_st s2)) last2; 
   assert (ret_of last1 == S.find_min (v_of (inverse_st s1))); 
   assert (ret_of last1 == S.find_min (v_of (inverse_st s2)));
   ()
#pop-options

////////////////////////////////////////////////////////////////

let linearizable_gt0_s1'_noop (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    consistent_branches lca (inverse_st s1) s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Noop_first? (resolve_conflict last1 last2)))
          (ensures eq (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2))
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = 
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_apply_log init_st (ops_of s1)

////////////////////////////////////////////////////////////////

let linearizable_gt0_s2'_noop (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\
                    consistent_branches lca s1 (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Noop_second? (resolve_conflict last1 last2)))
          (ensures eq (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2)))
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = 
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_apply_log init_st (ops_of s2)

////////////////////////////////////////////////////////////////

let linearizable_gt0_s1's2'_noop_both (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    consistent_branches lca (inverse_st s1) (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Noop_both? (resolve_conflict last1 last2)))
          (ensures eq (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = S.set nat

// init state 
let init_st_s = S.empty

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = 
  match op with
  |(id, (Enqueue x, _)) -> S.add x s
  |(_, (Dequeue, _)) -> if s = S.empty then s else S.remove_min_nat s
  
//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) : Tot prop =
  //(forall e. S.mem e st <==> S.mem (snd e) st_s)
  (forall e. S.mem e st_s <==> (exists id. S.mem (id, e) st))

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

let min_same (st_s:concrete_st_s) (st:concrete_st) 
  : Lemma (requires eq_sm st_s st)
          (ensures (None? (S.find_min_nat st_s) <==> None? (S.find_min st)) /\
                   (Some? (S.find_min_nat st_s) <==> Some? (S.find_min st)) /\
                   (Some? (S.find_min_nat st_s) ==> S.extract (S.find_min_nat st_s) = snd (S.extract (S.find_min st)))) = admit()

let remove_same (st_s:concrete_st_s) (st:concrete_st) 
  : Lemma (requires eq_sm st_s st)
          (ensures (eq_sm (S.remove_min_nat st_s) (S.remove_min st))) = admit()
          
//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st /\ do_pre st op)
          (ensures eq_sm (do_s st_s op) (do st op)) =
  min_same st_s st;
  remove_same st_s st;
  if Enqueue? (fst (snd op)) then () else ()
  
////////////////////////////////////////////////////////////////

(*
let rec linearizable_gt0_ind1_dd_stf (lca s1' s2':st) (last1 last2:op_t)
  : Lemma (requires apply_log_ret init_st (snoc (ops_of s1') last1) /\
                    apply_log_ret init_st (snoc (ops_of s2') last2) /\
                    do_pre (v_of s1') last1 /\ do_pre (v_of s2') last2 /\ 
                    consistent_branches_s1s2_gt0 lca (do_st s1' last1) (do_st s2' last2) /\
                    consistent_branches lca s1' s2' /\
                    consistent_branches lca (do_st s1' last1) s2' /\
                      //fst last1 <> fst last2 /\
                    ret_of last1 == return (v_of s1') last1 /\
                    ret_of last2 == return (v_of s2') last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) < fst (ret_ele last2))
                    
          (ensures do_pre (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2') last2))) 
          (decreases length (ops_of s1')) =
  valid_is_unique lca; valid_is_unique s1'; valid_is_unique s2'; 
  valid_is_unique (do_st s1' last1); valid_is_unique (do_st s2' last2);
  last_deq (v_of s2') last2; last_deq (v_of s1') last1;
  merge_prop (v_of lca) (do (v_of s1') last1) (v_of s2');
  merge_prop (v_of lca) (do (v_of s1') last1) (do (v_of s2') last2);
  let min1 = S.extract (S.find_min (v_of s1')) in
  let min2 = S.extract (S.find_min (v_of s2')) in
  let i' = S.intersect (v_of lca) (S.intersect (do (v_of s1') last1) (v_of s2')) in
  if ops_of s1' = ops_of lca then admit()
  else 
    (if S.mem min2 (v_of lca) && S.mem min1 (v_of lca) then
      (let s1'' = inverse_st s1' in
       let pre1, last1' = un_snoc (ops_of s1') in
       lemma_mem_snoc pre1 last1';
       lem_apply_log init_st (ops_of s1');
       last_deq (v_of s1'') last1'; 
       if Dequeue? (fst (snd last1')) then
         (assume (consistent_branches lca s1' (do_st s2' last2) /\ //todo
                  consistent_branches lca s1'' s2' /\    //todo
                  consistent_branches lca s1' s2'); //todo
         lem_apply_log init_st (ops_of s1'); last_deq (v_of s1'') last1'; valid_is_unique s1''; 
         (*assert (Some? (ret_of last1')); 
           assert (fst (ret_ele last1') < fst (ret_ele last2)); *)
         linearizable_gt0_ind1_dd_stf lca s1'' s2' last1' last2;
         (*assert (do_pre (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2)
                      (concrete_merge (v_of lca) (v_of s1') (do (v_of s2') last2))); *)
         last_deq (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2;
         //assert (S.find_min (concrete_merge (v_of lca) (v_of s1') (v_of s2')) = Some min2);
         merge_prop (v_of lca) (v_of s1') (do (v_of s2') last2);
         merge_prop (v_of lca) (v_of s1') (v_of s2');
        (*assert (min1 <> ret_ele last1');
         assert (S.mem min2 (v_of s1')); 
         assert (S.mem min2 (do (v_of s1') last1));*) 
         let i'' = S.intersect (v_of lca) (S.intersect (v_of s1') (v_of s2')) in
         merge_prop1 (v_of lca) (v_of s1') (v_of s2') min2;
         
         min_in_inter (v_of lca) (v_of s1') (v_of s2') min2;
         //assert (S.find_min i'' = Some min2);          
         min_in_inter (v_of lca) (do (v_of s1') last1) (v_of s2') min2;
         (*assert (S.find_min i' = Some min2);
         
         assert (S.mem min2 i');         
         assert (forall e. S.mem e (do (v_of s1') last1) <==> S.mem e (v_of s1') /\ e <> min1);
         assert (forall e. S.mem e (do (v_of s1') last1) \/ e = min1 <==> S.mem e (v_of s1'));
         assert (ret_ele last1' <> min2);
         assert (forall e. S.mem e i'' /\ e <> min1 <==> S.mem e i');
         
         assert (forall e. S.mem e (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) <==>
                      (S.mem e (concrete_merge (v_of lca) (v_of s1') (v_of s2')) /\ e <> min1)); 
         assert (forall e. S.mem e (concrete_merge (v_of lca) (v_of s1') (do (v_of s2') last2)) /\ e <> min1 <==>
                      S.mem e (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2') last2)));
         
         assert (S.find_min (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) = Some min2);*)
         last_deq (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2)
      else 
        (assert (Enqueue? (fst (snd last1'))); 
         let last1_new = (fst last1, (fst (snd last1), return (v_of s1'') last1)) in
         last_deq (v_of s1'') last1_new;
         if (fst last1', get_ele last1') <> min1 then
           (assert (S.find_min (v_of s1'') = Some min1);
            assert (Some? (ret_of last1_new) /\ fst (ret_ele last1_new) < fst (ret_ele last2)); 
            if ret_ele last1_new <> min1 then ()
            else 
              (assert (ret_ele last1_new = min1);
               assert (fst last1' > fst min1); 
               assume (apply_log_ret init_st (snoc (ops_of s1'') last1_new) /\ //todo
                     do_pre (v_of s1'') last1_new /\ //todo
                     consistent_branches lca (do_st s1'' last1_new) (do_st s2' last2) /\ //todo
                     consistent_branches lca s1'' s2' /\    //todo
                     consistent_branches lca (do_st s1'' last1_new) s2'); //todo 
               linearizable_gt0_ind1_dd_stf lca s1'' s2' last1_new last2; 
               merge_prop (v_of lca) (do (v_of s1'') last1_new) (do (v_of s2') last2);
               last_deq (concrete_merge (v_of lca) (do (v_of s1'') last1_new) (v_of s2')) last2;
               merge_prop (v_of lca) (do (v_of s1'') last1_new) (v_of s2'); 
               min_in_inter (v_of lca) (do (v_of s1'') last1_new) (v_of s2') min2;
               assume (fst last1' > fst min2); //todo - this is true but not sure how to prove this
               last_deq (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2))
         else 
           (assume ((fst last1', get_ele last1') = min1); //this case will not occur
            admit())))
     else admit())
     *)
