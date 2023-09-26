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

let check_find_min (s:concrete_st)
  : Lemma (requires s = S.add (2,1) (S.singleton (3,1)))
          (ensures S.find_min s = Some (2,1)) 
  = let m = S.find_min s in
    assert (S.mem (2,1) s /\ (forall e1. S.mem e1 s ==> fst (2,1) <= fst e1));
    ()

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
  match op with
  |(id, (Enqueue x, _)) -> S.add (id, x) s
  |(_, (Dequeue, _)) -> if s = S.empty then s else S.remove_min s

let eq_min_same (a b:concrete_st) 
  : Lemma (requires eq a b /\ S.unique_st a /\ S.unique_st b)
          (ensures S.find_min a = S.find_min b) = ()

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = 
  assume (S.unique_st a /\ S.unique_st b);
  if Enqueue? (fst (snd op)) then () else ()
  
let return (s:concrete_st) (o:op_t) : ret_t =
  match o with
  |(_, (Enqueue _, _)) -> None
  |(_, (Dequeue, r)) -> if s = S.empty then None 
                          else (S.always_min_exists s; 
                                assert (Some? (S.find_min s));
                                Some (S.extract_s (S.find_min s)))

let last_deq (s:concrete_st) (op:op_t)
  : Lemma (requires true)
          (ensures ((Dequeue? (fst (snd op)) /\ Some? (ret_of op) /\ return s op == ret_of op) ==>
                   s <> S.empty /\ S.find_min s == ret_of op /\
                   S.mem (S.extract_s (S.find_min s)) s) /\
                   (Dequeue? (fst (snd op)) /\ None? (ret_of op) /\ return s op == ret_of op ==> s = S.empty)) =
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
                                                 else if fst (ret_ele x) > fst (ret_ele y) then First_then_second
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
  : Lemma ((concrete_merge lca s1 s2 == 
                         S.union (S.intersect lca (S.intersect s1 s2))
                         (S.union (S.remove_if s1 (fun e -> S.mem e lca)) (S.remove_if s2 (fun e -> S.mem e lca))))) = ()

let merge_min (lca s1 s2:concrete_st) (m:(pos & nat))
  : Lemma (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2) /\
                    Some? (S.find_min (concrete_merge lca s1 s2)) /\
                    m = S.extract_s (S.find_min (concrete_merge lca s1 s2)))
          (ensures S.mem m s1 \/ S.mem m s2) = 
  S.always_min_exists lca; S.always_min_exists s1; S.always_min_exists s2

let min_union (s s1:concrete_st)
  : Lemma (requires (s <> S.empty /\ Some? (S.find_min s) /\ S.unique_st s /\ 
                    (forall e. S.mem e s1 ==> (fst (S.extract_s (S.find_min s))) < (fst e))))
          (ensures (S.find_min (S.union s s1) = S.find_min s)) = ()
          
let min_from_lca (lca s1 s2:concrete_st) (m:(pos & nat))
  : Lemma (requires (S.find_min (S.intersect lca (S.intersect s1 s2)) = Some m) /\
                    (let da = S.remove_if s1 (fun e -> S.mem e lca) in
                     let db = S.remove_if s2 (fun e -> S.mem e lca) in
                     (forall e. S.mem e da ==> fst e > fst m) /\
                     (forall e. S.mem e db ==> fst e > fst m)) /\
                     S.unique_st lca /\ S.unique_st s1 /\ S.unique_st s2)
          (ensures S.find_min (concrete_merge lca s1 s2) = Some m) = 
  assert (S.mem m (S.intersect lca (S.intersect s1 s2)));
  assert (Some? (S.find_min (concrete_merge lca s1 s2)));
  let da = S.remove_if s1 (fun e -> S.mem e lca) in
  let db = S.remove_if s2 (fun e -> S.mem e lca) in
  assert (forall e. S.mem e (S.union da db) ==> fst e > fst m);
  assert (S.mem m (concrete_merge lca s1 s2));
  assert (forall e. S.mem e (concrete_merge lca s1 s2) ==> fst e >= fst m);
  //assume (forall e. S.mem e (concrete_merge lca s1 s2) /\ e <> m ==> fst e > fst m);
  min_union (S.intersect lca (S.intersect s1 s2)) (S.union da db);
  ()

let do_is_unique (s:concrete_st) (op:op_t) 
  : Lemma (requires S.unique_st s /\ (not (S.mem_id_s (fst op) s)))
          (ensures S.unique_st (do s op)) = 
  match op with
  |(id, (Enqueue x, _)) -> ()
  |(_, (Dequeue, _)) -> ()

let append_id (l:concrete_st) (ele:(pos * nat))
  : Lemma (ensures (forall id. S.mem_id_s id (S.add ele l) <==> S.mem_id_s id l \/ id = fst ele) /\
                   (S.unique_st l /\ not (S.mem_id_s (fst ele) l)) ==> 
                    S.unique_st (S.add ele l))
  = ()

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (forall id. S.mem_id_s id (apply_log s l) ==> S.mem_id_s id s \/ mem_id id l) /\
                   (forall e. S.mem e (apply_log s l) ==> S.mem e s \/ 
                         (exists op. mem op l /\ (*Enqueue? (fst (snd op)) /\*) e == (fst op, get_ele op))))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> (if Enqueue? (fst (snd (head l))) then append_id s (fst (head l), get_ele (head l)) else ());
       mem_cons (head l) (tail l);
       lem_foldl (do s (head l)) (tail l)
       
let rec lem_foldl1 (s:concrete_st) (l:log)
  : Lemma (requires S.unique_st s /\ distinct_ops l /\
                    (forall id. S.mem_id_s id s ==> not (mem_id id l)))
          (ensures S.unique_st (apply_log s l))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> do_is_unique s (head l);
       (if Enqueue? (fst (snd (head l))) then append_id s (fst (head l), get_ele (head l)) else ());
       mem_cons (head l) (tail l);
       distinct_invert_append (create 1 (head l)) (tail l);
       lem_foldl1 (do s (head l)) (tail l); ()

let valid_is_unique (s:st0) 
  : Lemma (requires distinct_ops (ops_of s) /\ v_of s == apply_log init_st (ops_of s))
          (ensures S.unique_st (v_of s)) =
  lem_foldl1 init_st (ops_of s)

#push-options "--z3rlimit 50"
let s1s2_gt_lca (lca s1 s2:st1)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    (forall e e1. S.mem e (v_of lca) /\ S.mem e1 (v_of s1) /\ fst e = fst e1 ==> e = e1) /\
                    (forall e e1. S.mem e (v_of lca) /\ S.mem e1 (v_of s2) /\ fst e = fst e1 ==> e = e1))
         
          (ensures (forall e e1. (S.mem e (v_of lca) /\ 
                    S.mem e1 (S.remove_if (v_of s1) (fun e -> S.mem e (v_of lca)))) ==> (fst e < fst e1)) /\
                   (forall e e1. (S.mem e (v_of lca) /\ 
                    S.mem e1 (S.remove_if (v_of s2) (fun e -> S.mem e (v_of lca)))) ==> (fst e < fst e1))) =
  
  lem_foldl init_st (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))


let rec min1_min2 (s:concrete_st) (l:log) (m1 m2:(pos & nat))
  : Lemma (requires S.unique_st s /\ distinct_ops l /\ fst m1 < fst m2 /\
                    S.mem m1 s /\ S.mem m2 s /\ 
                    (forall id. S.mem_id_s id s ==> not (mem_id id l)))
        
          (ensures S.mem m1 (apply_log s l) ==> S.mem m2 (apply_log s l))
          
          (decreases length l) = 
  match length l with
  |0 -> ()
  |_ -> do_is_unique s (head l);
       mem_cons (head l) (tail l);
       distinct_invert_append (create 1 (head l)) (tail l);
       if Enqueue? (fst (snd (head l))) then append_id s (fst (head l), get_ele (head l))
       else (if (S.find_min (do s (head l)) = Some m1) then () else admit());
       min1_min2 (do s (head l)) (tail l) m1 m2       
       
////////////////////////////////////////////////////////////////

let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = ()
  
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

////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 50"
let rec base_de_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    //ret_of last2 = return (v_of s2) last2 /\
                    
                    First_then_second? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\ Enqueue? (fst (snd last1)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
  //assume (ret_ele last2 <> (fst last1, get_ele last1));
           (decreases length (ops_of lca)) =
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  if length (ops_of lca) = 0 then ()
  else 
    (let l' = inverse_st lca in
     let _, lastop = un_snoc (ops_of lca) in
     if Enqueue? (fst (snd lastop)) then 
       (base_de_fts l' l' l' last1 last2;
        mem_ele_id (last (ops_of lca)) (ops_of lca))
     else 
       (if Some? (ret_of lastop) then 
           (base_de_fts l' l' l' last1 last2;
            mem_ele_id (last (ops_of lca)) (ops_of lca);
            assert (S.mem (fst last1, get_ele last1) (concrete_merge (v_of l') (do (v_of l') last1) (do (v_of l') last2)));
            assume (not (S.mem (fst last1, get_ele last1) (v_of lca))); ())
            //assume (not (S.mem (fst last1, get_ele last1) (v_of lca))); ())
            //assume (S.find_min (v_of lca) <> Some (fst last1, get_ele last1)); ())
            //lem_foldl init_st (ops_of lca))
        else (lem_apply_log init_st (ops_of lca);
              last_deq (v_of l') lastop)))

let rec base_de_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ Enqueue? (fst (snd last2)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases length (ops_of lca)) =
 valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  if length (ops_of lca) = 0 then ()
  else 
    (let l' = inverse_st lca in
     let _, lastop = un_snoc (ops_of lca) in
     if Enqueue? (fst (snd lastop)) then 
       (base_de_stf l' l' l' last1 last2;
        mem_ele_id (last (ops_of lca)) (ops_of lca))
     else 
       (if Some? (ret_of lastop) then 
           (assume (S.find_min (v_of lca) <> Some (fst last2, get_ele last2)); ())
            //lem_foldl init_st (ops_of lca))
        else (lem_apply_log init_st (ops_of lca);
              last_deq (v_of l') lastop)))

let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    ret_of last1 = return (v_of s1) last1 /\
                    ret_of last2 = return (v_of s2) last2)
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second_then_first? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) =
  lem_suf_equal2_last (ops_of lca) (snoc (ops_of s1) last1);
  lem_suf_equal2_last (ops_of lca) (snoc (ops_of s2) last2);
  if First_then_second? (resolve_conflict last1 last2) then
    (if (Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 > fst last2) || 
        (Dequeue? (fst (snd last1)) && Some? (ret_of last1) &&
         Dequeue? (fst (snd last2)) && Some? (ret_of last2) && fst (ret_ele last1) > fst (ret_ele last2)) then ()
     else base_de_fts lca s1 s2 last1 last2)
  else if Second_then_first? (resolve_conflict last1 last2) then
    (if (Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 < fst last2) ||
        (Dequeue? (fst (snd last1)) && Some? (ret_of last1) &&
         Dequeue? (fst (snd last2)) && Some? (ret_of last2) && fst (ret_ele last1) <= fst (ret_ele last2)) then ()
     else base_de_stf lca s1 s2 last1 last2)
  else ()
  
  
  (*S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_diff (snoc (ops_of s1) last1) (ops_of lca);
  lem_diff (snoc (ops_of s2) last2) (ops_of lca);
  lem_foldl init_st (ops_of lca)*)

////////////////////////////////////////////////////////////////

let ind_fts_pre (lca s1 s2:st) (last1 last2:op_t) =
  consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
  consistent_branches lca s1 s2 /\
  length (ops_of s2) > length (ops_of lca) /\
  fst last1 <> fst last2 /\
  ret_of last1 = return (v_of s1) last1 /\
  ret_of last2 = return (v_of s2) last2 /\
  (let s2' = inverse_st s2 in
  consistent_branches lca s1 (do_st s2' last2) /\
  consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
  consistent_branches lca s1 (do_st s2 last2) /\
  First_then_second? (resolve_conflict last1 last2) /\
  eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
     (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)))

#push-options "--z3rlimit 200"
let linearizable_gt0_ind_ee_de_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_fts_pre lca s1 s2 last1 last2 /\
                    ((Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 > fst last2) \/
                     (Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\ Enqueue? (fst (snd last1)))))
       
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
   S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
   valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
   lem_diff (snoc (ops_of s1) last1) (ops_of lca); 
   lem_foldl init_st (ops_of lca)

let linearizable_gt0_ind_dd_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_fts_pre lca s1 s2 last1 last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) > fst (ret_ele last2))
       
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
   admit()

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
  consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
  consistent_branches lca s1 s2 /\
  length (ops_of s2) > length (ops_of lca) /\
  fst last1 <> fst last2 /\
  ret_of last1 = return (v_of s1) last1 /\
  ret_of last2 = return (v_of s2) last2 /\
  (let s2' = inverse_st s2 in
  consistent_branches lca (do_st s1 last1) s2' /\
  consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
  consistent_branches lca (do_st s1 last1) s2 /\
  ops_of s1 = ops_of lca /\
  Second_then_first? (resolve_conflict last1 last2) /\
  eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
     (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)))

let linearizable_gt0_ind_ee_de_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_stf_pre lca s1 s2 last1 last2 /\
                    ((Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 < fst last2) \/
                     (Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ Enqueue? (fst (snd last2)))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_diff (snoc (ops_of s2) last2) (ops_of lca);
  lem_foldl init_st (ops_of lca)

let linearizable_gt0_ind_dd_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_stf_pre lca s1 s2 last1 last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) <= fst (ret_ele last2))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
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
  : Lemma (requires consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    ret_of last1 = return (v_of s1) last1 /\
                    ret_of last2 = return (v_of s2) last2)
       
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
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = () //going thro because of SMTPat

////////////////////////////////////////////////////////////////

let ind1_fts_pre (lca s1 s2:st) (last1 last2:op_t) =
  consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca) /\
  fst last1 <> fst last2 /\
  ret_of last1 = return (v_of s1) last1 /\
  ret_of last2 = return (v_of s2) last2 /\
  (let s1' = inverse_st s1 in
  consistent_branches lca s1' (do_st s2 last2) /\
  consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
  consistent_branches lca s1 (do_st s2 last2) /\
  ops_of s2 = ops_of lca /\
  First_then_second? (resolve_conflict last1 last2) /\
  eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
     (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)))

let linearizable_gt0_ind1_ee_de_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind1_fts_pre lca s1 s2 last1 last2 /\
                    ((Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 > fst last2) \/
                     (Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\ Enqueue? (fst (snd last1)))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_diff (snoc (ops_of s1) last1) (ops_of lca);
  lem_foldl init_st (ops_of lca)

let linearizable_gt0_ind1_dd_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind1_fts_pre lca s1 s2 last1 last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) > fst (ret_ele last2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
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
  consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca) /\
  fst last1 <> fst last2 /\
  ret_of last1 = return (v_of s1) last1 /\
  ret_of last2 = return (v_of s2) last2 /\
  (let s1' = inverse_st s1 in
  consistent_branches lca (do_st s1' last1) s2 /\
  consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
  consistent_branches lca (do_st s1 last1) s2 /\
  Second_then_first? (resolve_conflict last1 last2) /\
  eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
     (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)))

let linearizable_gt0_ind1_ee_de_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind1_stf_pre lca s1 s2 last1 last2 /\
                    ((Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 < fst last2) \/
                     (Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ Enqueue? (fst (snd last2)))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
  lem_diff (snoc (ops_of s1) last1) (ops_of lca);
  lem_diff (snoc (ops_of s2) last2) (ops_of lca);
  lem_foldl init_st (ops_of lca)

#push-options "--z3rlimit 700"
let rec linearizable_gt0_ind1_dd_stf (lca s1' s2':st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1' last1) (do_st s2' last2) /\
                    consistent_branches lca s1' s2' /\
                    consistent_branches lca (do_st s1' last1) s2' /\
                    fst last1 <> fst last2 /\
                    ret_of last1 = return (v_of s1') last1 /\
                    ret_of last2 = return (v_of s2') last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) < fst (ret_ele last2))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2') last2)))
          (decreases length (ops_of s1')) =
  S.always_min_exists (v_of lca); S.always_min_exists (v_of s1'); S.always_min_exists (v_of s2');
  S.always_min_exists (do (v_of s1') last1); S.always_min_exists (do (v_of s2') last2);
  valid_is_unique lca; valid_is_unique s1'; valid_is_unique s2'; valid_is_unique (do_st s1' last1);
  last_deq (v_of s2') last2; last_deq (v_of s1') last1;
  let min1 = S.extract_s (S.find_min (v_of s1')) in
  let min2 = S.extract_s (S.find_min (v_of s2')) in
  let da = S.remove_if (do (v_of s1') last1) (fun e -> S.mem e (v_of lca)) in
  let da' = S.remove_if (v_of s1') (fun e -> S.mem e (v_of lca)) in
  let db = S.remove_if (do (v_of s2') last2) (fun e -> S.mem e (v_of lca)) in
  let db' = S.remove_if (v_of s2') (fun e -> S.mem e (v_of lca)) in
  let i' = S.intersect (v_of lca) (S.intersect (do (v_of s1') last1) (v_of s2')) in
  let i = S.intersect (v_of lca) (S.intersect (do (v_of s1') last1) (do (v_of s2') last2)) in
  merge_prop (v_of lca) (do (v_of s1') last1) (v_of s2');
  merge_prop (v_of lca) (do (v_of s1') last1) (do (v_of s2') last2);
  if ops_of s1' = ops_of lca then admit()                                            //done 
  else 
    (if S.mem min2 (v_of lca) && S.mem min1 (v_of lca) then
       (assume (length (ops_of s1') > length (ops_of lca)); 
        let s1'' = inverse_st s1' in
        let pre1, last1' = un_snoc (ops_of s1') in
        lemma_mem_snoc pre1 last1';

        if Dequeue? (fst (snd last1')) then
          (admit()(*;assume (consistent_branches lca s1' (do_st s2' last2) /\
                   consistent_branches lca s1'' s2' /\
                   consistent_branches lca s1' s2' /\
                   fst last1' <> fst last2);
           lem_apply_log init_st (ops_of s1');
           assume (ret_of last1' = return (v_of s1'') last1');
           assume (Some? (ret_of last1'));
           if (fst (ret_ele last1') < fst (ret_ele last2)) then
             (S.always_min_exists (v_of s1''); valid_is_unique s1''; last_deq (v_of s1'') last1';
              S.always_min_exists (v_of s1'); 
              assume (S.unique_st (v_of s1')); //  valid_is_unique (do_st s1'' last1'); 
              assume (S.mem min2 (v_of s2'));
              assume (not (S.mem min2 db'));
              linearizable_gt0_ind1_dd_stf lca s1'' s2' last1' last2;
              assume (eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2)
                         (concrete_merge (v_of lca) (v_of s1') (do (v_of s2') last2))); 
              //lem_diff (ops_of s1') (ops_of lca);
              //lem_diff (ops_of s1'') (ops_of lca);
              //split_prefix init_st (ops_of lca) (ops_of s1'');
              let i'' = S.intersect (v_of lca) (S.intersect (v_of s1') (v_of s2')) in
              let da'' = S.remove_if (v_of s1') (fun e -> S.mem e (v_of lca)) in
              merge_prop (v_of lca) (v_of s1') (v_of s2');
              merge_prop (v_of lca) (v_of s1') (do (v_of s2') last2);

              if None? (S.find_min (concrete_merge (v_of lca) (v_of s1') (v_of s2'))) then
                ((*admit();assume ((concrete_merge (v_of lca) (v_of s1') (v_of s2')) = S.empty);
                 assume (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2 = S.empty);
                 assume ((concrete_merge (v_of lca) (v_of s1') (do (v_of s2') last2)) = S.empty);
                 assume (db' = S.empty);
                 assume (da'' = S.empty);
                 assume (db = S.empty); 
                 assume (i'' = S.empty);*)
                 admit())
              else 
               (if (S.find_min (concrete_merge (v_of lca) (v_of s1') (v_of s2')) = Some min2) then
                 (admit()(*;assume (S.mem min2 (v_of lca));
                  assume (S.mem min2 i''); 
                  assume (S.mem min2 (v_of s1'));
                  assume (S.mem min2 (do (v_of s1') last1));
                  assume (S.mem min2 (v_of s2'));
                  assume (S.mem min2 i');
                  admit()*)) //todo
               
                else admit())) //done
              
           else admit()*)) //done
         
        else  
          (assume (Enqueue? (fst (snd last1'))); 
           let last1_new = (fst last1, (fst (snd last1), return (v_of s1'') last1)) in
           assume (consistent_branches lca (do_st s1'' last1_new) (do_st s2' last2) /\ //todo
                   consistent_branches lca s1'' s2' /\    //todo
                   consistent_branches lca (do_st s1'' last1_new) s2' /\
                   fst last1_new <> fst last2); //todo
           lem_apply_log init_st (ops_of s1'); S.always_min_exists (v_of s1''); valid_is_unique s1''; 
           last_deq (v_of s1'') last1_new;
           if Some? (ret_of last1_new) then
           
             (if fst (ret_ele last1_new) < fst (ret_ele last2) then 
               (let da_new = S.remove_if (do (v_of s1'') last1_new) (fun e -> S.mem e (v_of lca)) in
               let i_new = S.intersect (v_of lca) (S.intersect (do (v_of s1'') last1_new) (v_of s2')) in
               assume (not (S.mem min2 da_new));
               assume (not (S.mem min2 db')); 
               linearizable_gt0_ind1_dd_stf lca s1'' s2' last1_new last2;
               merge_prop (v_of lca) (do (v_of s1'') last1_new) (v_of s2');
               merge_prop (v_of lca) (do (v_of s1'') last1_new) (do (v_of s2') last2);
               assume (S.mem min2 (concrete_merge (v_of lca) (do (v_of s1'') last1_new) (v_of s2'))); //todo
               assume (S.find_min (concrete_merge (v_of lca) (do (v_of s1'') last1_new) (v_of s2')) = Some min2); //todo
               assume (S.mem min2 i_new);
               assume (S.mem min2 (do (v_of s1'') last1_new));
               assume (S.mem min2 (do (v_of s1') last1));
               assume (not (S.mem min1 (do (v_of s1') last1)));
               assume (S.find_min (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) = Some min2); //todo
               ())
               
             else admit())

           else admit())) 

     else admit())


#push-options "--z3rlimit 300"
let rec linearizable_gt0_ind1_dd_stf (lca s1' s2':st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1' last1) (do_st s2' last2) /\
                    consistent_branches lca s1' s2' /\
                    consistent_branches lca (do_st s1' last1) s2' /\
                    //length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    ret_of last1 = return (v_of s1') last1 /\
                    ret_of last2 = return (v_of s2') last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (ret_ele last1) < fst (ret_ele last2))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) last2)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2') last2)))
          (decreases length (ops_of s1')) = 
  S.always_min_exists (v_of lca); S.always_min_exists (v_of s1'); S.always_min_exists (v_of s2');
  S.always_min_exists (do (v_of s1') last1); S.always_min_exists (do (v_of s2') last2);
  valid_is_unique lca; valid_is_unique s1'; valid_is_unique s2'; valid_is_unique (do_st s1' last1);
  last_deq (v_of s2') last2; last_deq (v_of s1') last1;
  let min1 = S.extract_s (S.find_min (v_of s1')) in
  let min2 = S.extract_s (S.find_min (v_of s2')) in
  let da = S.remove_if (do (v_of s1') last1) (fun e -> S.mem e (v_of lca)) in
  let da' = S.remove_if (v_of s1') (fun e -> S.mem e (v_of lca)) in
  let db = S.remove_if (do (v_of s2') last2) (fun e -> S.mem e (v_of lca)) in
  let db' = S.remove_if (v_of s2') (fun e -> S.mem e (v_of lca)) in
  let i' = S.intersect (v_of lca) (S.intersect (do (v_of s1') last1) (v_of s2')) in
  merge_prop (v_of lca) (do (v_of s1') last1) (v_of s2');
  if ops_of s1' = ops_of lca then ()                                            //done
  
  else 
    (if S.mem min2 (v_of lca) && S.mem min1 (v_of lca) then
       (assert (length (ops_of s1') > length (ops_of lca)); 
        let s1'' = inverse_st s1' in
        let pre1, last1' = un_snoc (ops_of s1') in
        lemma_mem_snoc pre1 last1';
       
        if Dequeue? (fst (snd last1')) && ret_of last1 = return (v_of s1'') last1 then
          (assume (consistent_branches lca (do_st s1'' last1) (do_st s2' last2) /\ //todo
                   consistent_branches lca s1'' s2' /\    //todo
                   consistent_branches lca (do_st s1'' last1) s2'); //todo
           linearizable_gt0_ind1_dd_stf lca s1'' s2' last1 last2)                     //done
        
        else if Enqueue? (fst (snd last1')) && ret_of last1 = return (v_of s1'') last1 then
           (lem_apply_log init_st (ops_of s1'); S.always_min_exists (v_of s1''); valid_is_unique s1'';
            last_deq (v_of s1'') last1;
            assume (consistent_branches lca (do_st s1'' last1) (do_st s2' last2) /\
                    consistent_branches lca s1'' s2' /\    //todo
                    consistent_branches lca (do_st s1'' last1) s2');
            linearizable_gt0_ind1_dd_stf lca s1'' s2' last1 last2;
            lem_foldl init_st (ops_of lca);
            lem_diff (ops_of s1') (ops_of lca);
            
            assert ((fst last1', get_ele last1') <> min1);
            assert (S.mem min1 (v_of s1''));
            
            assert (distinct_ops (diff (ops_of s1'') (ops_of lca)));
            lem_diff (ops_of s1'') (ops_of lca);
            split_prefix init_st (ops_of lca) (ops_of s1'');
            
            min1_min2 (v_of lca) (diff (ops_of s1'') (ops_of lca)) min1 min2; 
           
            assert (S.mem min2 (v_of s1'')); 
            assert (S.mem min2 (do (v_of s1') last1)); 
            assert (S.mem min2 i'); 
            assert (S.find_min i' = Some min2);
            assume ((forall e e1. S.mem e (v_of lca) /\ S.mem e1 (v_of s1') /\ fst e = fst e1 ==> e = e1) /\
                    (forall e e1. S.mem e (v_of lca) /\ S.mem e1 (v_of s2') /\ fst e = fst e1 ==> e = e1)); //todo
            s1s2_gt_lca lca (do_st s1' last1) s2';
            min_union i' (S.union da db');
            assert (S.find_min (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2')) = Some min2);
            ())
       else admit())
   
    else if S.mem min2 (v_of lca) && not (S.mem min1 (v_of lca)) then
      (assume ((forall e e1. S.mem e (v_of lca) /\ S.mem e1 (v_of s1') /\ fst e = fst e1 ==> e = e1) /\
               (forall e e1. S.mem e (v_of lca) /\ S.mem e1 (v_of s2') /\ fst e = fst e1 ==> e = e1)); //todo
       s1s2_gt_lca lca s1' s2')
   
    else if not (S.mem min2 (v_of lca)) && not (S.mem min1 (v_of lca)) then
      (admit())
   
    else admit())


 (*let i' = S.intersect (v_of lca) (S.intersect (do (v_of s1) last1) (v_of s2)) in
  let i = S.intersect (v_of lca) (S.intersect (do (v_of s1) last1) (do (v_of s2) last2)) in
  let m' = concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2) in
  let m = concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) in*)

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
  : Lemma (requires consistent_branches_s1s2_gt0 lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    ret_of last1 = return (v_of s1) last1 /\
                    ret_of last2 = return (v_of s2) last2)
                           
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

let linearizable_gt0_s1's2' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    consistent_branches lca (inverse_st s1) (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     First? (resolve_conflict last1 last2)))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
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

(*#push-options "--z3rlimit 50"
let rec dd_same (lca s1' s2':st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1' s2' /\  
                    consistent_branches lca (do_st s1' last1) (do_st s2' last2) /\
                    fst last1 <> fst last2 /\
                     
                    Dequeue? (fst (snd last1)) /\ Dequeue? (fst (snd last2)) /\ 
                    Some? (ret_of last1) /\ ret_of last1 = ret_of last2 /\
                    S.find_min (v_of s1') = S.find_min (v_of s2'))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2') last2)))) 
          (decreases %[length (ops_of s1'); length (ops_of s2')]) =
  if ops_of s1' = ops_of lca then
    (valid_is_unique lca; valid_is_unique s1'; valid_is_unique s2')
  else 
    (let s1'' = inverse_st s1' in
     let _, last1' = un_snoc (ops_of s1') in
     if Enqueue? (fst (snd last1')) then
       (valid_is_unique lca; valid_is_unique s1'; valid_is_unique s2'; valid_is_unique s1'';
        assume (forall id. S.mem_id_s id (v_of s1') ==> fst last1' > id);()) //working
     else admit())

let rec dd_same_s1_s2gt0 (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    consistent_branches lca (inverse_st s1) (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     First? (resolve_conflict last1 last2)))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  let s1' = inverse_st s1 in
  let s2' = inverse_st s2 in
  lem_inverse (ops_of lca) (ops_of s1);
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s2);
  inverse_diff_id_s1'_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  lem_apply_log init_st (ops_of s1);
  lem_apply_log init_st (ops_of s2);
  assert (consistent_branches lca s1' s2'); 
  assert (Dequeue? (fst (snd last1)) /\ Dequeue? (fst (snd last2)) /\ ret_of last1 = ret_of last2 /\ Some? (ret_of last1));
  last_deq (v_of s1') last1;
  last_deq (v_of s2') last2; 
  dd_same lca s1' s2' last1 last2*)

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = S.set nat

// init state 
let init_st_s = S.empty

let find_min_seq (s:concrete_st_s)
    : (m:option nat
           {(Some? m <==> (exists (e:nat). S.mem e s /\ (forall e1. S.mem e1 s ==> e <= e1))) /\
            (Some? m ==> (exists (e:nat). S.mem e s /\ (forall e1. S.mem e1 s ==> e <= e1) /\ e = S.extract_s m)) /\
        (s = S.empty ==> (m = None \/ (~ (exists (e:nat). S.mem e s /\ (forall e1. S.mem e1 s ==> e <= e1))))) 
        (*s <> empty ==> Some? m*)}) =
  S.find_if s (fun e -> (S.forall_s s (fun e1 -> e <= e1)))
  
let remove_min_seq (s:concrete_st_s) 
  : (r:concrete_st_s{(s = S.empty ==> r = s) /\
                   (s <> S.empty /\ Some? (find_min_seq s) ==> (forall e. S.mem e r <==> (S.mem e s /\ e <> S.extract_s (find_min_seq s)))) /\
                   (s <> S.empty /\ None? (find_min_seq s) ==> (forall e. S.mem e r <==> S.mem e s))}) =
  if s = S.empty then s 
  else (let m = find_min_seq s in
        if Some? m then S.remove_if s (fun e -> e = S.extract_s (find_min_seq s))
        else s)
        
// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = 
  match op with
  |(id, (Enqueue x, _)) -> S.add x s
  |(_, (Dequeue, _)) -> if s = S.empty then s else remove_min_seq s
  
//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) : Tot prop =
  (forall e. S.mem e st ==> S.mem (snd e) st_s) /\
  (forall e. S.mem e st_s ==> (exists id. S.mem (id, e) st))

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

let min_same (st_s:concrete_st_s) (st:concrete_st) 
  : Lemma (requires eq_sm st_s st)
          (ensures (None? (find_min_seq st_s) <==> None? (S.find_min st)) /\
                   (Some? (find_min_seq st_s) <==> Some? (S.find_min st)) /\
                   (Some? (find_min_seq st_s) ==> S.extract_s (find_min_seq st_s) = snd (S.extract_s (S.find_min st)))) = admit()

let remove_same (st_s:concrete_st_s) (st:concrete_st) 
  : Lemma (requires eq_sm st_s st)
          (ensures (eq_sm (remove_min_seq st_s) (S.remove_min st))) =
  admit()
 
//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) =
  min_same st_s st;
  remove_same st_s st;
  if Enqueue? (fst (snd op)) then () else ()
  
////////////////////////////////////////////////////////////////


(*
let linearizable_gt0_ind_dd_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ind_fts_pre lca s1 s2 last1 last2 /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (extract last1) < fst (extract last2))
       
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
   S.always_min_exists (v_of lca); S.always_min_exists (v_of s1); S.always_min_exists (v_of s2);
   S.always_min_exists (do (v_of s1) last1); S.always_min_exists (do (v_of s2) last2);
   valid_is_unique lca; valid_is_unique s1; valid_is_unique s2;
   valid_is_unique (do (v_of s1) last1, hide (snoc (ops_of s1) last1));
   valid_is_unique (do (v_of s2) last2, hide (snoc (ops_of s2) last2)); 
   last_deq (v_of s1) last1;
   last_deq (v_of s2) last2;
   let min1 = S.find_min (v_of s1) in
   let min2 = S.find_min (v_of s2) in
   assert (ret_of last1 = min1);
   assert (ret_of last2 = min2);
   assert (fst (S.extract_s min1) < fst (S.extract_s min2)); 
   lem_diff (snoc (ops_of s1) last1) (ops_of lca); 
   lem_diff (snoc (ops_of s2) last2) (ops_of lca); 
   lem_diff (ops_of s1) (ops_of lca); 
   lem_diff (ops_of s2) (ops_of lca); 
   lem_foldl init_st (ops_of lca);
   lem_foldl init_st (ops_of s1);
   lem_foldl init_st (ops_of s2);
   lem_foldl init_st (snoc (ops_of s1) last1);
   lem_foldl init_st (snoc (ops_of s2) last2);
   split_prefix init_st (ops_of lca) (ops_of s1);
   split_prefix init_st (ops_of lca) (ops_of s2);
   split_prefix init_st (ops_of lca) (snoc (ops_of s1) last1);
   split_prefix init_st (ops_of lca) (snoc (ops_of s2) last2);
   lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
   lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
   lem_foldl (v_of lca) (diff (snoc (ops_of s1) last1) (ops_of lca));
   lem_foldl (v_of lca) (diff (snoc (ops_of s2) last2) (ops_of lca));
   //assume (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2) <> S.empty);
   S.always_min_exists (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2));
   //let min_m = S.extract_s (S.find_min (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) in
   //merge_min (v_of lca) (v_of s1) (do (v_of s2) last2) min_m;
   //assume (S.find_min (v_of s1) = min1);
   //assume (forall id. S.mem_id_s id (do (v_of s2) last2) ==> lt (fst (S.extract_s min1)) id); 
   S.mem_remove_min (v_of s1); S.mem_remove_min (v_of s2);
   //assume (min_m = S.extract_s min1); 
   ()
   *)
