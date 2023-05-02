module App

open SeqUtils
module S = Set_extended

#set-options "--query_stats"
// the concrete state type
// It is a set of pairs of timestamp and element.
type concrete_st = s:S.set (nat & nat)//{s <> empty ==> (exists (e:(nat * nat)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1))}

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

type ret_t:eqtype = option (nat * nat)

let get_ele (o:op_t{Enqueue? (fst (snd o))}) : nat =
  match o with
  |(_, (Enqueue x,_)) -> x

let mem_id_s (id:nat) (s:concrete_st) =
  S.exists_s s (fun e -> fst e = id)
  
let unique_st (s:concrete_st) =
  //forall_s s (fun e -> count e s > 0) &&
  S.forall_s s (fun e -> not (S.exists_s s (fun e1 -> snd e <> snd e1 && fst e = fst e1)))

val extract_s (#a:Type0) (m:option a{Some? m}) : a
let extract_s (Some x) = x

let find_min (s:concrete_st)
    : (m:option (nat * nat) 
           {(Some? m <==> (exists (e:(nat * nat)). S.mem e s /\ (forall e1. S.mem e1 s ==> fst e <= fst e1))) /\
            (Some? m ==> (exists (e:(nat * nat)). S.mem e s /\ (forall e1. S.mem e1 s ==> fst e <= fst e1) /\ e = extract_s m)) /\
        (s = S.empty ==> (m = None \/ (~ (exists (e:(nat * nat)). S.mem e s /\ (forall e1. S.mem e1 s ==> fst e <= fst e1))))) 
        (*s <> empty ==> Some? m*)}) =
  S.find_if s (fun e -> (S.forall_s s (fun e1 -> fst e <= fst e1)))

let check_find_min (s:concrete_st)
  : Lemma (requires s = S.add (2,1) (S.singleton (3,1)))
          (ensures find_min s = Some (2,1)) 
  = let m = find_min s in
    assert (S.mem (2,1) s /\ (forall e1. S.mem e1 s ==> fst (2,1) <= fst e1));
    (*assert (Some? m);
    assert (fst (extract_s m) = 1);
    assert (forall e. mem e s ==> 1 <= fst e);*) ()

let remove_min (s:concrete_st) 
  : (r:concrete_st{(s = S.empty ==> r = s) /\
                   (s <> S.empty /\ Some? (find_min s) ==> (forall e. S.mem e r <==> (S.mem e s /\ e <> extract_s (find_min s)))) /\
                   (s <> S.empty /\ None? (find_min s) ==> (forall e. S.mem e r <==> S.mem e s))}) =
  if s = S.empty then s 
  else (let m = find_min s in
        if Some? m then S.remove_if s (fun e -> e = extract_s (find_min s))
        else s)

let find_min_equal (a b:concrete_st)
  : Lemma (requires unique_st a /\ unique_st b /\ eq a b)
          (ensures eq (remove_min a) (remove_min b)) = ()

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
  match op with
  |(id, (Enqueue x, _)) -> S.add (id, x) s
  |(_, (Dequeue, _)) -> if s = S.empty then s else remove_min s

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = 
  assume (unique_st a /\ unique_st b); 
  match op with
  |(id, (Enqueue x, _)) -> ()
  |(_, (Dequeue, _)) -> ()
  
let return (s:concrete_st) (o:op_t) : ret_t =
  match o with
  |(_, (Enqueue _, _)) -> None
  |(_, (Dequeue, r)) -> if s = S.empty then None 
                          else (assume (exists (e:(nat * nat)). S.mem e s /\ (forall e1. S.mem e1 s ==> fst e <= fst e1));
                                assert (Some? (find_min s));
                                Some (extract_s (find_min s)))

let extract (o:op_t{Dequeue? (fst (snd o)) /\ Some? (ret_of o)}) : (nat * nat) =
  let (_, (_, Some x)) = o in x

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  match x, y with
  |(_,(Enqueue _,_)), (_,(Enqueue _,_)) -> if fst x < fst y then Second_then_first else First_then_second
  |_, (_,(Dequeue,None)) -> Noop_second
  |(_,(Dequeue,None)), _ -> Noop_first
  |(_,(Dequeue,None)), (_,(Dequeue,None)) -> Noop_both
  |(_,(Enqueue _,_)), (_,(Dequeue,Some _)) -> Second_then_first
  |(_,(Dequeue,Some _)), (_,(Enqueue _,_)) -> First_then_second 
  |(_,(Dequeue,Some _)), (_,(Dequeue,Some _)) -> if fst (extract x) = fst (extract y) then First 
                                                 else if fst (extract x) < fst (extract y) then First_then_second
                                                      else Second_then_first
 
let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  let i' = S.intersect s1 s2 in
  let i = S.intersect lca i' in
  let da = S.remove_if s1 (fun e -> S.mem e lca) in
  let db = S.remove_if s2 (fun e -> S.mem e lca) in
  S.union i (S.union da db)
  
let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0)
        
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

let linearizable_gt0_base_ee_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 > fst last2)
         
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

#push-options "--z3rlimit 50"
let linearizable_gt0_base_de_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ Enqueue? (fst (snd last2)))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = 
  assume (unique_st (v_of lca) /\ unique_st (v_of s1) /\ unique_st (v_of s2)); //todo
  assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
  assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond  
  assume (forall id. mem_id_s id (v_of s2) ==> fst last2 > id);
  ()

let linearizable_gt0_base_dd_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (extract last1) < fst (extract last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = 
  assume (unique_st (v_of lca) /\ unique_st (v_of s1) /\ unique_st (v_of s2)); //todo
  assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
  assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond  
  ()

let linearizable_gt0_base_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    First_then_second? (resolve_conflict last1 last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  if Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 > fst last2 then
    linearizable_gt0_base_ee_fts lca s1 s2 last1 last2
  else if Dequeue? (fst (snd last1)) && Some? (ret_of last1) && Enqueue? (fst (snd last2)) then
    linearizable_gt0_base_de_fts lca s1 s2 last1 last2
  else linearizable_gt0_base_dd_fts lca s1 s2 last1 last2

let linearizable_gt0_base_ee_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 < fst last2)
         
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_base_de_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\ Enqueue? (fst (snd last1)))
         
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  assume (unique_st (v_of lca) /\ unique_st (v_of s1) /\ unique_st (v_of s2)); //todo
  assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
  assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond  
  assume (forall id. mem_id_s id (v_of s1) ==> fst last1 > id);
  ()

let linearizable_gt0_base_dd_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (extract last1) >= fst (extract last2))
         
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
   assume (unique_st (v_of lca) /\ unique_st (v_of s1) /\ unique_st (v_of s2)); //todo
   assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
   assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond  
   ()

let linearizable_gt0_base_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    Second_then_first? (resolve_conflict last1 last2))
         
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =
  if Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 < fst last2 then
    linearizable_gt0_base_ee_stf lca s1 s2 last1 last2
  else if Dequeue? (fst (snd last2)) && Some? (ret_of last2) && Enqueue? (fst (snd last1)) then
    linearizable_gt0_base_de_stf lca s1 s2 last1 last2
  else linearizable_gt0_base_dd_stf lca s1 s2 last1 last2
  
let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)))
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second_then_first? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = admit()

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
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = admit()

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
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   ((Second_then_first? (resolve_conflict last1 last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = admit()

let linearizable_gt0_s1's2' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     First? (resolve_conflict last1 last2) /\
                     (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                     (exists l1. (v_of (inverse_st s1) == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of (inverse_st s2) == apply_log (v_of lca) l2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
   assume (unique_st (v_of lca) /\ unique_st (v_of s1) /\ unique_st (v_of s2)); //todo
   lem_apply_log init_st (ops_of s1);
   lem_apply_log init_st (ops_of s2);
   admit()

let linearizable_gt0_s1'_noop (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Noop_first? (resolve_conflict last1 last2) /\
                     (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                     (exists l1. (v_of (inverse_st s1) == apply_log (v_of lca) l1)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures eq (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2))
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = 
  assume (unique_st (v_of lca) /\ unique_st (v_of s1) /\ unique_st (v_of s2)); //todo
  lem_apply_log init_st (ops_of s1)

let linearizable_gt0_s2'_noop (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Noop_second? (resolve_conflict last1 last2) /\
                     (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                     (exists l2. (v_of (inverse_st s2) == apply_log (v_of lca) l2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2))))
          (ensures eq (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2)))
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = 
  assume (unique_st (v_of lca) /\ unique_st (v_of s1) /\ unique_st (v_of s2)); //todo
  lem_apply_log init_st (ops_of s2)
  
let linearizable_gt0_s1's2'_noop_both (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Noop_both? (resolve_conflict last1 last2) /\
                     (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                     (exists l1. (v_of (inverse_st s1) == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of (inverse_st s2) == apply_log (v_of lca) l2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures eq (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()


////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = S.set nat

// init state 
let init_st_s = S.empty

let find_min_seq (s:concrete_st_s)
    : (m:option nat
           {(Some? m <==> (exists (e:(nat)). S.mem e s /\ (forall e1. S.mem e1 s ==> e <= e1))) /\
            (Some? m ==> (exists (e:(nat)). S.mem e s /\ (forall e1. S.mem e1 s ==> e <= e1) /\ e = extract_s m)) /\
        (s = S.empty ==> (m = None \/ (~ (exists (e:(nat)). S.mem e s /\ (forall e1. S.mem e1 s ==> e <= e1))))) 
        (*s <> empty ==> Some? m*)}) =
  S.find_if s (fun e -> (S.forall_s s (fun e1 -> e <= e1)))
  
let remove_min_seq (s:concrete_st_s) 
  : (r:concrete_st_s{(s = S.empty ==> r = s) /\
                   (s <> S.empty /\ Some? (find_min_seq s) ==> (forall e. S.mem e r <==> (S.mem e s /\ e <> extract_s (find_min_seq s)))) /\
                   (s <> S.empty /\ None? (find_min_seq s) ==> (forall e. S.mem e r <==> S.mem e s))}) =
  if s = S.empty then s 
  else (let m = find_min_seq s in
        if Some? m then S.remove_if s (fun e -> e = extract_s (find_min_seq s))
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
          (ensures (None? (find_min_seq st_s) <==> None? (find_min st)) /\
                   (Some? (find_min_seq st_s) <==> Some? (find_min st)) /\
                   (Some? (find_min_seq st_s) ==> extract_s (find_min_seq st_s) = snd (extract_s (find_min st)))) = admit()

let remove_same (st_s:concrete_st_s) (st:concrete_st) 
  : Lemma (requires eq_sm st_s st)
          (ensures (eq_sm (remove_min_seq st_s) (remove_min st))) =
  admit();min_same st_s st
 
//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) =
  min_same st_s st;
  remove_same st_s st;
  if Enqueue? (fst (snd op)) then () else ()
  
////////////////////////////////////////////////////////////////
