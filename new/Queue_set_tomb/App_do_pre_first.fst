module App_do_pre_first

module S = Set_extended
  
let unique_st (s:S.set (nat & nat)) =
  S.forall_s s (fun e -> not (S.exists_s s (fun e1 -> snd e <> snd e1 && fst e = fst e1)))
  
let mem_id_s (id:nat) (s:S.set (nat & nat))
  : (r:bool {s = S.empty ==> r == false}) =
  S.exists_s s (fun e -> fst e = id)

// the concrete state type
// It is a set of pairs of timestamp and element.
type concrete_st = s:(S.set (nat & nat) & S.set nat) {unique_st (fst s) /\
                                                (forall id. S.mem id (snd s) ==> mem_id_s id (fst s))}

// init state
let init_st = (S.empty, S.empty)

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  S.equal (fst a) (fst b) /\
  S.equal (snd a) (snd b)

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
  | Dequeue : option nat -> app_op_t

let get_ele (o:op_t{Enqueue? (snd o)}) : nat =
  match o with
  |(_, (Enqueue x)) -> x

let can_deq (o:op_t{Dequeue? (snd o)}) =
  match o with
  |(_, Dequeue (Some _)) -> true
  |_ -> false

let get_rem_ele (op:op_t{Dequeue? (snd op) /\ can_deq op}) =
  let (_, Dequeue (Some ele)) = op in ele

let do_pre (s:concrete_st) (op:op_t) : prop =
  match op with
  |(ts, Enqueue ele) -> ~ (mem_id_s ts (fst s))
  |(_, Dequeue ele) -> (can_deq op ==> mem_id_s (get_rem_ele op) (fst s))
  
// apply an operation to a state
let do (s:concrete_st) (op:op_t{do_pre s op}) : concrete_st =
  match op with
  |(id, (Enqueue x)) -> (S.add (id, x) (fst s), snd s)
  |(_, (Dequeue x)) -> if can_deq op then (fst s, S.add (get_rem_ele op) (snd s)) else s

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b /\ do_pre a op)
           (ensures eq (do a op) (do b op)) = ()
  
//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  match x, y with
  |(_,(Enqueue _)), (_,(Enqueue _)) -> if fst x < fst y then Second_then_first else First_then_second
  |_, (_, (Dequeue None)) -> Second_then_first
  |(_, (Dequeue None)), _ -> First_then_second
  |(_, (Dequeue None)), (_, (Dequeue None)) -> First_then_second
  |(_,(Enqueue _)), (_, (Dequeue None)) -> Second_then_first
  |(_,(Dequeue (Some _))), (_,(Enqueue _)) -> First_then_second 
  |(_,(Dequeue (Some _))), (_,(Dequeue (Some _))) -> First_then_second
  |(_,(Enqueue _)), (_,(Dequeue (Some _))) -> First_then_second

// concrete merge pre-condition
let merge_pre (l a b:concrete_st) =
  (forall id. mem_id_s id (fst l) ==> ~ (mem_id_s id (S.difference (fst a) (fst l)))) /\
  (forall id. mem_id_s id (fst l) ==> ~ (mem_id_s id (S.difference (fst b) (fst l)))) /\
  (forall id. mem_id_s id (S.difference (fst a) (fst l)) ==> ~ (mem_id_s id (S.difference (fst b) (fst l)))) 
  
let concrete_merge (lca s1:concrete_st) (s2:concrete_st{merge_pre lca s1 s2}) : concrete_st =
   (S.union (fst lca) (S.union (fst s1) (fst s2)),   
    S.union (snd lca) (S.union (snd s1) (snd s2)))

// Prove that merge is commutative
let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures merge_pre (v_of lca) (v_of s2) (v_of s1) /\
                   (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = ()  

let pre1_pre2_s2 (lca s1 s2:st)
    : Lemma (requires consistent_branches_s2_gt0 lca s1 s2)
            (ensures consistent_branches lca s1 (inverse_st s2)) = 
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2);
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2)

let pre1_pre2_s1 (lca s1 s2:st)
    : Lemma (requires consistent_branches_s1_gt0 lca s1 s2)
            (ensures consistent_branches lca (inverse_st s1) s2) = 
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s1);
  inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2)

#push-options "--z3rlimit 100"
let rec linearizable_s1_0' (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) 
          (decreases length (ops_of s2)) =
  if ops_of s2 = ops_of lca then ()
  else 
    (let s2' = inverse_st s2 in
     pre1_pre2_s2 lca s1 s2; 
     linearizable_s1_0' lca s1 s2')

let rec linearizable_s2_0' (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s2 = ops_of lca /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))
          (decreases length (ops_of s1)) =
  if ops_of s1 = ops_of lca then ()
  else 
    (let s1' = inverse_st s1 in
     pre1_pre2_s1 lca s1 s2; 
     linearizable_s2_0' lca s1' s2)

let rec subset_s1 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (S.subset (fst (v_of lca)) (fst (v_of s1))) /\
                   (S.subset (snd (v_of lca)) (snd (v_of s1))))
          (decreases length (ops_of s1)) =
  if ops_of s1 = ops_of lca then ()
  else 
    (let s1' = inverse_st s1 in
     pre1_pre2_s1 lca s1 s2; 
     subset_s1 lca s1' s2)

let rec subset_s2 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (S.subset (fst (v_of lca)) (fst (v_of s2))) /\
                   (S.subset (snd (v_of lca)) (snd (v_of s2))))
          (decreases length (ops_of s2)) =
  if ops_of s2 = ops_of lca then ()
  else 
    (let s2' = inverse_st s2 in
     pre1_pre2_s2 lca s1 s2; 
     subset_s2 lca s1 s2')

let subset_prop (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (S.subset (fst (v_of lca)) (fst (v_of s1))) /\
                   (S.subset (snd (v_of lca)) (snd (v_of s1))) /\
                   (S.subset (fst (v_of lca)) (fst (v_of s2))) /\
                   (S.subset (snd (v_of lca)) (snd (v_of s2)))) =
  subset_s1 lca s1 s2;
  subset_s2 lca s1 s2
  
#push-options "--z3rlimit 400" 
let lem_lastop (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2))
          (ensures ((Dequeue? (snd last1) /\ can_deq last1 /\ Enqueue? (snd last2)) ==> fst last2 <> get_rem_ele last1) /\
                   ((Dequeue? (snd last2) /\ can_deq last2 /\ Enqueue? (snd last1)) ==> fst last1 <> get_rem_ele last2)) = 
  subset_prop lca (do_st s1 last1) (do_st s2 last2);
  subset_prop lca s1 s2

let linearizable_gt0_s1' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    //is_prefix (ops_of lca) (ops_of s2) /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =
  subset_prop lca (do_st s1 last1) (do_st s2 last2);
  subset_prop lca s1 s2;
  lem_lastop lca s1 s2 last1 last2

let linearizable_gt0_s2' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    consistent_branches lca s1 s2 /\
                    //is_prefix (ops_of lca) (ops_of s1) /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    //Remove? (snd last1) /\ Add_after? (snd last2) /\
                    //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 = get_after_id last2 /\ fst last1 < fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  subset_prop lca (do_st s1 last1) (do_st s2 last2);
  subset_prop lca s1 s2;
  lem_lastop lca s1 s2 last1 last2
  
