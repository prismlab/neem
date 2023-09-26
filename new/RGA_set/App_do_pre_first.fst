module App_do_pre_first

module S = Set_extended

// the set has entries with unique timestamps 
let unique_st (s:S.set (nat & (nat & nat))) =
  S.forall_s s (fun e -> not (S.exists_s s (fun e1 -> snd e <> snd e1 && fst e = fst e1)))

let mem_id_s (id:nat) (s:S.set (nat & (nat & nat))) 
  : (r:bool {s = S.empty ==> r == false}) =
  S.exists_s s (fun e -> fst e = id)

#set-options "--query_stats"
// the concrete state type
type concrete_st = s:(S.set (nat & (nat & nat)) & S.set nat) {unique_st (fst s) /\
                                                      (forall id. S.mem id (snd s) ==> mem_id_s id (fst s))}
                   // first ele of the pair is a tuple of timestamp, 
                   //     id after which the ele is to be inserted and ele to be inserted
                   // second ele of the pair is a tombstone set

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
// (the only operation is Add, so nat is fine)
type app_op_t:eqtype = 
  |Add_after : after_id:nat -> ele:nat -> app_op_t //inserts ele after after_id
  |Remove : id:pos -> app_op_t //removes the element with identifier id

let get_ele (op:op_t{Add_after? (snd op)}) : nat =
  let (_, Add_after _ ele) = op in ele

let get_after_id (op:op_t{Add_after? (snd op)}) : nat =
  let (_, Add_after id _) = op in id

let get_rem_id (op:op_t{Remove? (snd op)}) : pos =
  let (_, Remove id) = op in id

let do_pre (s:concrete_st) (op:op_t) : prop =
  match op with
  |(ts, Add_after after_id ele) -> ~ (mem_id_s ts (fst s)) /\                      
                                  (~ (after_id = 0) ==> mem_id_s after_id (fst s))
  |(_, Remove id) -> mem_id_s id (fst s) /\ mem_id_s id (fst s) 

let do_prop (s:concrete_st) (op:op_t) :
  Lemma (ensures (Add_after? (snd op) ==> (do_pre s op <==>
                           ~ (mem_id_s (fst op) (fst s)) /\                      
                                  (~ ((get_after_id op) = 0) ==> mem_id_s (get_after_id op) (fst s)))) /\
                 (Remove? (snd op) ==> (do_pre s op <==>
                          mem_id_s (get_rem_id op) (fst s)))) = ()

// apply an operation to a state
let do (s:concrete_st) (op:op_t{do_pre s op}) 
  : (r:concrete_st{S.subset (fst s) (fst r) /\ S.subset (snd s) (snd r)}) =
   match op with
  |(ts, Add_after after_id ele) -> (S.add (ts, (after_id, ele)) (fst s), snd s)
  |(_, Remove id) -> (fst s, S.add id (snd s))

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b /\ do_pre a op)
           (ensures eq (do a op) (do b op)) = ()

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res = 
  match x, y with
  |(ts1, (Add_after id1 _)), (ts2, (Add_after id2 _)) -> if id1 = id2 then 
                                                           if ts1 > ts2 then First_then_second else Second_then_first 
                                                        else First_then_second //ts1 <> id2 /\ ts2 <> id1
  |(ts1, (Add_after id1 _)), (ts2, Remove id2) -> First_then_second 
  |(ts1, Remove id1), (ts2, (Add_after id2 _)) -> Second_then_first 
  |(ts1, Remove id1), (ts2, Remove id2) -> First_then_second

let resolve_conflict_prop (x:op_t) (y:op_t{fst x <> fst y}) 
  : Lemma ((First_then_second? (resolve_conflict x y) <==>
                         (Add_after? (snd x) /\ Add_after? (snd y) /\ get_after_id x = get_after_id y /\ fst x > fst y) \/
                         (Add_after? (snd x) /\ Add_after? (snd y) /\ get_after_id x <> get_after_id y) \/
                         (Add_after? (snd x) /\ Remove? (snd y)) \/
                         (Remove? (snd x) /\ Remove? (snd y))) /\
                         
           (Second_then_first? (resolve_conflict x y) <==>
                         (Add_after? (snd x) /\ Add_after? (snd y) /\ get_after_id x = get_after_id y /\ fst x < fst y) \/
                         (Remove? (snd x) /\ Add_after? (snd y)))) = ()

// concrete merge pre-condition
let merge_pre l a b =
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
          (ensures (Add_after? (snd last1) /\ Add_after? (snd last2) ==>
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1) /\
                   (Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1) /\
                   (Remove? (snd last2) /\ Add_after? (snd last1) ==> fst last1 <> get_rem_id last2)) = 
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
  resolve_conflict_prop last1 last2;
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
  resolve_conflict_prop last1 last2;
  subset_prop lca (do_st s1 last1) (do_st s2 last2);
  subset_prop lca s1 s2;
  lem_lastop lca s1 s2 last1 last2

/////////////////////////////////////////////////////////////////////////////////




/////////////////////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 200" 
let rec invalid_exec1 (lca s1 s2:st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2) last2 /\ 
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    Remove? (snd last2))
          (ensures (length (ops_of s1) > length (ops_of lca) ==> 
                    (let _, last1 = un_snoc (ops_of s1) in
                      (Add_after? (snd last1) ==>
                           fst last1 <> get_rem_id last2))))
          (decreases %[length (ops_of s1); length (ops_of s2)]) =
  if ops_of lca = ops_of s1 then () //done
  else 
    (let s1' = inverse_st s1 in
     let pre1, last1 = un_snoc (ops_of s1) in
     lem_apply_log init_st (ops_of s1);
     inverse_helper init_st pre1 last1;
     if ops_of lca = pre1 then 
       (if ops_of lca = ops_of s2 then () ///done
        else 
          (let s2' = inverse_st s2 in
          let pre2, lastop2 = un_snoc (ops_of s2) in
          do_prop (v_of s2') last2; 
          lem_apply_log init_st (ops_of s2);
          inverse_helper init_st pre2 lastop2;
          //assert (mem_id_s (get_rem_id last2) (fst (v_of s2')) <==> do_pre (v_of s2') last2);
          pre1_pre2_s2 lca s1 s2;
          if mem_id_s (get_rem_id last2) (fst (v_of s2')) then 
            (assert(do_pre (v_of s2') last2);
             assume (consistent_branches lca s1 (do_st s2' last2)); //can be done
             invalid_exec1 lca s1 s2' last2)
          else 
            (assert (not (mem_id_s (get_rem_id last2) (fst (v_of s2'))));
            if Add_after? (snd lastop2) && fst lastop2 = get_rem_id last2 then 
              (lem_diff (snoc (ops_of s2) last2) (ops_of lca);
                lem_diff (ops_of s2) (ops_of lca); 
                assert (mem_id (fst lastop2) (diff (ops_of s2) (ops_of lca)));
                assert (not (mem_id (fst lastop2) (ops_of lca)));
                assert (mem_id (fst lastop2) (ops_of s2));
                lemma_append_count_assoc_fst (ops_of s2) (create 1 last2);
                assert (mem_id (fst lastop2) (snoc (ops_of s2) last2)); 
                assert (mem_id (fst lastop2) (diff (snoc (ops_of s2) last2) (ops_of lca)));
                lem_diff (snoc (ops_of s1) last1) (ops_of lca);
                assert (mem_id (fst last1) (diff (snoc (ops_of s1) last1) (ops_of lca))); 
                ()) 
            else 
              (assert (do_pre (v_of s2') last2);
               assume (consistent_branches lca s1 (do_st s2' last2)); //can be done
               invalid_exec1 lca s1 s2' last2))))
     else 
       (let s1'' = inverse_st s1' in
        let pre1', last1' = un_snoc pre1 in
        lem_apply_log init_st pre1;
        inverse_helper init_st pre1' last1';
        if Add_after? (snd last1) && Add_after? (snd last1') && fst last1' = get_after_id last1 then //done
         (assert (do_pre (v_of s1'') (fst last1, snd last1')); //done
          assume (consistent_branches lca (do_st s1'' (fst last1, snd last1')) (do_st s2 last2) /\ //can be done
                  consistent_branches lca (do_st s1'' (fst last1, snd last1')) s2); //can be done
          invalid_exec1 lca (do_st s1'' (fst last1, snd last1')) s2 last2)
        else if Add_after? (snd last1) && Add_after? (snd last1') && fst last1' <> get_after_id last1 then //done
          (assert (not (mem_id_s (fst last1) (fst (v_of s1'')))); //done
           assert (do_pre (v_of s1'') last1); //done
           assume (consistent_branches lca (do_st s1'' last1) (do_st s2 last2) /\ //can be done
                   consistent_branches lca (do_st s1'' last1) s2); //can be done
           invalid_exec1 lca (do_st s1'' last1) s2 last2)
        else if Remove? (snd last1') && Add_after? (snd last1) && get_rem_id last1' <> fst last1 then //done
          (assert (do_pre (v_of s1'') last1); //done
           assume (consistent_branches lca (do_st s1'' last1) (do_st s2 last2) /\ //can be done
                   consistent_branches lca (do_st s1'' last1) s2); //can be done
           invalid_exec1 lca (do_st s1'' last1) s2 last2)
        else 
          ())) //done

let rec invalid_exec2 (lca s1 s2:st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2) last2 /\ 
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    Add_after? (snd last2))
          (ensures (length (ops_of s1) > length (ops_of lca) ==> 
                    (let _, last1 = un_snoc (ops_of s1) in
                      (Add_after? (snd last1) ==>
                           fst last1 <> get_after_id last2))))
          (decreases %[length (ops_of s1); length (ops_of s2)]) =
  if ops_of lca = ops_of s1 then () //done
  else 
    (let s1' = inverse_st s1 in
     let pre1, last1 = un_snoc (ops_of s1) in
     lem_apply_log init_st (ops_of s1);
     inverse_helper init_st pre1 last1;
     if ops_of lca = pre1 then 
       (if ops_of lca = ops_of s2 then () ///done
        else 
          (let s2' = inverse_st s2 in
          let pre2, lastop2 = un_snoc (ops_of s2) in
          do_prop (v_of s2') last2; 
          lem_apply_log init_st (ops_of s2);
          inverse_helper init_st pre2 lastop2;
          //assert (mem_id_s (get_rem_id last2) (fst (v_of s2')) <==> do_pre (v_of s2') last2);
          pre1_pre2_s2 lca s1 s2;
          if Remove? (snd lastop2) then //done
            (assert (do_pre (v_of s2') last2); //done
             assume (consistent_branches lca s1 (do_st s2' last2)); //can be done
             invalid_exec2 lca s1 s2' last2)
          else if Add_after? (snd lastop2) && fst lastop2 <> get_after_id last2 then //todo
            (assert (do_pre (v_of s2') last2); //done
             assume (consistent_branches lca s1 (do_st s2' last2)); //can be done
             invalid_exec2 lca s1 s2' last2)
          else 
            (assert (Add_after? (snd lastop2) && fst lastop2 = get_after_id last2); 
            lem_diff (snoc (ops_of s2) last2) (ops_of lca);
            lem_diff (ops_of s2) (ops_of lca); 
            lemma_append_count_assoc_fst (ops_of s2) (create 1 last2);
            assert (mem_id (fst lastop2) (diff (snoc (ops_of s2) last2) (ops_of lca))); 
            assert (mem_id (fst last1) (diff (ops_of s1) (ops_of lca)));
            ())))
     else 
       (let s1'' = inverse_st s1' in
        let pre1', last1' = un_snoc pre1 in
        lem_apply_log init_st pre1;
        inverse_helper init_st pre1' last1';
        if Remove? (snd last1') then //done
          (assert (do_pre (v_of s1'') last1); //done
           assume (consistent_branches lca (do_st s1'' last1) (do_st s2 last2) /\ //can be done
                   consistent_branches lca (do_st s1'' last1) s2); //can be done
           invalid_exec2 lca (do_st s1'' last1) s2 last2)
        else if Add_after? (snd last1') && Add_after? (snd last1) && fst last1' <> get_after_id last1 then 
          (assert (do_pre (v_of s1'') last1); //done
           assume (consistent_branches lca (do_st s1'' last1) (do_st s2 last2) /\ //can be done
                   consistent_branches lca (do_st s1'' last1) s2); //can be done
           invalid_exec2 lca (do_st s1'' last1) s2 last2)
        else if Add_after? (snd last1') && Add_after? (snd last1) && fst last1' = get_after_id last1 then //done
          (assert (do_pre (v_of s1'') (fst last1, snd last1')); //done
           assume (consistent_branches lca (do_st s1'' (fst last1, snd last1')) (do_st s2 last2) /\ //can be done
                   consistent_branches lca (do_st s1'' (fst last1, snd last1')) s2); //can be done
           invalid_exec2 lca (do_st s1'' (fst last1, snd last1')) s2 last2)
        else ())) //done

///////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

module L = FStar.List.Tot

// the concrete state 
type concrete_st_s' = list (timestamp_t * nat)

// init state 
let init_st_s' = []

(*let do_pre_mrdt (s:concrete_st) (op:op_t) =
  match op with
  |(ts, Add_after after_id ele) -> ~ (mem_id_s ts (fst s) \/ S.mem ts (snd s)) /\
                                  (~ (after_id = 0) ==> mem_id_s after_id (fst s))
  |(_, Remove id) -> mem_id_s id (fst s) /\ ~ (S.mem id (snd s))*)

let mem_id_s' (id:nat) (s:concrete_st_s') =
  exists e. L.mem e s /\ fst e = id

let do_pre' (s:concrete_st_s') (op:op_t) =
  match op with
  |(ts, Add_after after_id ele) -> ~ (mem_id_s' ts s) /\
                                  (~ (after_id = 0) ==> mem_id_s' after_id s)
  |(_, Remove id) -> mem_id_s' id s

let rec add (s:concrete_st_s') (op:op_t{Add_after? (snd op) /\ mem_id_s' (get_after_id op) s}) 
  : (r:concrete_st_s'{(forall id. mem_id_s' id r <==> mem_id_s' id s \/ id = fst op)}) =
  match s with
  |[x] -> x::[fst op, get_ele op]
  |x::xs -> if fst x = get_after_id op then x::(L.append [(fst op, get_ele op)] xs) else x::add xs op

let rec remove (s:concrete_st_s') (id:timestamp_t) 
  : (r:concrete_st_s'{(forall e. L.mem e r <==> L.mem e s /\ fst e <> id)}) =
  match s with
  |[] -> []
  |x::xs -> if fst x = id then remove xs id else x::remove xs id

// apply an operation to a state 
let do_s' (s:concrete_st_s') (op:op_t{do_pre' s op}) 
  : (r:concrete_st_s'{Add_after? (snd op) ==> (forall id. mem_id_s' id r <==> mem_id_s' id s \/ id = fst op)}) =
  match op with
  |(ts, Add_after after_id ele) -> if after_id = 0 then (fst op, get_ele op)::s else add s op
  |(_, Remove id) -> remove s (get_rem_id op)

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm' (st_s:concrete_st_s') (st:concrete_st) = 
  (forall id. mem_id_s' id st_s <==> (mem_id_s id (fst st) /\ not (S.mem id (snd st))))
  
//initial states are equivalent
let initial_eq' _
  : Lemma (ensures eq_sm' init_st_s' init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq' (st_s:concrete_st_s') (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm' st_s st /\ do_pre st op /\ do_pre' st_s op) 
          (ensures eq_sm' (do_s' st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////
//// Linearization properties - intermediate merge //////

let prop1 (l:concrete_st) (o1 o2 o3:op_t) // cond1
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second /\
                    do_pre l o1 /\ do_pre l o3 /\ do_pre (do l o1) o2 /\ do_pre (do (do l o3) o1) o2)
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

let prop2 (s s':concrete_st) (o1 o2:op_t) //cond2
  : Lemma (requires do_pre s o2 /\ do_pre s' o2 /\ do_pre s o1 /\ do_pre s' o1 /\
                    do_pre (do s o1) o2 /\ merge_pre s (do s o2) s' /\
                    eq (concrete_merge s (do s o2) s') (do s' o2))
          (ensures eq (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

let prop3 (l a b c:concrete_st) (op op':op_t) //cond3
  : Lemma 
    (requires merge_pre l a b /\ eq (concrete_merge l a b) c /\ 
              do_pre b op /\ do_pre c op /\ do_pre (do b op) op' /\ do_pre (do c op) op' /\
              (forall (o:op_t). do_pre b o /\ do_pre c o ==> eq (concrete_merge l a (do b o)) (do c o)))
              //fst op <> fst op'
    (ensures eq (concrete_merge l a (do (do b op) op')) (do (do c op) op')) = ()

let prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t) //automatic //cond5
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o3' /\ fst o2 <> fst o3 /\ fst o2 <> fst o3' /\
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second /\
                    do_pre l o1 /\ do_pre s o3 /\ do_pre (do l o1) o2 /\ //do_pre (do s o3) o1 /\
                    do_pre s o3' /\ do_pre (do s o3') o3 /\ do_pre (do (do s o3') o3) o1 /\
                    do_pre (do (do (do s o3') o3) o1) o2 /\
                    do_pre (do s o3) o1 /\ do_pre (do (do s o3) o1) o2 /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do s o3) o1) /\
                    //   merge_pre (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1) /\
                    //o3.o1, o3.o2
                    eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                      (do (do (do (do s o3') o3) o1) o2)) = ()

let rec_merge (s si si' sn sn':concrete_st)
  : Lemma (requires merge_pre s sn sn' /\ merge_pre si sn sn' /\ merge_pre si' sn sn' /\ 
                    merge_pre s sn si' /\ merge_pre s si sn' /\
                    merge_pre s si si' /\ merge_pre s si' si /\ 
                    merge_pre si sn (concrete_merge s si si') /\ merge_pre si' sn' (concrete_merge s si' si) /\
                    merge_pre (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn) /\
                    merge_pre si sn (concrete_merge s si sn') /\ merge_pre si' (concrete_merge s sn si') sn' /\
                    
                    eq (concrete_merge s sn sn') (concrete_merge si sn (concrete_merge s si sn')) /\
                    eq (concrete_merge s sn sn') (concrete_merge si' (concrete_merge s sn si') sn') /\
                    eq (concrete_merge s sn si') (concrete_merge si sn (concrete_merge s si si')) /\
                    eq (concrete_merge s si sn') (concrete_merge si' sn' (concrete_merge s si' si)))
         
          (ensures (eq (concrete_merge s sn sn')
                       (concrete_merge (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn)))) = ()
                       
let rec_merge1 (s si si' sn sn':concrete_st)
  : Lemma (requires merge_pre s sn sn' /\ merge_pre si sn sn' /\ merge_pre si' sn sn' /\ 
                    merge_pre s sn si' /\ merge_pre s si sn' /\
                    merge_pre s si si' /\ merge_pre s si' si /\ 
                    merge_pre si sn (concrete_merge s si si') /\ merge_pre si' sn' (concrete_merge s si' si) /\
                    merge_pre (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn) /\
                    eq (concrete_merge s sn sn') (concrete_merge si sn sn') /\
                    eq (concrete_merge s sn sn') (concrete_merge si' sn sn') /\
                    eq (concrete_merge s sn si') (concrete_merge si sn (concrete_merge s si si')) /\
                    eq (concrete_merge s si sn') (concrete_merge si' sn' (concrete_merge s si' si)))
          (ensures (eq (concrete_merge s sn sn')
                       (concrete_merge (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn)))) = ()
          
////////////////////////////////////////////////////////////////
