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
  |(ts, Add_after after_id ele) -> ~ (mem_id_s ts (fst s)) /\ //after_id <> ts /\                            
                                  (~ (after_id = 0) ==> mem_id_s after_id (fst s))
  |(_, Remove id) -> mem_id_s id (fst s) /\ mem_id_s id (fst s)  ///\ ~ (S.mem id (snd s))

let do_prop (s:concrete_st) (op:op_t) :
  Lemma (ensures (Add_after? (snd op) ==> (do_pre s op <==>
                           ~ (mem_id_s (fst op) (fst s)) /\ //get_after_id op <> fst op /\                          
                                  (~ ((get_after_id op) = 0) ==> mem_id_s (get_after_id op) (fst s)))) /\
                 (Remove? (snd op) ==> (do_pre s op <==>
                          mem_id_s (get_rem_id op) (fst s)))) = ()

// apply an operation to a state
let do (s:concrete_st) (op:op_t{do_pre s op}) 
  : (r:concrete_st{(*//(Add_after? (snd op) ==> (forall id. mem_id_s id (fst r) <==> mem_id_s id (fst s) \/ id = fst op)) /\
                   //(Remove? (snd op) ==> (forall id. S.mem id (snd r) <==> S.mem id (snd s) \/ id = get_rem_id op)) /\*)
                    S.subset (fst s) (fst r) /\ S.subset (snd s) (snd r)}) =
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
  |(ts1, (Add_after id1 _)), (ts2, Remove id2) -> First_then_second //(*if ts1 = id2 then*) Second_then_first (*else First_then_second*) //ts1 <> id2
  |(ts1, Remove id1), (ts2, (Add_after id2 _)) -> Second_then_first //First_then_second //ts2 <> id1
  
  |(ts1, Remove id1), (ts2, Remove id2) -> (*if id1 = id2 then First else*) First_then_second

let resolve_conflict_prop (x:op_t) (y:op_t{fst x <> fst y}) 
  : Lemma ((First_then_second? (resolve_conflict x y) <==>
                         (Add_after? (snd x) /\ Add_after? (snd y) /\ get_after_id x = get_after_id y /\ fst x > fst y) \/
                         (Add_after? (snd x) /\ Add_after? (snd y) /\ get_after_id x <> get_after_id y) \/
                         //(Add_after? (snd x) /\ Remove? (snd y) /\ fst x <> get_rem_id y) \/
                         (Add_after? (snd x) /\ Remove? (snd y)) \/
                         (Remove? (snd x) /\ Remove? (snd y))) /\
                         
           (Second_then_first? (resolve_conflict x y) <==>
                         (Add_after? (snd x) /\ Add_after? (snd y) /\ get_after_id x = get_after_id y /\ fst x < fst y) \/
                         (Remove? (snd x) /\ Add_after? (snd y)))) = ()

// concrete merge pre-condition
let merge_pre l a b =
  S.subset (fst l) (fst a) /\ S.subset (fst l) (fst b) /\
  S.subset (snd l) (snd a) /\ S.subset (snd l) (snd b) /\
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

let linearizable_s1_0' (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_s2_0' (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s2 = ops_of lca /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires do_pre_prop s l)
    (ensures (length l > 0 ==> (S.subset (fst s) (fst (apply_log s l))) /\
                              (S.subset (snd s) (snd (apply_log s l)))))
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

#push-options "--z3rlimit 100" 
let merge_pre_prop (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2)) =
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))
  (*assert (forall id. mem_id_s id (fst (v_of lca)) ==> ~ (mem_id_s id (S.difference (fst (v_of s1)) (fst (v_of lca)))));
  assert (forall id. mem_id_s id (fst (v_of lca)) ==> ~ (mem_id_s id (S.difference (fst (v_of s2)) (fst (v_of lca)))));
  assert (forall id. mem_id_s id (S.difference (fst (v_of s1)) (fst (v_of lca))) ==> 
                ~ (mem_id_s id (S.difference (fst (do (v_of s2) last2)) (fst (v_of lca)))));
  assert (forall id. mem_id_s id (S.difference (fst (do (v_of s1) last1)) (fst (v_of lca))) ==> 
                ~ (mem_id_s id (S.difference (fst (v_of s2)) (fst (v_of lca)))));
  ()*)

let lem_cond (lca s1 s2:st) (last1 last2:op_t)
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
                   (Remove? (snd last2) /\ Add_after? (snd last1) ==> fst last1 <> get_rem_id last2)) = ()

#push-options "--z3rlimit 200" 
let linearizable_gt0_s1' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  resolve_conflict_prop last1 last2;
  merge_pre_prop lca s1 s2 last1 last2;
  lem_cond lca s1 s2 last1 last2

let linearizable_gt0_s2' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    consistent_branches lca s1 s2 /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) 
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  resolve_conflict_prop last1 last2;
  merge_pre_prop lca s1 s2 last1 last2;
  lem_cond lca s1 s2 last1 last2

/////////////////////////////////////////////////////////////////////////////////




/////////////////////////////////////////////////////////////////////////////////



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
  
#push-options "--z3rlimit 400" 
let rec invalid_exec1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    Add_after? (snd last1) /\ Remove? (snd last2) /\
                    fst last1 <> fst last2)
          (ensures (fst last1 <> get_rem_id last2))
          (decreases %[length (ops_of s1); length (ops_of s2)]) = 
  if ops_of lca = ops_of s1 then
    (if ops_of lca = ops_of s2 then ()
     else 
       (let s2' = inverse_st s2 in
        let pre2, lastop2 = un_snoc (ops_of s2) in
        do_prop (v_of s2') last2; 
        lem_apply_log init_st (ops_of s2);
        inverse_helper init_st pre2 lastop2;
        assert (mem_id_s (get_rem_id last2) (fst (v_of s2')) <==> do_pre (v_of s2') last2);
        pre1_pre2_s2 lca s1 s2;
        if mem_id_s (get_rem_id last2) (fst (v_of s2')) then 
          (assert(do_pre (v_of s2') last2); 
           assume (consistent_branches lca (do_st s1 last1) (do_st s2' last2)); //can be done
           invalid_exec1 lca s1 s2' last1 last2)
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
              assume (consistent_branches lca (do_st s1 last1) (do_st s2' last2)); //can be done
              invalid_exec1 lca s1 s2' last1 last2))))
  else 
    (let s1' = inverse_st s1 in 
     assume (consistent_branches_s1_gt0 lca s1 s2);
     let pre1, lastop1 = un_snoc (ops_of s1) in
     do_prop (v_of s1') last1; //include it if needed
     lem_apply_log init_st (ops_of s1);
     inverse_helper init_st pre1 lastop1;
     pre1_pre2_s1 lca s1 s2;
     assume (fst lastop1 <> fst last1); //can be done
     if Add_after? (snd lastop1) && fst lastop1 <> get_after_id last1 then 
       (assert (not (mem_id_s (fst last1) (fst (v_of s1'))));
        assert (do_pre (v_of s1') last1);
        assume (consistent_branches lca (do_st s1' last1) (do_st s2 last2)); //can be done
        invalid_exec1 lca s1' s2 last1 last2)
     else if Add_after? (snd lastop1) && fst lastop1 = get_after_id last1 then  //check this case with full do_pre for add
       admit()
     else if Remove? (snd lastop1) && get_rem_id lastop1 <> fst last1 then
       (assert (do_pre (v_of s1') last1); 
        assume (consistent_branches lca (do_st s1' last1) (do_st s2 last2)); //can be done
        invalid_exec1 lca s1' s2 last1 last2)
     else ()) //Remove? (snd lastop1) && get_rem_id lastop1 = fst last1


let rec invalid_exec2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    Add_after? (snd last1) /\ Add_after? (snd last2) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2))
          (ensures fst last1 <> get_after_id last2 (* /\ fst last2 <> get_after_id last1*))
          (decreases %[length (ops_of s1); length (ops_of s2)]) = 
  if ops_of lca = ops_of s1 then
    (if ops_of lca = ops_of s2 then () //done
     else 
       (let s2' = inverse_st s2 in
        let pre2, lastop2 = un_snoc (ops_of s2) in
        do_prop (v_of s2') last2; //include it if needed
        lem_apply_log init_st (ops_of s2);
        inverse_helper init_st pre2 lastop2;
        pre1_pre2_s2 lca s1 s2;
        assume (fst lastop2 <> fst last2); //can be done
        if Remove? (snd lastop2) then
          (assert (do_pre (v_of s2') last2); 
           pre1_pre2_s2 lca s1 s2;
           assume (consistent_branches lca (do_st s1 last1) (do_st s2' last2)); //can be done
           invalid_exec2 lca s1 s2' last1 last2)
        else if Add_after? (snd lastop2) && fst lastop2 <> get_after_id last2 then
          (assert (do_pre (v_of s2') last2); //done
           pre1_pre2_s2 lca s1 s2;
           assume (consistent_branches lca (do_st s1 last1) (do_st s2' last2)); //can be done
           invalid_exec2 lca s1 s2' last1 last2)
        else 
          (lem_diff (snoc (ops_of s2) last2) (ops_of lca);
           lem_diff (ops_of s2) (ops_of lca); 
           lemma_append_count_assoc_fst (ops_of s2) (create 1 last2);
           assert (mem_id (fst lastop2) (diff (snoc (ops_of s2) last2) (ops_of lca)));
           lemma_mem_append (ops_of s1) (create 1 last1);
           assert (snoc (ops_of s1) last1 == Seq.append (ops_of s1) (create 1 last1));
           lemma_append_count_assoc_fst (ops_of s1) (create 1 last1);
           assert (mem_id (fst last1) (snoc (ops_of s1) last1));
           lem_diff (snoc (ops_of s1) last1) (ops_of lca);
           assert (mem_id (fst last1) (diff (snoc (ops_of s1) last1) (ops_of lca)));
           ())))
  else 
    (let s1' = inverse_st s1 in 
     assert (consistent_branches_s1_gt0 lca s1 s2);
     let pre1, lastop1 = un_snoc (ops_of s1) in
     do_prop (v_of s1') last1; //include it if needed
     lem_apply_log init_st (ops_of s1);
     inverse_helper init_st pre1 lastop1;
     pre1_pre2_s1 lca s1 s2;
     assume (fst lastop1 <> fst last1); //can be done
     if Remove? (snd lastop1) then 
       (assert (do_pre (v_of s1') last1); //done
        assume (consistent_branches lca (do_st s1' last1) (do_st s2 last2)); //can be done
        invalid_exec2 lca s1' s2 last1 last2)
     else if Add_after? (snd lastop1) && fst lastop1 <> get_after_id last1 then 
       (assert (do_pre (v_of s1') last1); //done
        assume (consistent_branches lca (do_st s1' last1) (do_st s2 last2)); //can be done
        invalid_exec2 lca s1' s2 last1 last2)
     else 
       admit())

///////////////////////////////////////////////////////////////////



(*let merge_prop (lca s1:st) (last1:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\
                    distinct_ops (ops_of lca) /\ distinct_ops (ops_of s1) /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (snoc (ops_of s1) last1) /\ 
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (snoc (ops_of s1) last1) (ops_of lca)) ==> lt id id1) /\
                    S.subset (fst (v_of lca)) (fst (do (v_of s1) last1)) /\
                    S.subset (snd (v_of lca)) (snd (do (v_of s1) last1)))
          (ensures S.subset (fst (v_of lca)) (fst (v_of s1)) /\
                   S.subset (snd (v_of lca)) (snd (v_of s1))) =
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

#push-options "--z3rlimit 300" 
let check (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    //merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2))
          (ensures (Add_after? (snd last1) /\ Add_after? (snd last2) ==>
                      fst last1 <> get_after_id last2 (*/\ fst last2 <> get_after_id last1*))) = ()//(Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1)) = ()

let check' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2))
          (ensures (Add_after? (snd last1) /\ Add_after? (snd last2) ==>
                      fst last2 <> get_after_id last1)) = 
  check lca s2 s1 last2 last1

let check'' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    //merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2))
          (ensures (Add_after? (snd last1) /\ Add_after? (snd last2) ==>
                      fst last2 <> get_after_id last1)) = ()
                      
let check1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2))
          (ensures (Remove? (snd last2) /\ Add_after? (snd last1) ==> fst last1 <> get_rem_id last2)) = ()
                      
let rec invalid_exec (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2)
          (ensures (Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1) /\
                   (Remove? (snd last2) /\ Add_after? (snd last1) ==> fst last1 <> get_rem_id last2) /\
                   (Add_after? (snd last1) /\ Add_after? (snd last2) ==>
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1)) = 
  if Add_after? (snd last1) && Remove? (snd last2) then
    invalid_exec1 lca s1 s2 last1 last2
  else 
    (assume ((Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1) /\
             (Add_after? (snd last1) /\ Add_after? (snd last2) ==>
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1));
     ())
  

#push-options "--z3rlimit 100" //with subset pre
let linearizable_gt0_s1' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    //is_prefix (ops_of lca) (ops_of s2) /\
                    fst last1 <> fst last2 /\
                    //First_then_second? (resolve_conflict last1 last2) /\
                    //Remove? (snd last1) /\ Remove? (snd last2) /\ //all done
                    Add_after? (snd last1) /\ Remove? (snd last2) /\
                    //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 <> get_after_id last2 /\
                    //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 = get_after_id last2 /\ fst last1 > fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2))
          (ensures //merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\ //only w/o subset pre
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 (*/\ //only with subset pre
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)*)) = 
  invalid_exec lca s1 s2 last1 last2
  (*assert ((Remove? (snd last2) /\ Add_after? (snd last1) ==> fst last1 <> get_rem_id last2) /\
          (Add_after? (snd last1) /\ Add_after? (snd last2) ==>
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1));*)
  ()

let linearizable_gt0_s2' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    consistent_branches lca s1 s2 /\
                    //is_prefix (ops_of lca) (ops_of s1) /\
                    fst last1 <> fst last2 /\
                    //Second_then_first? (resolve_conflict last1 last2) /\
                    Remove? (snd last1) /\ Add_after? (snd last2) /\
  //                  Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 = get_after_id last2 /\ fst last1 < fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2))
                    //do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) 
          (ensures //merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 (*/\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)*)) =
  //invalid_exec lca s1 s2 last1 last2;
  assert ((Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1) /\
          (Add_after? (snd last1) /\ Add_after? (snd last2) ==>
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1));
  ()*)
