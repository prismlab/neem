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

(*let do_pre (s:concrete_st) (op:op_t) : prop =
  match op with
  |(ts, Add_after after_id ele) -> ~ (mem_id_s ts (fst s)) /\                            
                                  (~ (after_id = 0) ==> mem_id_s after_id (fst s))
  |(_, Remove id) -> mem_id_s id (fst s) /\ ~ (S.mem id (snd s))*)
  
let do_pre (s:concrete_st) (op:op_t) : prop =
  match op with
  |(ts, Add_after after_id ele) -> ~ (mem_id_s ts (fst s))                               
                                  //(~ (after_id = 0) ==> mem_id_s after_id (fst s))
  |(ts, Remove id) -> True //mem_id_s id (fst s) /\ ~ (S.mem id (snd s))

// apply an operation to a state
(*let do (s:concrete_st) (op:op_t{do_pre s op}) 
  : (r:concrete_st{(Add_after? (snd op) ==> (forall id. mem_id_s id (fst r) <==> mem_id_s id (fst s) \/ id = fst op)) /\
                   (Remove? (snd op) ==> (forall id. S.mem id (snd r) <==> S.mem id (snd s) \/ id = get_rem_id op)) /\
                   S.subset (fst s) (fst r) /\ S.subset (snd s) (snd r)}) =
   match op with
  |(ts, Add_after after_id ele) -> (S.add (ts, (after_id, ele)) (fst s), snd s)
  |(_, Remove id) -> (fst s, S.add id (snd s))*)
  
let do (s:concrete_st) (op:op_t{do_pre s op}) : (r:concrete_st{S.subset (fst s) (fst r) /\ S.subset (snd s) (snd r)}) =  
 
  match op with
  |(ts, Add_after after_id ele) -> if (after_id <> 0 && not (mem_id_s after_id (fst s)))then s 
                                  else (S.add (ts, (after_id, ele)) (fst s), snd s)
  
  |(_, Remove id) -> if mem_id_s id (fst s) (*&& not (S.mem id (snd s))*) then (fst s, S.add id (snd s)) else s
  
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
  //S.subset (fst l) (fst a) /\ S.subset (fst l) (fst b) /\
  //S.subset (snd l) (snd a) /\ S.subset (snd l) (snd b) /\
  (forall id. mem_id_s id (fst l) ==> ~ (mem_id_s id (S.difference (fst a) (fst l)))) /\
  (forall id. mem_id_s id (fst l) ==> ~ (mem_id_s id (S.difference (fst b) (fst l)))) /\
  (forall id. mem_id_s id (S.difference (fst a) (fst l)) ==> ~ (mem_id_s id (S.difference (fst b) (fst l))))

let concrete_merge (lca s1:concrete_st) (s2:concrete_st{merge_pre lca s1 s2}) : concrete_st =
  (*(S.union (S.intersect (fst lca) (S.intersect (fst s1) (fst s2))) 
           (S.union (S.difference (fst s1) (fst lca)) (S.difference (fst s2) (fst lca))),
   S.union (snd lca) (S.union (snd s1) (snd s2)))*)
  
   (*S.union (fst lca)
           (S.union (S.difference (fst s1) (fst lca)) (S.difference (fst s2) (fst lca))),*)
   
   (S.union (fst lca) (S.union (fst s1) (fst s2)),   
    S.union (snd lca) (S.union (snd s1) (snd s2)))
  
// Prove that merge is commutative
let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures merge_pre (v_of lca) (v_of s2) (v_of s1) /\
                   (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = ()           
                      
let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

#push-options "--z3rlimit 100"
let linearizable_s1_0''_do_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    ops_of s1 = ops_of lca /\                    
                    fst last2 > 0 /\
                    length (ops_of s2') > 0)
         
          (ensures do_pre (v_of (inverse_st s2')) last2) = ()

let linearizable_s1_0''_base_merge_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\ 
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    fst last2 > 0 /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    length (ops_of s2') > 0 /\
                    do_pre (v_of (inverse_st s2')) last2)

          (ensures (let l' = inverse_st lca in
                    merge_pre (v_of l') (v_of l') (do (v_of l') last2))) = ()

let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
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

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()
          
#push-options "--z3rlimit 200"
let linearizable_s1_0''_merge_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    do_pre (v_of inv2) last2 /\
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2)))
         
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of (inverse_st s2')) last2)) = ()

let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
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
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_gt0_base_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    First_then_second? (resolve_conflict last1 last2))
         
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  assume (//(Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1) /\
          (Add_after? (snd last1) /\ Add_after? (snd last2) ==>
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1)); //used for eq
  ()

let linearizable_gt0_base_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    Second_then_first? (resolve_conflict last1 last2))
         
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
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
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) =
  if First_then_second? (resolve_conflict last1 last2) then
    linearizable_gt0_base_fts lca s1 s2 last1 last2
  else if Second_then_first? (resolve_conflict last1 last2) then
    linearizable_gt0_base_stf lca s1 s2 last1 last2
  else ()

let linearizable_gt0_s2'_do_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2)) 
         
          (ensures (length (ops_of s2) > length (ops_of lca) ==> do_pre (v_of (inverse_st s2)) last2) /\
                   (length (ops_of s1) > length (ops_of lca) ==> do_pre (v_of (inverse_st s1)) last1)) = ()

let linearizable_gt0_s2'_merge_pre (lca s1 s2:st) (last1 last2:op_t)
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
                      merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of (inverse_st s2)) last2))) = ()
                      
let linearizable_gt0_s1'_do_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2)) 
          (ensures (length (ops_of s2) > length (ops_of lca) ==> do_pre (v_of (inverse_st s2)) last2) /\
                   (length (ops_of s1) > length (ops_of lca) ==> do_pre (v_of (inverse_st s1)) last1)) = ()

let linearizable_gt0_s1'_merge_pre (lca s1 s2:st) (last1 last2:op_t)
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
                      merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of (inverse_st s2)) last2))) = ()

#push-options "--z3rlimit 600"
let linearizable_gt0_ind_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s2' = inverse_st s2 in
                    do_pre (v_of s2') last2 /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    //Remove? (snd last1) /\ Remove? (snd last2) /\ //all done
                    //Add_after? (snd last1) /\ Remove? (snd last2) /\
                    //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 <> get_after_id last2 /\
                    //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 = get_after_id last2 /\ fst last1 > fst last2 /\
                    //consistent_branches lca s1 (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    //consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  
  lem_apply_log init_st (ops_of s2);
  let pre, lastop = un_snoc (ops_of s2) in
  inverse_helper init_st pre lastop;
  assume (Remove? (snd last1) ==> get_rem_id last1 <> fst lastop);
  assume (Add_after? (snd last1) /\ Remove? (snd last2) ==> fst last1 <> get_rem_id last2 /\ fst last1 <> fst lastop); 
  assume (Add_after? (snd last1) /\ Remove? (snd last2) /\ Remove? (snd lastop) ==> fst last1 <> get_rem_id lastop);
  assume (Add_after? (snd last1) /\ Remove? (snd last2) /\ Add_after? (snd lastop) ==>
                fst last1 <> get_after_id lastop /\ fst lastop <> get_after_id last1); 
  assume ((Add_after? (snd last1) /\ Add_after? (snd last2) ==> fst last1 <> fst lastop /\
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1)); 
  assume (Add_after? (snd last1) /\ Add_after? (snd last2) /\ Add_after? (snd lastop) ==>
                     fst last1 <> get_after_id lastop /\ fst lastop <> get_after_id last1); 
  assume (Add_after? (snd last1) /\ Add_after? (snd last2) /\ Remove? (snd lastop) ==>
                     fst last1 <> get_rem_id lastop);
  ()
 
let linearizable_gt0_ind_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s2' = inverse_st s2 in
                    do_pre (v_of s2') last2 /\
                    ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    //Remove? (snd last1) /\ Add_after? (snd last2) /\
                    //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 = get_after_id last2 /\ fst last1 < fst last2 /\
                    //consistent_branches lca (do_st s1 last1) s2' /\
                    //consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2') /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 
          (*[SMTPat (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))]*) = ()

let linearizable_gt0_ind1_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s1' = inverse_st s1 in
                    do_pre (v_of s1') last1 /\
                    ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    //Remove? (snd last1) /\ Remove? (snd last2) /\ //all done
                    //Add_after? (snd last1) /\ Remove? (snd last2) /\
                    //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 <> get_after_id last2 /\
                    //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 = get_after_id last2 /\ fst last1 > fst last2 /\
                    //consistent_branches lca s1' (do_st s2 last2) /\
                    //consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1') (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
                    
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_ind1_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s1' = inverse_st s1 in
                    do_pre (v_of s1') last1 /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    //Remove? (snd last1) /\ Add_after? (snd last2) /\
                    //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 = get_after_id last2 /\ fst last1 < fst last2 /\
                    //consistent_branches lca (do_st s1' last1) s2 /\
                    //consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
                           
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\    
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =  //both do_pre and eq
  
  lem_apply_log init_st (ops_of s1);
  let pre, lastop = un_snoc (ops_of s1) in
  inverse_helper init_st pre lastop;
  assume (Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1 /\ fst last2 <> fst lastop);
  assume (Remove? (snd last1) /\ Add_after? (snd last2) /\ Remove? (snd lastop) ==> fst last2 <> get_rem_id lastop);
  assume (Remove? (snd last1) /\ Add_after? (snd last2) /\ Add_after? (snd lastop) ==>
                fst last2 <> get_after_id lastop /\ fst lastop <> get_after_id last2);
  assume ((Add_after? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> fst lastop /\
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1));
  assume (Add_after? (snd last1) /\ Add_after? (snd last2) /\ Add_after? (snd lastop) ==>
                     fst last2 <> get_after_id lastop /\ fst lastop <> get_after_id last2);
  assume (Add_after? (snd last1) /\ Add_after? (snd last2) /\ Remove? (snd lastop) ==>
                     fst last2 <> get_rem_id lastop);
  ()

let fts_merge_pre' (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     First_then_second? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) = ()

let stf_merge_pre' (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Second_then_first? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = ()






(*#push-options "--z3rlimit 400"
(*let linearizable_gt0_ind_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s2' = inverse_st s2 in
                    do_pre (v_of s2') last2 /\
                    First_then_second? (resolve_conflict last1 last2) /\
     Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 = get_after_id last2 /\ fst last1 > fst last2 /\
     //Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 <> get_after_id last2 /\
     //Add_after? (snd last1) /\ Remove? (snd last2) /\ fst last1 <> get_rem_id last2 /\ //not done
     //Remove? (snd last1) /\ Add_after? (snd last2) /\
     //Remove? (snd last1) /\ Remove? (snd last2) /\
                    //consistent_branches lca s1 (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    //consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
       
          (ensures //merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   //do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (*[SMTPat (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))]*) =  // eq not working
  lem_apply_log init_st (ops_of s2);
  let pre, lastop = un_snoc (ops_of s2) in
  inverse_helper init_st pre lastop;
  assume (Remove? (snd last1) ==> get_rem_id last1 <> fst lastop);
  assume (Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1);
  assume (Add_after? (snd last1) /\ Remove? (snd last2) ==> fst last1 <> get_rem_id last2);
  assume (Add_after? (snd last1) /\ Add_after? (snd last2) ==> fst last1 <> fst lastop /\
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1);
  ()*)


let linearizable_s1_0' (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    ops_of s1 = ops_of lca)
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()


let linearizable_gt0_fts (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\
                    consistent_branches lca (inverse_st s1) s2 /\
                    consistent_branches lca (inverse_st s1) (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                    do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    (*merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                    do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\*)
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = ()
                        

let linearizable_gt0_base_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
         
          (ensures //merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   //do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = () 


#push-options "--z3rlimit 100"
(*let linearizable_s1_0'1 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    ops_of s1 = ops_of lca /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = admit()

#push-options "--z3rlimit 200"
let linearizable_gt0_s21 (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\
                    consistent_branches lca s1 (inverse_st s2) /\
                    consistent_branches lca (inverse_st s1) (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\ 
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2)) /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures (let pre2, last2 = un_snoc (ops_of s2) in 
                    //merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 (*/\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)*))) =
  lem_apply_log init_st (ops_of s2);
  let pre2, last2 = un_snoc (ops_of s2) in 
  inverse_helper init_st pre2 last2;
  assert (v_of s2 = do (v_of (inverse_st s2)) last2);
  if Remove? (snd last2) then () else ()*)

let rec linearizable_s1_0''_base_do_pre1 (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\ 
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    fst last2 > 0 /\ //Add_after? (snd last2) /\
                    length (ops_of s2') > 0)
          (ensures do_pre (v_of (inverse_st s2')) last2) 
          (decreases length (ops_of s2')) =
  lem_apply_log init_st (ops_of s2');
  let pre, lastop = un_snoc (ops_of s2') in
  inverse_helper init_st pre lastop;
  (*if length (ops_of s2') = 0 then ()
  else 
    (lem_apply_log init_st (ops_of s2');
     let _, lastop = un_snoc (ops_of s2') in
     let s2'' = inverse_st s2' in
     if Remove? (snd lastop) then () 
     else 
       (if fst lastop <> get_rem_id last2 then () 
        else 
          (();//assert (~ (S.mem (get_rem_id last2) (snd (v_of s2''))));
           //assume (mem_id_s (get_rem_id last2) (fst (v_of s2'')));
           ())))*) ()

  (*if length (ops_of lca) = 0 then admit()
  else if length (ops_of lca) = 1 then 
    (lem_apply_log init_st (ops_of s2');
     let _, lastop = un_snoc (ops_of s2') in
     //inverse_helper init_st (ops_of lca) lastop;
     
     //if Add_after? (snd lastop) then admit() else ())
     assert (fst init_st == S.empty); 
     assert (not (mem_id_s (fst last2) (fst init_st))); 
     if Remove? (snd last2) then () else ())
  else 
    (let l' = inverse_st lca in
     assume (do_pre (v_of l') last2 /\
             length (ops_of l') > 0 /\
             consistent_branches l' l' (do_st l' last2));
     linearizable_s1_0''_base_do_pre l' l' l' last2); ()*)

let linearizable_s1_0''_do_pre1 (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    ops_of s1 = ops_of lca /\                    
                    fst last2 > 0 /\
                    length (ops_of s2') > length (ops_of lca))         
          (ensures do_pre (v_of (inverse_st s2')) last2) = ()
          
let linearizable_s1_0''_base_merge_pre1 (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\ 
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    fst last2 > 0 /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    length (ops_of s2') > 0 /\
                    do_pre (v_of (inverse_st s2')) last2)

          (ensures (let l' = inverse_st lca in
                    merge_pre (v_of l') (v_of l') (do (v_of l') last2))) = ()

let linearizable_s1_0''_base_ind1 (lca s1 s2':st) (last2:op_t)
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

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

(*let linearizable_s1_0''_do_pre1 (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    ops_of s1 = ops_of lca /\                    
                    fst last2 > 0 /\
                    length (ops_of s2') > length (ops_of lca))         
          (ensures do_pre (v_of (inverse_st s2')) last2) = admit()*)

let linearizable_s1_0''_merge_pre1 (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    do_pre (v_of inv2) last2 /\
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2)))
         
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of (inverse_st s2')) last2)) = ()

#push-options "--z3rlimit 50"
let linearizable_s1_0''_ind1 (lca s1 s2':st) (last2:op_t)
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
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0_s2_0_base1 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

#push-options "--z3rlimit 100"
let linearizable_gt0_base_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    Remove? (snd last1) /\ Add_after? (snd last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2))
         
          (ensures //merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) (*/\                   
                   //do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  (*assume ((Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1) /\
          (Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 <> get_after_id last2 ==>
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1));*)
  //assume (not (mem_id_s (fst last2) (fst (v_of lca))) /\ not (S.mem (fst last2) (snd (v_of lca))));
  admit()

 let linearizable_gt0_base_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    Second_then_first? (resolve_conflict last1 last2))
         
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_base1 (lca s1 s2:st) (last1 last2:op_t)
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
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = 
  if First_then_second? (resolve_conflict last1 last2) then
    linearizable_gt0_base_fts lca s1 s2 last1 last2
  else if Second_then_first? (resolve_conflict last1 last2) then
    linearizable_gt0_base_stf lca s1 s2 last1 last2
  else ()

let linearizable_gt0_s2'_do_pre1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2)) 
         
          (ensures (length (ops_of s2) > length (ops_of lca) ==> do_pre (v_of (inverse_st s2)) last2) /\
                   (length (ops_of s1) > length (ops_of lca) ==> do_pre (v_of (inverse_st s1)) last1)) = ()

let linearizable_gt0_s2'_merge_pre1 (lca s1 s2:st) (last1 last2:op_t)
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
                      merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of (inverse_st s2)) last2))) = ()

let linearizable_gt0_s1'_do_pre1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2)) 
         
          (ensures (length (ops_of s2) > length (ops_of lca) ==> do_pre (v_of (inverse_st s2)) last2) /\
                   (length (ops_of s1) > length (ops_of lca) ==> do_pre (v_of (inverse_st s1)) last1)) = ()

let linearizable_gt0_s1'_merge_pre1 (lca s1 s2:st) (last1 last2:op_t)
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
                      merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of (inverse_st s2)) last2))) = ()

#push-options "--z3rlimit 200"
let linearizable_gt0_ind_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s2' = inverse_st s2 in
                    do_pre (v_of s2') last2 /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    //Remove? (snd last1) /\ Add_after? (snd last2) /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1 /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    //do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)))) 
        
          (ensures //merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) ///\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 (*/\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)*)) = 
                      
  (*assume ((Remove? (snd last1) /\ Add_after? (snd last2) ==> fst last2 <> get_rem_id last1) /\
          (Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 <> get_after_id last2 ==>
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1));*)
  lem_apply_log init_st (ops_of s2);
  let pre, lastop = un_snoc (ops_of s2) in
  inverse_helper init_st pre lastop; 
  assume (fst last1 <> fst lastop); //can be done
  (*if Remove? (snd last1) then () 
  else 
    (assert (~ (mem_id_s (fst last1) (fst (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))))); ())*) ()  
                    
let linearizable_gt0_ind_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s2' = inverse_st s2 in
                    do_pre (v_of s2') last2 /\
                    ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2') /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_ind1_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s1' = inverse_st s1 in
                    do_pre (v_of s1') last1 /\
                    ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1' (do_st s2 last2) /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1') (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)))) 
        
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_ind1_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    (let s1' = inverse_st s1 in
                    do_pre (v_of s1') last1 /\
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
        
          (ensures //merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) (*/\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 (*/\    
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)*)) = 
  assume ((Add_after? (snd last1) /\ Remove? (snd last2) /\ get_after_id last1 = get_rem_id last2 ==> 
                      fst last1 <> get_rem_id last2 /\ get_after_id last1 <> fst last2) /\
          (Add_after? (snd last1) /\ Add_after? (snd last2) /\ get_after_id last1 = get_after_id last2 /\ fst last2 > fst last1 ==>
                      fst last1 <> get_after_id last2 /\ fst last2 <> get_after_id last1));
  ()

let fts_merge_pre1 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in 
                     let _, last2 = un_snoc (ops_of s2) in 
                     fst last1 <> fst last2 /\
                     First_then_second? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) = ()
   
let stf_merge_pre1 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Second_then_first? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = ()

(*let first_merge_pre1 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     First? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) = ()*)

(*let convergence1 (lca s1' s2:concrete_st) (ls1' ls2:log) (o:op_t)
  : Lemma (requires do_pre s1' o /\
                    merge_pre lca (do s1' o) s2 /\
                    merge_pre lca s1' s2 /\
                    merge_pre s1' (do s1' o) (concrete_merge lca s1' s2))                   
          (ensures eq (concrete_merge lca (do s1' o) s2)
                      (concrete_merge s1' (do s1' o) (concrete_merge lca s1' s2))) = ()

let convergence2 (lca' lca s3 s1 s2:concrete_st) (llca ls3 ls1 ls2:log)
  : Lemma (requires merge_pre lca s3 s1 /\
                    merge_pre lca' (concrete_merge lca s3 s1) s2 /\
                    merge_pre lca' s1 s2 /\
                    merge_pre s1 (concrete_merge lca s3 s1) (concrete_merge lca' s1 s2))
          (ensures eq (concrete_merge lca' (concrete_merge lca s3 s1) s2)
                      (concrete_merge s1 (concrete_merge lca s3 s1) (concrete_merge lca' s1 s2))) = ()

let convergence3 (s:concrete_st) (op:op_t)
  : Lemma (requires do_pre s op /\
                    merge_pre s s (do s op))
          (ensures eq (concrete_merge s s (do s op)) (do s op)) = ()




let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
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
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) =
  if First_then_second? (resolve_conflict last1 last2) then
    linearizable_gt0_ind_fts lca s1 s2 last1 last2
  else linearizable_gt0_ind_stf lca s1 s2 last1 last2


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
*)
