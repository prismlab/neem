module App

module S = Set_extended

#set-options "--query_stats"
// the concrete state type
type concrete_st = s:(S.set nat & S.set nat){S.subset (snd s) (fst s)} 
                 //first one is add set, second one is remove set

// init state
let init_st = (S.empty, S.empty)

// equivalence between 2 concrete states
let eq (a b:concrete_st) = 
  //S.equal (S.difference (fst a) (snd a)) (S.difference (fst b) (snd b))
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
  | Add : nat -> app_op_t
  | Rem : nat -> app_op_t

let get_ele (op:op_t) = 
  match op with
  |(_, Add ele) -> ele
  |(_, Rem ele) -> ele

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : (r:concrete_st{S.subset (fst s) (fst r) /\ S.subset (snd s) (snd r)}) =
  match op with
  |(_, Add ele) -> if S.mem ele (snd s) then s else (S.add ele (fst s), snd s)
  |(_, Rem ele) -> if S.mem ele (fst s) then (fst s, S.add ele (snd s)) else s
  
let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()
           
//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res = 
  match x, y with
  |(_, Rem ele), (_, Add ele1) -> if ele = ele1 then First_then_second else Second_then_first
  |(_, Add ele), (_, Rem ele1) -> if ele = ele1 then Second_then_first else First_then_second
  |_ -> Second_then_first

// concrete merge operation
let concrete_merge (lca s1 s2:concrete_st) : concrete_st =
  (S.union (fst lca) (S.union (fst s1) (fst s2)), (S.union (snd lca) (S.union (snd s1) (snd s2))))

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

#push-options "--z3rlimit 50"
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
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = ()              

#push-options "--z3rlimit 100"
let linearizable_gt0_ind_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (let s2' = inverse_st s2 in
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_ind_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (let s2' = inverse_st s2 in
                    ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

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
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = admit()

let linearizable_gt0_ind1_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (let s1' = inverse_st s1 in
                    ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1' (do_st s2 last2) /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
                           
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let merge_pre (lca s1 s2:concrete_st) =
  S.subset (fst lca) (fst s1) /\ S.subset (fst lca) (fst s2) /\
  S.subset (snd lca) (snd s1) /\ S.subset (snd lca) (snd s2)

let trial (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (let s1' = inverse_st s1 in
                    Rem? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2 /\ 
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
        
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  lem_apply_log init_st (ops_of s1);
  (*let pre, lastop = un_snoc (ops_of s1) in
  //if Add? (snd lastop) && get_ele lastop = get_ele last1 then () //done
  //if Rem? (snd lastop) && get_ele lastop = get_ele last1 then () //done
  //if Rem? (snd lastop) && get_ele lastop <> get_ele last1 then ()  //done
  //if Add? (snd lastop) && get_ele lastop <> get_ele last1 && get_ele lastop <> get_ele last2 then () //done
 
  if Add? (snd lastop) && get_ele lastop <> get_ele last1 && get_ele lastop = get_ele last2 then () 
  //linearization not possible
  //ex. s1' = {},{}, s1 = {1},{}, s2 = {},{}, lastop = Add 1, last1 = Rem 2, last2 = Rem 1
 
  else admit*)()
  
#push-options "--z3rlimit 300"
let linearizable_gt0_ind1_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (let s1' = inverse_st s1 in
                    Rem? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\ //not working
                    //Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2 /\ // working
                    //Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    (*merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\*)
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))      
        
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  lem_apply_log init_st (ops_of s1);
  let pre, lastop = un_snoc (ops_of s1) in
  //if Add? (snd lastop) && get_ele lastop = get_ele last1 then () //done
  //if Rem? (snd lastop) && get_ele lastop = get_ele last1 then () //done
  //if Rem? (snd lastop) && get_ele lastop <> get_ele last1 then ()  //done
  //if Add? (snd lastop) && get_ele lastop <> get_ele last1 && get_ele lastop <> get_ele last2 then () //done
 
  if Add? (snd lastop) && get_ele lastop <> get_ele last1 && get_ele lastop = get_ele last2 then () 
  //linearization not possible
  //ex. s1' = {},{}, s1 = {1},{}, s2 = {},{}, lastop = Add 1, last1 = Rem 2, last2 = Rem 1
 
  else admit()

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
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = admit()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = S.set nat

// init state 
let init_st_s = S.empty

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s =
  match op with
  |(_, Add ele) -> S.add ele s
  |(_, Rem ele) -> S.remove_if s (fun e -> e = ele)

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  S.equal (S.difference (fst st) (snd st)) st_s

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = 
  if Add? (snd op) then admit() else ()

////////////////////////////////////////////////////////////////

let convergence1 (lca s1' s2:st) (o:op_t)
  : Lemma (requires //consistent_branches lca s1 s2 /\
                    //consistent_branches lca s1' s2 /\
                    (exists l1 l2 l3. apply_log (v_of lca) l1 == v_of s1' /\ apply_log (v_of lca) l2 == v_of s2 /\
                                 apply_log (v_of lca) l3 == (do (v_of s1') o)) /\
                    (exists l1 l2. apply_log (v_of s1') l1 == (do (v_of s1') o) /\
                              apply_log (v_of s1') l2 == (concrete_merge (v_of lca) (v_of s1') (v_of s2))))
          (ensures eq (concrete_merge (v_of lca) (do (v_of s1') o) (v_of s2)) 
                      (concrete_merge (v_of s1') (do (v_of s1') o) (concrete_merge (v_of lca) (v_of s1') (v_of s2)))) = ()

let convergence2 (lca' lca s3 s1' s2:st)
  : Lemma (requires //consistent_branches lca s3 s1' /\
                    //consistent_branches lca' s1' s2 /\
                    (exists l1 l2. apply_log (v_of lca) l1 == v_of s3 /\ apply_log (v_of lca) l2 == v_of s1') /\
                    (exists l1 l2. apply_log (v_of lca') l1 == v_of s1' /\ apply_log (v_of lca') l2 == v_of s2) /\
                    (exists l1. apply_log (v_of lca') l1 == (concrete_merge (v_of lca) (v_of s3) (v_of s1'))) /\
                    (exists l1 l2. apply_log (v_of s1') l1 == (concrete_merge (v_of lca') (v_of s1') (v_of s2)) /\ 
                              apply_log (v_of s1') l2 == (concrete_merge (v_of lca) (v_of s3) (v_of s1'))))
          (ensures eq (concrete_merge (v_of lca') (concrete_merge (v_of lca) (v_of s3) (v_of s1')) (v_of s2)) 
                      (concrete_merge (v_of s1') 
                                       (concrete_merge (v_of lca) (v_of s3) (v_of s1'))
                                       (concrete_merge (v_of lca') (v_of s1') (v_of s2)))) = ()
