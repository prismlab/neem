module App

#set-options "--query_stats"
// the concrete state type
// It is a pair of timestamp and value
type concrete_st = nat * nat

// init state
let init_st = 0, 0

// equivalence between 2 concrete states
let eq (a b:concrete_st) = a == b

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
// (the only operation is Write value, so nat is fine)
type app_op_t = nat

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st = (fst op, snd op)

let lem_do (a b:concrete_st) (op:op_t)
  : Lemma (requires eq a b)
          (ensures eq (do a op) (do b op)) = ()
           
//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if lt (fst y) (fst x) then First_then_second else Second_then_first

// concrete merge operation
let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  if fst s1 < fst s2 then s2 else s1

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (length l > 0 ==> (let _, last = un_snoc l in apply_log s l = (fst last, snd last)) /\
                                     mem_id (fst (apply_log s l)) l) /\
                   (length l = 0 ==> (apply_log s l = s)) /\
                   (length l > 0 /\ (forall id. mem_id id l ==> lt (fst s) id) ==> (lt (fst s) (fst (apply_log s l)))) /\
                   ((fst (apply_log s l) = fst s) \/ mem_id (fst (apply_log s l)) l))
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

#push-options "--z3rlimit 50"
let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = 
  lem_foldl init_st (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  assert (fst (v_of s1) >= fst (v_of lca) /\ fst (v_of s2) >= fst (v_of lca) );
  assert (fst (v_of s1) = fst (v_of s2) ==> v_of s1 = v_of s2);
  ()
#pop-options

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

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) =
  assert (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)); //assert needed
  let pre1, last1 = un_snoc (ops_of s1) in
  lemma_mem_snoc pre1 last1;
  mem_ele_id last1 (ops_of lca)

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
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))  = ()              

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
type concrete_st_s = nat

// init state 
let init_st_s = 0

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = snd op

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == snd st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////
//// Linearization properties //////

let merge1 (lca s1 s2:concrete_st)  =
  if fst s1 < fst s2 then s2 else s1

let conv_prop1 (lca s1 s2:concrete_st) (op1 op2:op_t)
  : Lemma (requires fst op1 <> fst op2 /\ resolve_conflict op1 op2 = First_then_second)
          (ensures eq (merge1 lca (do s1 op1) (do s2 op2)) (do (merge1 lca s1 (do s2 op2)) op1)) = ()

let conv_prop2 (lca s1 s2:concrete_st) (op1 op2:op_t)
  : Lemma (requires fst op1 <> fst op2 /\ resolve_conflict op1 op2 = Second_then_first)
          (ensures eq (merge1 lca (do s1 op1) (do s2 op2)) (do (merge1 lca (do s1 op1) s2) op2)) = ()

let conv_prop3 (s:concrete_st)
  : Lemma (eq (merge1 s s s) s) = ()

let conv_prop4 (lca s1 s2:concrete_st) (op:op_t)
  : Lemma (ensures eq (merge1 lca (do s1 op) (do s2 op)) (do (merge1 lca s1 s2) op)) = ()

let merge_pre (l a b:concrete_st) = 
  (fst a >= fst l) /\ (fst b >= fst l) /\
  ((fst a = fst b) ==> ((a = l) /\ (b = l))) 

let rec_merge (s si si' sn sn':concrete_st)
  : Lemma (requires merge_pre s sn sn' /\ merge_pre si sn sn' /\ merge_pre si' sn sn' /\ 
                    merge_pre s sn si' /\ merge_pre s si sn' /\
                    merge_pre s si si' /\ merge_pre s si' si /\ 
                    merge_pre si sn (merge1 s si si') /\ merge_pre si' sn' (merge1 s si' si) /\
                    merge_pre (merge1 s si si') (merge1 s si sn') (merge1 s si' sn) /\
                    merge_pre si sn (merge1 s si sn') /\ merge_pre si' (merge1 s sn si') sn' /\
                    
                    eq (merge1 s sn sn') (merge1 si sn (merge1 s si sn')) /\
                    eq (merge1 s sn sn') (merge1 si' (merge1 s sn si') sn') /\
                    eq (merge1 s sn si') (merge1 si sn (merge1 s si si')) /\
                    eq (merge1 s si sn') (merge1 si' sn' (merge1 s si' si)))
         
          (ensures (eq (merge1 s sn sn')
                       (merge1 (merge1 s si si') (merge1 s si sn') (merge1 s si' sn)))) = ()
                      
let rec_merge1 (s si si' sn sn':concrete_st)
  : Lemma (requires merge_pre s sn sn' /\ merge_pre si sn sn' /\ merge_pre si' sn sn' /\ 
                    merge_pre s sn si' /\ merge_pre s si sn' /\
                    merge_pre s si si' /\ merge_pre s si' si /\ 
                    merge_pre si sn (merge1 s si si') /\ merge_pre si' sn' (merge1 s si' si) /\
                    merge_pre (merge1 s si si') (merge1 s si sn') (merge1 s si' sn) /\
                    eq (merge1 s sn sn') (merge1 si sn sn') /\
                    eq (merge1 s sn sn') (merge1 si' sn sn') /\
                    eq (merge1 s sn si') (merge1 si sn (merge1 s si si')) /\
                    eq (merge1 s si sn') (merge1 si' sn' (merge1 s si' si)))
          (ensures (eq (merge1 s sn sn')
                       (merge1 (merge1 s si si') (merge1 s si sn') (merge1 s si' sn)))) = ()
          
////////////////////////////////////////////////////////////////

(*let do_prop (s:concrete_st) (o:op_t) 
  : Lemma (fst (do s o) = fst o) = ()


#push-options "--z3rlimit 300"
let rec convergence (lca s1' s2:concrete_st) (ls1' ls2:log) (o:op_t)
  : Lemma (requires distinct_ops ls1' /\ distinct_ops ls2 /\
                    s1' == apply_log lca ls1' /\
                    s2 == apply_log lca ls2 /\
                    (forall id. mem_id id ls1' ==> not (mem_id id ls2)) /\
                    not (mem_id (fst o) ls1') /\
                    fst lca < fst o /\
                        //fst s1' < fst o /\ ==> direct proof
                    (forall id. mem_id id ls1' ==> fst o > id) /\
                    (exists l1 l2 l3. apply_log lca l1 == s1' /\ apply_log lca l2 == s2 /\
                                 apply_log lca l3 == (do s1' o)) /\
                    (exists l1 l2. apply_log s1' l1 == (do s1' o) /\
                              apply_log s1' l2 == (concrete_merge lca s1' s2)))
          (ensures eq (concrete_merge lca (do s1' o) s2)
                      (concrete_merge s1' (do s1' o) (concrete_merge lca s1' s2))) = 
  if fst s1' < fst o then ()
  else if fst s1' > fst o then 
    (if length ls1' = 0 then ()
     else 
       (let ls1'', lastop1 = un_snoc ls1' in
        let s1'' = apply_log lca ls1'' in
        split_prefix lca ls1'' ls1';
        lemma_append_count_assoc_fst ls1'' (create 1 lastop1);
        convergence lca s1'' s2 ls1'' ls2 o))
  else ()

let convergence1 (lca s1' s2:st) (o:op_t)
  : Lemma (requires //consistent_branches lca s1 s2 /\
                    //consistent_branches lca s1' s2 /\
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id. mem_id id (ops_of s1') ==> fst o > id) /\
                    (exists l1 l2 l3. apply_log (v_of lca) l1 == v_of s1' /\ apply_log (v_of lca) l2 == v_of s2 /\
                                 apply_log (v_of lca) l3 == (do (v_of s1') o)) /\
                    (exists l1 l2. apply_log (v_of s1') l1 == (do (v_of s1') o) /\
                              apply_log (v_of s1') l2 == (concrete_merge (v_of lca) (v_of s1') (v_of s2))))
          (ensures eq (concrete_merge (v_of lca) (do (v_of s1') o) (v_of s2)) 
                      (concrete_merge (v_of s1') (do (v_of s1') o) (concrete_merge (v_of lca) (v_of s1') (v_of s2)))) = 
  do_prop (v_of s1') o;
  if ops_of s1' = ops_of lca then 
    (if fst (v_of s1') < fst o then () //done
     else if fst (v_of s1') > fst o then 
       (if length (ops_of lca) = 0 then () //done 
        else 
          (let l' = inverse_st lca in
           let pre, lastop = un_snoc (ops_of lca) in
           lemma_append_count_assoc_fst pre (create 1 lastop);
           assert (mem_id (fst lastop) (ops_of s1'));
           assert (v_of s1' == (fst lastop, snd lastop)); 
           assert (fst (v_of s1') < fst o); //proof by contradiction
           ())) //done
     else ()) //done
  else 
    (if fst (v_of s1') < fst o then () //done
     else if fst (v_of s1') > fst o then 
       (let s1'' = inverse_st s1' in
        let pre, lastop = un_snoc (ops_of s1') in
        lemma_append_count_assoc_fst pre (create 1 lastop);
        assert (is_prefix (ops_of s1') (snoc (ops_of s1') o));
        assert (mem_id (fst lastop) (ops_of s1')); 
        assert (v_of s1' == (fst lastop, snd lastop));
        assert (fst (v_of s1') < fst o); //proof by contradiction
        ()) //done
     else ()) //done

let convergence2 (lca' lca s3 s1 s2:st)
  : Lemma (requires //consistent_branches lca s3 s1' /\
                    //consistent_branches lca' s1' s2 /\
                    (exists l1 l2. apply_log (v_of lca) l1 == v_of s3 /\ apply_log (v_of lca) l2 == v_of s1) /\
                    (exists l1 l2. apply_log (v_of lca') l1 == v_of s1 /\ apply_log (v_of lca') l2 == v_of s2) /\
                    (exists l1. apply_log (v_of lca') l1 == (concrete_merge (v_of lca) (v_of s3) (v_of s1))) /\
                    (exists l1 l2. apply_log (v_of s1) l1 == (concrete_merge (v_of lca') (v_of s1) (v_of s2)) /\ 
                              apply_log (v_of s1) l2 == (concrete_merge (v_of lca) (v_of s3) (v_of s1))))
          (ensures eq (concrete_merge (v_of lca') (concrete_merge (v_of lca) (v_of s3) (v_of s1)) (v_of s2)) 
                      (concrete_merge (v_of s1) 
                                      (concrete_merge (v_of lca) (v_of s3) (v_of s1))
                                      (concrete_merge (v_of lca') (v_of s1) (v_of s2)))) = () //done


let convergence3 (lca' lca s3 s1 s2:concrete_st) (llca ls3 ls1 ls2:log)
  : Lemma (requires //distinct_ops llca /\ distinct_ops ls3 /\ distinct_ops ls1 /\ distinct_ops ls2 /\
                    //lca == apply_log lca' llca /\
                    s3 == apply_log lca ls3 /\
                    s1 == apply_log lca ls1 /\
                    s2 == apply_log lca' ls2 /\
                    //(forall id. mem_id id llca ==> not (mem_id id ls1) /\ not (mem_id id ls2) /\ not (mem_id id ls3)) /\
                    //(forall id. mem_id id ls1 ==> not (mem_id id ls2) /\ not (mem_id id ls3)) /\
                    //(forall id. mem_id id ls2 ==> not (mem_id id ls3)) /\
                    //(exists l1 l2. apply_log lca l1 == s3 /\ apply_log lca l2 == s1) /\
                    (exists l1. apply_log lca' l1 == s1) /\
                    (exists l1. apply_log lca' l1 == (concrete_merge lca s3 s1)) /\
                    (exists l1 l2. apply_log s1 l1 == (concrete_merge lca' s1 s2) /\ 
                              apply_log s1 l2 == (concrete_merge lca s3 s1)))
          (ensures eq (concrete_merge lca' (concrete_merge lca s3 s1) s2)
                      (concrete_merge s1 (concrete_merge lca s3 s1) (concrete_merge lca' s1 s2))) = ()
#pop-options*)
