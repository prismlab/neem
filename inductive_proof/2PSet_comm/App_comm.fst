module App_comm

module S = Set_extended
open SeqUtils

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
  |(_, Rem ele), (_, Add ele1) -> (*if ele = ele1 then*) Second_then_first //else First_then_second
  |(_, Add ele), (_, Rem ele1) -> (*if ele = ele1 then*) First_then_second //else Second_then_first
  |_ -> Second_then_first

(*let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res = 
  if get_ele x = get_ele y && Add? (snd x) && Rem? (snd y) then 
    First_then_second 
  else Second_then_first*)

// concrete merge operation
let concrete_merge (lca s1 s2:concrete_st) : concrete_st =
  (S.union (fst lca) (S.union (fst s1) (fst s2)), (S.union (snd lca) (S.union (snd s1) (snd s2))))

let commutative (x y:op_t) = 
  not (((Add? (snd x) && Rem? (snd y) && get_ele x = get_ele y) ||
        (Add? (snd y) && Rem? (snd x) && get_ele x = get_ele y))) 

let comm_symmetric (x y:op_t) 
  : Lemma (requires commutative x y)
          (ensures commutative y x) = ()

let commutative_prop (x y:op_t) 
  : Lemma (requires commutative x y)
          (ensures (forall s. eq (apply_log s (cons x (cons y empty))) (apply_log s (cons y (cons x empty))))) = ()
          
let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = ()

let lem_trans_merge_s1' (lca s1 s2 s1':concrete_st)
  : Lemma (requires eq s1 s1' /\
                    (exists l1' l1 l2. s1' == apply_log lca l1' /\ s1 == apply_log lca l1 /\ s2 == apply_log lca l2))
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1' s2)) = ()

let lem_trans_merge_s2' (lca s1 s2 s2':concrete_st)
  : Lemma (requires eq s2 s2' /\
                    (exists l1 l2' l2. s1 == apply_log lca l1 /\ s2' == apply_log lca l2' /\ s2 == apply_log lca l2))
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1 s2')) = ()

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
  
let rec linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca)
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))
          (decreases (length (ops_of s2))) =
  if ops_of s2 = ops_of lca then ()
  else 
    (let pre, lastop = un_snoc (ops_of s2) in
     pre1_pre2_s2 lca s1 s2;
     linearizable_s1_0 lca s1 (inverse_st s2))

#push-options "--z3rlimit 100"
let linearizable_gt0_s2'_op (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\                   
                     (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                      suf2 == snd (pre_suf (ops_of s2) op2) /\
                      (let s2' = inverse_st_op s2 op2 in
                      consistent_branches lca s1 s2' /\
                      consistent_branches lca s1 (do_st s2' op2)))))
     
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let s2' = inverse_st_op s2 op2 in                      
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) op2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') op2)))) = ()

let linearizable_gt0_s1'_op (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\                                          
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     exists_triple last2 (diff (ops_of s1) (ops_of lca)) /\                    
                     (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                      suf1 == snd (pre_suf (ops_of s1) op1) /\
                      (let s1' = inverse_st_op s1 op1 in
                      consistent_branches lca s1' s2 /\
                      consistent_branches lca (do_st s1' op1) s2))))
       
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let (pre1, op1, suf2) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    let s1' = inverse_st_op s1 op1 in                     
                    eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) op1)
                       (concrete_merge (v_of lca) (do (v_of s1') op1) (v_of s2)))) = ()
  
let linearizable_gt0_s1' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\                    
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     First_then_second? (resolve_conflict last1 last2) /\
                     consistent_branches lca (inverse_st s1) s2))
        
          (ensures (let _, last1 = un_snoc (ops_of s1) in                  
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = ()

let lem_l2r_s10_base (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\ 
                    ops_of s1 = ops_of lca /\
                    Rem? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca)
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) = ()

let lem_l2r_s10_ind (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                    ops_of s1 = ops_of lca /\
                    Rem? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    is_prefix (ops_of lca) (ops_of s2) /\

                    (let s2' = inverse_st s2 in
                    consistent_branches lca s1 s2' /\ 
                    is_prefix (ops_of lca) (ops_of s2') /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))))
                   
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) = () 
                      
let rec lem_l2r_s10 (lca s1 s2:st) (last2:op_t)
 : Lemma (requires consistent_branches lca s1 s2 /\ 
                   ops_of s1 = ops_of lca /\
                   Rem? (snd last2) /\
                   not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   is_prefix (ops_of lca) (ops_of s2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
         (decreases %[length (ops_of s2)]) =
   if ops_of s2 = ops_of lca
     then lem_l2r_s10_base lca s1 s2 last2
   else 
     (let s2' = inverse_st s2 in
      pre1_pre2_s2 lca s1 s2;
      //lem_common_pre1_s2' lca s1 s2 last2;
      lem_l2r_s10 lca s1 s2' last2;
      lem_l2r_s10_ind lca s1 s2 last2) 

let not_add_eq (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    consistent_branches_s2_gt0 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                     Rem? (snd last2) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     (let s2' = inverse_st s2 in
                     is_prefix (ops_of lca) (ops_of s2')))) 
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    ~ (Add? (snd last1) /\ get_ele last1 = get_ele last2))) = 
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2); 
  assert (fst last1 <> fst last2);

  let s1' = inverse_st s1 in
  lemma_mem_snoc (ops_of s1') last1;
  assert (mem last1 (ops_of s1)); 
  lem_last (ops_of s1);
  assert (last (ops_of s1) = last1);
  lem_diff (ops_of s1) (ops_of lca);
  assert (last (diff (ops_of s1) (ops_of lca)) = last1);
  assert (mem last1 (diff (ops_of s1) (ops_of lca)));
  let pre, suf = pre_suf (diff (ops_of s1) (ops_of lca)) last1 in
  lem_lastop_suf_0 (diff (ops_of s1) (ops_of lca)) pre suf last1;
  assert (length suf = 0);
  lemma_empty suf; 
  comm_empty_log last1 suf; 
  assert (commutative_seq last1 suf);

  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> not (commutative last1 last2));
  //resolve_conflict_prop last2 last1;
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> exists_triple last2 (diff (ops_of s1) (ops_of lca)));
  assert (~ (Add? (snd last1) /\ get_ele last1 = get_ele last2)); ()

let lem_l2r_l1r_eq (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    consistent_branches_s2_gt0 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                     Rem? (snd last2) /\ Rem? (snd last1) && get_ele last1 = get_ele last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\ //extra
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     (let s2' = inverse_st s2 in
                     is_prefix (ops_of lca) (ops_of s2'))))              
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = admit();
  let s2' = inverse_st s2 in  //check why this line is needed
  lem_last (ops_of s2);
  let s1' = inverse_st s1 in //check why this line is needed
  lem_last (ops_of s1)

let commu_seq_prop (op:op_t) (l:log)
  : Lemma (requires Add? (snd op))
          (ensures commutative_seq op l <==> (forall e. mem e l ==> ~ (get_ele op = get_ele e /\ Rem? (snd e)))) = ()

let commu_seq_prop_l (op:op_t) (l':log) (last1:op_t)
  : Lemma (requires Add? (snd op) /\ get_ele last1 <> get_ele op /\ commutative_seq op l')
          (ensures commutative_seq op (snoc l' last1)) = 
  lemma_mem_snoc l' last1;
  commu_seq_prop op l';
  commu_seq_prop op (snoc l' last1)
  
let lem_l2r_neq_p2'_help (l:log) (last2:op_t)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd last2) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 <> get_ele last2 /\
                    exists_triple last2 l'))
          (ensures exists_triple last2 l) 
          [SMTPat (let l', last1 = un_snoc l in
                   (exists_triple last2 l'))] =
  let l', last1 = un_snoc l in
  let pre', op', suf' = find_triple last2 l' in
  lemma_mem_snoc l' last1;
  assert (mem op' l);
  let pre, suf = pre_suf l op' in
  commu_seq_prop op' suf';
  
  assert ((snoc pre op') ++ suf = snoc ((snoc pre' op') ++ suf') last1);
  append_assoc (snoc pre' op') suf' (create 1 last1);
  assert ((snoc pre op') ++ suf = ((snoc pre' op') ++ (snoc suf' last1)));
  lem_suf_equal4 l op';
  distinct_invert_append l' (create 1 last1);
  lem_suf_equal4 l' op';

  not_mem_id l' last1;
  mem_ele_id op' l;
  mem_ele_id op' l';
  lem_id_not_snoc l' suf' last1 op'; 
  assert (not (mem_id (fst op') (snoc suf' last1)));
 
  count_1 l;
  //assert (count_id (fst op') (snoc pre op' ++ suf) = 1);
  lem_count_1 pre suf pre' (snoc suf' last1) op';
  
  assert (length suf = length (snoc suf' last1));
  lemma_append_inj (snoc pre op') suf (snoc pre' op') (snoc suf' last1);
  assert (suf = snoc suf' last1);
  commu_seq_prop_l op' suf' last1;
  assert (commutative_seq op' suf); 
  ()
  
let lem_l2r_neq_p2' (l:log) (last2:op_t)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd last2) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 <> get_ele last2))
          (ensures (let l', last1 = un_snoc l in 
                    (exists_triple last2 l' ==> exists_triple last2 l) /\
                    (not (exists_triple last2 l) ==> not (exists_triple last2 l')))) = ()
                    
let lem_l2r_neq_p2 (lca s1 s2:st)
 : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                   length (ops_of s1) > length (ops_of lca) /\
                   (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
         (ensures (let s1' = inverse_st s1 in
                   let s2' = inverse_st s2 in
                   let _, last2 = un_snoc (ops_of s2) in
                   (pre1_pre2_s1 lca s1 s2;
                    (not (exists_triple last2 (diff (ops_of s1') (ops_of lca))))))) = 
 pre1_pre2_s1 lca s1 s2;
 let s1' = inverse_st s1 in
 let _, last2 = un_snoc (ops_of s2) in
 let pre1, last1 = un_snoc (ops_of s1) in
 let pre1d, last1d = un_snoc (diff (ops_of s1) (ops_of lca)) in
 lem_diff (ops_of s1) (ops_of lca);
 assert (last1 = last1d);
 assert (get_ele last1d <> get_ele last2);
 assert ((diff (ops_of s1') (ops_of lca)) = pre1d);
 lem_l2r_neq_p2' (diff (ops_of s1) (ops_of lca)) last2

let lem_l2r_ind (lca s1 s2:st)
  : Lemma (requires (Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    (let s1' = inverse_st s1 in
                    consistent_branches_s2_gt0 lca s1 s2 /\
                    (let s2' = inverse_st s2 in
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last2 <> get_ele last1 /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1') (v_of s2)))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let s2' = inverse_st s2 in  //check why this line is needed
  lem_last (ops_of s2);
  let s1' = inverse_st s1 in //check why this line is needed
  lem_last (ops_of s1)

(*let lem_l2r_neq_p3'_help (l:log) (last2:op_t)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd last2) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 = get_ele last2 /\
                    exists_triple last2 l'))
          (ensures exists_triple last2 l) 
          [SMTPat (let l', last1 = un_snoc l in
                   (exists_triple last2 l'))] =  let l', last1 = un_snoc l in
  let pre', op', suf' = find_triple last2 l' in
  lemma_mem_snoc l' last1;
  assert (mem op' l);
  let pre, suf = pre_suf l op' in
  commu_seq_prop op' suf';
  
  assert ((snoc pre op') ++ suf = snoc ((snoc pre' op') ++ suf') last1);
  append_assoc (snoc pre' op') suf' (create 1 last1);
  assert ((snoc pre op') ++ suf = ((snoc pre' op') ++ (snoc suf' last1)));
  lem_suf_equal4 l op';
  distinct_invert_append l' (create 1 last1);
  lem_suf_equal4 l' op';

  not_mem_id l' last1;
  mem_ele_id op' l;
  mem_ele_id op' l';
  lem_id_not_snoc l' suf' last1 op'; 
  assert (not (mem_id (fst op') (snoc suf' last1)));
 
  count_1 l;
  //assert (count_id (fst op') (snoc pre op' ++ suf) = 1);
  lem_count_1 pre suf pre' (snoc suf' last1) op';
  
  assert (length suf = length (snoc suf' last1));
  lemma_append_inj (snoc pre op') suf (snoc pre' op') (snoc suf' last1);
  assert (suf = snoc suf' last1);
  commu_seq_prop_l op' suf' last1;
  assert (commutative_seq op' suf); 
  ()
  
let lem_l2r_neq_p3' (l:log) (last2:op_t)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd last2) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 = get_ele last2))
          (ensures (let l', last1 = un_snoc l in 
                    (exists_triple last2 l' ==> exists_triple last2 l) /\
                    (not (exists_triple last2 l) ==> not (exists_triple last2 l')))) = ()
                    
let lem_l2r_neq_p3 (lca s1 s2:st)
 : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                   length (ops_of s1) > length (ops_of lca) /\
                   (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
         (ensures (let s1' = inverse_st s1 in
                   let s2' = inverse_st s2 in
                   let _, last2 = un_snoc (ops_of s2) in
                   (pre1_pre2_s1 lca s1 s2;
                    (not (exists_triple last2 (diff (ops_of s1') (ops_of lca))))))) = 
 pre1_pre2_s1 lca s1 s2;
 let s1' = inverse_st s1 in
 let _, last2 = un_snoc (ops_of s2) in
 let pre1, last1 = un_snoc (ops_of s1) in
 let pre1d, last1d = un_snoc (diff (ops_of s1) (ops_of lca)) in
 lem_diff (ops_of s1) (ops_of lca);
 assert (last1 = last1d);
 assert (get_ele last1d <> get_ele last2);
 assert ((diff (ops_of s1') (ops_of lca)) = pre1d);
 lem_l2r_neq_p3' (diff (ops_of s1) (ops_of lca)) last2*)

let lem_l3r_ind (lca s1 s2:st)
  : Lemma (requires (Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    (let s1' = inverse_st s1 in
                    consistent_branches_s2_gt0 lca s1 s2 /\
                    (let s2' = inverse_st s2 in
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last1) /\ Rem? (snd last2) /\ get_ele last2 = get_ele last1 /\
                    //is_prefix (ops_of lca) (ops_of s1) /\
                    //is_prefix (ops_of lca) (ops_of s2') /\
                    //not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1') (v_of s2)))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let s2' = inverse_st s2 in  //check why this line is needed
  lem_last (ops_of s2);
  let s1' = inverse_st s1 in //check why this line is needed
  lem_last (ops_of s1);
  lem_apply_log init_st (ops_of s1)

let rec trial (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    //length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    //(let s1' = inverse_st s1 in
                    Rem? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2 /\ 
                    //consistent_branches lca (do_st s1' last1) s2 /\
                    //consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2)
        
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1)]) =
  if ops_of s1 = ops_of lca then ()
  else 
    (let s1' = inverse_st s1 in
     lem_apply_log init_st (ops_of s1);
     pre1_pre2_s1 lca s1 s2;     
     assume (consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
             //consistent_branches lca s1' s2 /\
             consistent_branches lca (do_st s1' last1) s2);
     trial lca s1' s2 last1 last2; 
     lem_last (ops_of s1); ())
  
let rec lem_l2r' (lca s1 s2:st)
 : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Rem? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))
         (decreases %[length (ops_of s1)]) =
   let _, last2 = un_snoc (ops_of s2) in
   if ops_of s1 = ops_of lca then
     (let s2' = inverse_st s2 in
      pre1_pre2_s2 lca s1 s2;
      lem_l2r_s10 lca s1 s2' last2) 
   else 
     (let _, last1 = un_snoc (ops_of s1) in
      not_add_eq lca s1 s2;
      assert (~ (Add? (snd last1) /\ get_ele last1 = get_ele last2)); 
      let s1' = inverse_st s1 in
      let s2' = inverse_st s2 in
      if Rem? (snd last1) && get_ele last1 = get_ele last2 then
        (lem_last (ops_of s1);
         lem_last (ops_of s2);
         pre1_pre2_s1 lca s1 s2;
         pre1_pre2_s2 lca s1 s2;
         inverse_diff_id_s1'_s2' (ops_of lca) (ops_of s1) (ops_of s2);
         lem_diff (ops_of s1) (ops_of lca);
         lem_diff (ops_of s2) (ops_of lca);
         trial lca s1' s2' last1 last2)
      else if get_ele last1 <> get_ele last2 then
        (pre1_pre2_s1 lca s1 s2;
         lem_l2r_neq_p2 lca s1 s2;
         lem_l2r' lca s1' s2;
         lem_l2r_ind lca s1 s2)
      else ())

let lem_l2r (lca s1 s2:st)
 : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Rem? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     Second_then_first? (resolve_conflict last1 last2) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
 lem_l2r' lca s1 s2
 
#push-options "--z3rlimit 200"
let linearizable_gt0_s2' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     Second_then_first? (resolve_conflict last1 last2) /\
                     consistent_branches lca s1 (inverse_st s2)))
        
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  if Add? (snd last2) then () //done
  else lem_l2r lca s1 s2 //done

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = S.set nat & S.set nat

// init state 
let init_st_s = (S.empty, S.empty)

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s =
  match op with
  |(_, Add ele) -> (S.add ele (fst s), snd s)
  |(_, Rem ele) -> if S.mem ele (fst s) then (fst s, S.add ele (snd s)) else s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  S.equal (fst st_s) (fst st) /\
  S.equal (snd st_s) (snd st)

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()

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
