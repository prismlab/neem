module App_comm

open SeqUtils
module S = Set_extended_new

#set-options "--query_stats"
// the concrete state type
type concrete_st = S.t (pos & nat)

let init_st = S.empty

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
type app_op_t:eqtype =
  |Add : nat -> app_op_t
  |Rem : nat -> app_op_t

let get_ele (o:op_t) : nat =
  match snd o with
  |Add e -> e
  |Rem e -> e

let mem_ele (ele:nat) (s:concrete_st) : bool =
  S.exists_s s (fun e -> snd e = ele)

let mem_id_s (id:nat) (s:concrete_st) : bool =
  S.exists_s s (fun e -> fst e = id)
  
// apply an operation to a state
let do (s:concrete_st) (o:op_t)
  : (r:concrete_st{(Rem? (snd o) ==> (forall e. S.mem e s /\ snd e <> get_ele o <==> S.mem e r)) /\
                   (Add? (snd o) ==> (forall e. S.mem e s \/ e = (fst o, get_ele o) <==> S.mem e r))}) =
  match o with
  |(id, Add e) -> S.insert (id, e) s
  |(id, Rem e) -> S.filter s (fun ele -> snd ele <> e)
  
let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if get_ele x = get_ele y && Add? (snd x) && Rem? (snd y) then 
    First_then_second 
  else Second_then_first

let resolve_conflict_prop (x y:op_t) 
  : Lemma (requires fst x <> fst y)
          (ensures (First_then_second? (resolve_conflict x y) <==> (Add? (snd x) /\ Rem? (snd y) /\ get_ele x = get_ele y)) /\
                   (Second_then_first? (resolve_conflict x y) <==> ((Add? (snd x) /\ Rem? (snd y) /\ get_ele x <> get_ele y) \/
                                                       (Add? (snd x) /\ Add? (snd y)) \/
                                                       (Rem? (snd x) /\ Rem? (snd y)) \/
                                                       (Rem? (snd x) /\ Add? (snd y)))))
  = ()

(*merge l a b == (intersect l a b) U (a - l) U (b - l)*)
let concrete_merge (lca s1 s2:concrete_st) 
  : Tot (m:concrete_st{forall e. S.mem e m <==>
                            ((S.mem e lca /\ S.mem e s1 /\ S.mem e s2) \/
                            (S.mem e s1 /\ not (S.mem e lca)) \/
                            (S.mem e s2 /\ not (S.mem e lca)))}) =
  let da = S.difference s1 lca in    //a - l
  let db = S.difference s2 lca in    //b - l
  let i_ab = S.intersection s1 s2 in
  let i_lab = S.intersection lca i_ab in            // intersect l a b
  S.union i_lab (S.union da db)          // (intersect l a b) U (a - l) U (b - l)

//operations x and y are commutative
let commutative (x y:op_t) =
  not (((Add? (snd x) && Rem? (snd y) && get_ele x = get_ele y) ||
        (Add? (snd y) && Rem? (snd x) && get_ele x = get_ele y))) 

let comm_symmetric (x y:op_t) 
  : Lemma (requires commutative x y)
          (ensures commutative y x) = ()

// if x and y are commutative ops, applying them in any order should give equivalent results
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
                      
let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca)
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()
          
///////////////////////////////////////////

#push-options "--z3rlimit 50"
let ls1s2_to_ls1's2' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2)
          (ensures consistent_branches lca (inverse_st s1) (inverse_st s2)) =
  lem_inverse (ops_of lca) (ops_of s1);
  lem_inverse (ops_of lca) (ops_of s2);
  inverse_diff_id_s1'_s2' (ops_of lca) (ops_of s1) (ops_of s2)

let ls1s2_to_ls1s2' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2)
          (ensures consistent_branches lca s1 (inverse_st s2)) =
  lem_inverse (ops_of lca) (ops_of s2);
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2)

let ls1s2_to_ls1's2 (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1_gt0 lca s1 s2)
          (ensures consistent_branches lca (inverse_st s1) s2) =
  lem_inverse (ops_of lca) (ops_of s1);
  inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2)

let pre1_pre2_s2 (lca s1 s2:st)
    : Lemma (requires consistent_branches_s2_gt0 lca s1 s2)
            (ensures consistent_branches lca s1 (inverse_st s2)) = 
  lem_inverse (ops_of lca) (ops_of s2);
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2)

let pre1_pre2_s1 (lca s1 s2:st)
    : Lemma (requires consistent_branches_s1_gt0 lca s1 s2)
            (ensures consistent_branches lca (inverse_st s1) s2) = 
  lem_inverse (ops_of lca) (ops_of s1);
  inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2)
  
////////////////////////////////////////////////////////////////

let lem_exists (lastop:op_t) (l:log)
  : Lemma (requires true)
          (ensures exists_triple lastop l <==> (Rem? (snd lastop) /\
                   (exists op. mem op l /\ Add? (snd op) /\ get_ele op = get_ele lastop /\ fst op <> fst lastop /\
                    (let _, suf = pre_suf l op in
                    (forall r. mem r suf /\ get_ele r = get_ele lastop ==> Add? (snd r))))))
  = ()

let rec lem_l2a_l1r_eq''_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    Add? (snd last2) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 
          (decreases length (ops_of lca)) =
  if length (ops_of lca) = 0 then ()
  else  
    (let l' = inverse_st lca in
     lem_l2a_l1r_eq''_base  l' l' l' last1 last2;
     mem_ele_id (last (ops_of lca)) (ops_of lca))

let rec lem_l2a_l1r_eq''_s10 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Add? (snd last2) /\ 
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2)]) =
  if ops_of s2 = ops_of lca then
     lem_l2a_l1r_eq''_base lca s1 s2 last1 last2
  else 
    lem_l2a_l1r_eq''_s10 lca s1 (inverse_st s2) last1 last2
     
let rec lem_l2a_l1r_eq'' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires Add? (snd last2) /\ Rem? (snd last1) /\ get_ele last1 = get_ele last2 /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2); length (ops_of s1)]) = 
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    lem_l2a_l1r_eq''_base lca s1 s2 last1 last2
  else if ops_of s1 = ops_of lca then
    lem_l2a_l1r_eq''_s10 lca s1 s2 last1 last2
  else (let s1' = inverse_st s1 in
        lem_inverse (ops_of lca) (ops_of s1); 
        lem_l2a_l1r_eq'' lca s1' s2 last1 last2)
        
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
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') op2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let pre2, op2, suf2 = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  let s2' = inverse_st_op s2 op2 in
  lem_exists last1 (diff (ops_of s2) (ops_of lca));
  lem_inverse (ops_of lca) (ops_of s1);
  lem_diff (ops_of s1) (ops_of lca);
  lem_suf_equal2_last (ops_of lca) (ops_of s1);
  lem_diff (ops_of s2) (ops_of lca);
  lem_suf_equal2 (ops_of lca) (ops_of s2) op2;
  lem_inverse_op (ops_of lca) (ops_of s2) op2;
  lem_l2a_l1r_eq'' lca (inverse_st s1) s2' last1 op2

////////////////////////////////////////////////////////////////

let rec lem_l1a_l2r_eq''_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2 /\ 
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 
          (decreases length (ops_of lca)) = 
  if length (ops_of lca) = 0 then ()
  else 
    (let l' = inverse_st lca in
     lem_l1a_l2r_eq''_base  l' l' l' last1 last2;
     mem_ele_id (last (ops_of lca)) (ops_of lca))

let rec lem_l1a_l2r_eq''_s20 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2 /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1)]) =
  if ops_of s1 = ops_of lca then
     lem_l1a_l2r_eq''_base lca s1 s2 last1 last2
  else 
    lem_l1a_l2r_eq''_s20 lca (inverse_st s1) s2 last1 last2
     
let rec lem_l1a_l2r_eq'' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2 /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1); length (ops_of s2)]) =
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    lem_l1a_l2r_eq''_base lca s1 s2 last1 last2
  else if ops_of s2 = ops_of lca then
    lem_l1a_l2r_eq''_s20 lca s1 s2 last1 last2
  else lem_l1a_l2r_eq'' lca s1 (inverse_st s2) last1 last2
        
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
                       (concrete_merge (v_of lca) (do (v_of s1') op1) (v_of s2)))) =
  let _, last2 = un_snoc (ops_of s2) in
  let pre1, op1, suf1 = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  let s1' = inverse_st_op s1 op1 in
  lem_exists last2 (diff (ops_of s1) (ops_of lca));
  lem_inverse (ops_of lca) (ops_of s2);
  lem_diff (ops_of s2) (ops_of lca);
  lem_suf_equal2_last (ops_of lca) (ops_of s2);
  lem_diff (ops_of s1) (ops_of lca);
  lem_suf_equal2 (ops_of lca) (ops_of s1) op1;
  lem_inverse_op (ops_of lca) (ops_of s1) op1;
  lem_l1a_l2r_eq'' lca s1' (inverse_st s2) op1 last2
  
////////////////////////////////////////////////////////////////

let rem_add_lastop_neq_ele (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    consistent_branches_s2_gt0 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    fst last1 <> fst last2 /\
                    Add? (snd last1) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    ~ (Rem? (snd last2) /\ get_ele last1 = get_ele last2))) =
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
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
  
  assert (Rem? (snd last2) /\ get_ele last1 = get_ele last2 ==> commutative_seq last1 suf); 
  assert (Rem? (snd last2) /\ get_ele last1 = get_ele last2 ==> not (commutative last1 last2));
  assert (Rem? (snd last2) /\ get_ele last1 = get_ele last2 ==> First_then_second? (resolve_conflict last1 last2));
  assert (Rem? (snd last2) /\ get_ele last1 = get_ele last2 ==> 
          (not (commutative last1 last2) /\
          First_then_second? (resolve_conflict last1 last2) /\
          commutative_seq last1 suf));
  assert (Rem? (snd last2) /\ get_ele last1 = get_ele last2 ==> 
           exists_triple last2 (diff (ops_of s1) (ops_of lca)));
  ()
  
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
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  resolve_conflict_prop last1 last2;
  assert (Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2);
  if Rem? (snd last1) then ()
    else (assert (Add? (snd last1)); 
          rem_add_lastop_neq_ele lca s1 s2;
          assert (~ (Rem? (snd last2) /\ get_ele last1 = get_ele last2)); ()); 
  assert (~ (Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2)); 
  ()

////////////////////////////////////////////////////////////////

let lem_l2a''_s20_ind_l1r_eq (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s2 = ops_of lca /\ 
                    length (ops_of s1) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    Add? (snd last2) /\ Rem? (snd last1) /\ get_ele last1 = get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) /\
                    not (mem_id (fst last2) (ops_of lca)) /\

                    (let s1' = inverse_st s1 in
                     consistent_branches lca s1' s2 /\
                     not (exists_triple last2 (diff (ops_of s1') (ops_of lca))) /\                  
                     eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2))))
                     
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) = 
  let _, last1 = un_snoc (ops_of s1) in
  lem_inverse (ops_of lca) (ops_of s1);
  lem_diff (ops_of s1) (ops_of lca); 
  lem_suf_equal2_last (ops_of lca) (ops_of s1); 
  lem_l2a_l1r_eq'' lca (inverse_st s1) s2 last1 last2

#push-options "--z3rlimit 50"
let lem_l2a''_s20_ind (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s2 = ops_of lca /\ 
                    length (ops_of s1) > length (ops_of lca) /\
                    Add? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    
                    (let s1' = inverse_st s1 in
                     consistent_branches lca s1' s2 /\
                     not (exists_triple last2 (diff (ops_of s1') (ops_of lca))) /\                  
                     eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2))))
                     
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) = 
  let _, last1 = un_snoc (ops_of s1) in
  if Rem? (snd last1) && get_ele last1 <> get_ele last2 then ()
  else if Add? (snd last1) then ()
  else lem_l2a''_s20_ind_l1r_eq lca s1 s2 last2
#pop-options
  
let rec lem_l2a''_s20 (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s2 = ops_of lca /\
                    Add? (snd last2) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1)]) = 
  if ops_of s1 = ops_of lca then ()
  else 
    (let s1' = inverse_st s1 in
     pre1_pre2_s1 lca s1 s2;
     assert (consistent_branches lca s1' s2);
     let pre1, last1 = un_snoc (ops_of s1) in
     let pre1d, last1d = un_snoc (diff (ops_of s1) (ops_of lca)) in
     lem_diff (ops_of s1) (ops_of lca);
     assert (last1 = last1d);
     assert ((diff (ops_of s1') (ops_of lca)) = pre1d);
       //lem_not_exists_add last2 (diff (ops_of s1) (ops_of lca));
     assert (not (exists_triple last2 (diff (ops_of s1') (ops_of lca))));
     lem_inverse (ops_of lca) (ops_of s1);
     lem_l2a''_s20 lca s1' s2 last2;
     lem_l2a''_s20_ind lca s1 s2 last2)
     
let rec lem_l2a' (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    Add? (snd last2) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) 
          (decreases %[length (ops_of s2)]) =
  if ops_of s2 = ops_of lca then
    lem_l2a''_s20 lca s1 s2 last2
  else 
    (pre1_pre2_s2 lca s1 s2;
     lem_l2a' lca s1 (inverse_st s2) last2)
     
let lem_l2a (lca s1 s2:st)
 : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Add? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
   let _, last2 = un_snoc (ops_of s2) in
   let s2' = inverse_st s2 in
   pre1_pre2_s2 lca s1 s2;
   lem_diff (ops_of s2) (ops_of lca); 
   lem_suf_equal2_last (ops_of lca) (ops_of s2); 
   lem_l2a' lca s1 s2' last2;
   assert (S.mem (fst last2, get_ele last2) (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2));
   assert (S.mem (fst last2, get_ele last2) (concrete_merge (v_of lca) (v_of s1) (v_of s2)));
   ()

let lem_l2r_s10p (lca s1 s2:st)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Rem? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
          (ensures (let s2' = inverse_st s2 in
                    let _, last2 = un_snoc (ops_of s2) in
                    consistent_branches lca s1 s2' /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of s2')) /\
                    not (mem_id (fst last2) (ops_of s1)))) =
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  lem_id_s2' (ops_of lca) (ops_of s1) (ops_of s2)

let lem_common_pre1_s2' (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\
                    not (mem_id (fst last2) (ops_of s2)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of s1)) /\
                   ops_of s1 = ops_of lca /\
                   not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   is_prefix (ops_of lca) (ops_of s2))
          (ensures (let s2' = inverse_st s2 in
                   consistent_branches lca s1 s2' /\ 
                   not (mem_id (fst last2) (ops_of s2')) /\
                   is_prefix (ops_of lca) (ops_of s2'))) =
  lem_inverse (ops_of lca) (ops_of s2);
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2)

#push-options "--z3rlimit 50"
let rec lem_l2r_s10 (lca s1 s2:st) (last2:op_t)
 : Lemma (requires consistent_branches lca s1 s2 /\ 
                   ops_of s1 = ops_of lca /\
                   Rem? (snd last2) /\
                   not (mem_id (fst last2) (ops_of lca)) /\
                   not (mem_id (fst last2) (ops_of s1)) /\
                   not (mem_id (fst last2) (ops_of s2)) /\
                   not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   is_prefix (ops_of lca) (ops_of s2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
         (decreases %[length (ops_of s2)]) =
   if ops_of s2 = ops_of lca then ()
   else 
     (lem_common_pre1_s2' lca s1 s2 last2;
      lem_l2r_s10 lca s1 (inverse_st s2) last2)
#pop-options

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
  resolve_conflict_prop last2 last1;
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> 
                First_then_second? (resolve_conflict last2 last1));
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> 
                not (commutative last2 last1) /\
                First_then_second? (resolve_conflict last2 last1) /\
                commutative_seq last1 suf);
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> exists_triple last2 (diff (ops_of s1) (ops_of lca)));
  assert (~ (Add? (snd last1) /\ get_ele last1 = get_ele last2)); ()

let lem_l2r_neq_p1 (lca s1 s2:st)
 : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2)
         (ensures consistent_branches_s2_gt0 lca (inverse_st s1) s2) =
 lem_inverse (ops_of lca) (ops_of s1);
 inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
 lastop_diff (ops_of lca) (ops_of s1)

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
  assert (count_assoc_fst (fst op') (snoc pre op' ++ suf) = 1);
  lem_count_1 pre suf pre' (snoc suf' last1) op';
  
  assert (length suf = length (snoc suf' last1));
  lemma_append_inj (snoc pre op') suf (snoc pre' op') (snoc suf' last1);
  assert (suf = snoc suf' last1);
  lemma_mem_snoc suf' last1;
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
                   (lem_l2r_neq_p1 lca s1 s2;
                    (not (exists_triple last2 (diff (ops_of s1') (ops_of lca))))))) = 
 lem_l2r_neq_p1 lca s1 s2;
 let s1' = inverse_st s1 in
 let _, last2 = un_snoc (ops_of s2) in
 let pre1, last1 = un_snoc (ops_of s1) in
 let pre1d, last1d = un_snoc (diff (ops_of s1) (ops_of lca)) in
 lem_diff (ops_of s1) (ops_of lca);
 assert (last1 = last1d);
 assert (get_ele last1d <> get_ele last2);
 assert ((diff (ops_of s1') (ops_of lca)) = pre1d);
 lem_l2r_neq_p2' (diff (ops_of s1) (ops_of lca)) last2

#push-options "--z3rlimit 50"
let rec lem_l2r (lca s1 s2:st)
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
      lem_l2r_s10p lca s1 s2;
      lem_l2r_s10 lca s1 s2' last2) 
   else 
     (let _, last1 = un_snoc (ops_of s1) in
      not_add_eq lca s1 s2;
      assert (~ (Add? (snd last1) /\ get_ele last1 = get_ele last2));
      let s1' = inverse_st s1 in
      if Rem? (snd last1) && get_ele last1 = get_ele last2 then
        (lem_last (ops_of s2);
         lem_last (ops_of s1))
        //lem_l2r_l1r_eq lca s1 s2
      else if get_ele last1 <> get_ele last2 then
        (lem_inverse (ops_of lca) (ops_of s1);
         inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
         lastop_diff (ops_of lca) (ops_of s1);
         lem_l2r_neq_p2 lca s1 s2;
         lem_l2r lca s1' s2;
         lem_last (ops_of s2);
         lem_last (ops_of s1))
      else ())
#pop-options

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
  let _, last2 = un_snoc (ops_of s2) in
  if Add? (snd last2) then
    lem_l2a lca s1 s2
  else lem_l2r lca s1 s2
  
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
let concrete_st_s = S.t nat

// init state 
let init_st_s = S.empty
 
// apply an operation to a state 
let do_s (st_s:concrete_st_s) (o:op_t) : concrete_st_s =
  match snd o with
  |(Add e) -> S.insert e st_s
  |(Rem e) -> S.filter st_s (fun ele -> ele <> e) 

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  (forall e. S.mem e st_s <==> mem_ele e st)

//initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = 
  if Add? (snd op) then 
    (if S.mem (get_ele op) st_s then () else ()) 
  else ()

////////////////////////////////////////////////////////////////

let merge_pre (lca s1 s2:concrete_st) =
  (forall e. (S.mem e s1 /\ S.mem e s2) ==> S.mem e lca)

let rec remove_op (op:op_t) (l:log) 
  : Tot (r:log {forall e. mem e r <==> mem e l /\ e <> op})
    (decreases length l) =
  if length l = 0 then empty
  else if head l = op then remove_op op (tail l)
  else (let r = (remove_op op (tail l)) in
        mem_cons (head l) r;
        cons (head l) r)

let rec diff_op (s1 l:log) 
  : Tot (d:log {forall e. mem e d <==> mem e s1 /\ not (mem e l)}) 
    (decreases length l) =
  if length l = 0 then s1 
  else diff_op (remove_op (head l) s1) (tail l)

#push-options "--z3rlimit 100"
let rec convergence (lca s1' s2:concrete_st) (ls1' ls2:log) (o:op_t)
  : Lemma (requires distinct_ops ls1' /\ distinct_ops ls2 /\
                    s1' == apply_log lca ls1' /\
                    s2 == apply_log lca ls2 /\
                    (forall id. mem_id id ls1' ==> not (mem_id id ls2)) /\
                    not (mem_id (fst o) ls1'))
          (ensures eq (concrete_merge lca (do s1' o) s2)
                      (concrete_merge s1' (concrete_merge lca s1' s2) (do s1' o)))
          (decreases %[length ls1'; length ls2]) = 
  let ele = (fst o, get_ele o) in
  let lhs = (concrete_merge lca (do s1' o) s2) in
  let rhs = (concrete_merge s1' (concrete_merge lca s1' s2) (do s1' o)) in
  let da = S.difference (do s1' o) lca in
  let db = S.difference s2 lca in
  let db_rhs = S.difference (do s1' o) s1' in
  let i' = S.intersection lca (S.intersection s1' s2) in
  let i = S.intersection lca (S.intersection (do s1' o) s2) in
  if Rem? (snd o) then
    (admit();assert (forall e. S.mem e (concrete_merge s1' (concrete_merge lca s1' s2) (do s1' o)) ==>
                  S.mem e (concrete_merge lca (do s1' o) s2));
     if S.exists_s s1' (fun e -> snd e = get_ele o && S.mem e s2 && not (S.mem e lca)) then 
      (assert (length ls1' > 0 /\ length ls2 > 0);
       let ls1'', lastop1 = un_snoc ls1' in
       let s1'' = apply_log lca ls1'' in
       split_prefix lca ls1'' ls1';
       let ls2', lastop2 = un_snoc ls2 in
       let s2' = apply_log lca ls2' in
       split_prefix lca ls2' ls2;
       distinct_invert_append ls1'' (create 1 lastop1);
       distinct_invert_append ls2' (create 1 lastop2);
       lemma_append_count_assoc_fst ls1'' (create 1 lastop1);
       lemma_append_count_assoc_fst ls2' (create 1 lastop2);
       if length ls2' = 0 then 
         (if Add? (snd lastop2) && get_ele lastop2 = get_ele o then 
           (convergence lca s1'' s2 ls1'' ls2 o;
            assert (not (S.mem (fst lastop2, get_ele lastop2) s1'')); 
            assert ((fst lastop1, get_ele lastop1) <> (fst lastop2, get_ele lastop2)); 
            assert (not (S.mem (fst lastop2, get_ele lastop2) s1')); //todo
            ())
          else convergence lca s1'' s2 ls1'' ls2 o)
       else 
         (if Add? (snd lastop2) && get_ele lastop2 = get_ele o then 
           (convergence lca s1'' s2 ls1'' ls2 o; 
            convergence lca s1' s2' ls1' ls2' o;
            convergence lca s1'' s2 ls1'' ls2 lastop1)
          else 
            (convergence lca s1' s2' ls1' ls2' o; ())))
     else ())
  else 
    (if S.mem ele lhs then 
      (();if S.mem ele da || S.mem ele db then ()
       else if S.mem ele i' then ()
       else if S.mem ele db then () 
       else ())
     else if S.mem ele rhs then
       (if S.mem ele db_rhs then 
          (assert (length ls1' > 0);
           let ls1'', lastop1 = un_snoc ls1' in
           let s1'' = apply_log lca ls1'' in
           let i'' = S.intersection lca (S.intersection (do s1'' o) s2) in
           let da'' = S.difference (do s1'' o) lca in
           split_prefix lca ls1'' ls1';
           distinct_invert_append ls1'' (create 1 lastop1);
           lemma_append_count_assoc_fst ls1'' (create 1 lastop1);
           if Add? (snd lastop1) || (Rem? (snd lastop1) && get_ele lastop1 <> get_ele o) then 
             convergence lca s1'' s2 ls1'' ls2 o
           else 
             (assert (S.mem ele rhs); 
              assert (Rem? (snd lastop1) /\ get_ele lastop1 = get_ele o);
              assert (not (S.mem ele s1')); 
              convergence lca s1'' s2 ls1'' ls2 o; 
              (*assume (S.mem ele (do s1'' o)); 
              assume (not (S.mem ele i''));
              assume (not (S.mem ele s2)); 
              assume (not (S.mem ele db));
              assume (not (S.mem ele da''));
              assume (S.mem ele lca);
              assume (not (S.mem ele (concrete_merge lca (do s1'' o) s2))); *)
              
              assert (S.mem ele lca \/ not (S.mem ele lca));
              if not (S.mem ele lca) then ()
              else 
                (//assume (S.mem ele lca);
                 //assume (not (S.mem ele da''));
                 assert (S.mem ele s1''); 
                 assume ( (S.mem ele lhs)); //todo
                 ())))
         else ())
      else ())
 

(*let rec convergence1 (lca s1' s2:st) (o:op_t)
  : Lemma (requires (forall e. mem e (ops_of lca) ==> (mem e (ops_of s1'))) /\
                    (forall e. mem e (ops_of lca) ==> mem e (ops_of s2)) /\
                    (forall e e1. mem e (ops_of s1') /\ not (mem e (ops_of lca)) /\ 
                             mem e1 (ops_of s2) /\ not (mem e1 (ops_of lca)) ==> fst e <> fst e1))
          (ensures eq (concrete_merge (v_of lca) (do (v_of s1') o) (v_of s2)) 
                      (concrete_merge (v_of s1') (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (do (v_of s1') o)))
          (decreases %[length (ops_of s1'); length (ops_of s2)]) =
  let ele = (fst o, get_ele o) in
  let lhs = (concrete_merge (v_of lca) (do (v_of s1') o) (v_of s2)) in
  let rhs = (concrete_merge (v_of s1') (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (do (v_of s1') o)) in
  let da = S.difference (do (v_of s1') o) (v_of lca) in
  let da' = S.difference (v_of s1') (v_of lca) in
  let db = S.difference (v_of s2) (v_of lca) in
  let i_rhs = S.intersection (v_of s1') (S.intersection (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (do (v_of s1') o)) in
  let da_rhs = S.difference (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (v_of s1') in
  let db_rhs = S.difference (do (v_of s1') o) (v_of s1') in
  let i' = S.intersection (v_of lca) (S.intersection (v_of s1') (v_of s2)) in
  let da_rhs = S.difference (do (v_of s1') o) (v_of s1') in
  if Add? (snd o) then
    admit()
  else 
    (assume (Rem? (snd o));
     assume (forall e. S.mem e (concrete_merge (v_of s1') (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (do (v_of s1') o)) ==>
                  S.mem e (concrete_merge (v_of lca) (do (v_of s1') o) (v_of s2)));
     if S.exists_s (v_of s1') (fun e -> snd e = get_ele o && S.mem e (v_of s2) && not (S.mem e (v_of lca))) then 
       (if (forallb (fun e -> mem e (ops_of s1')) (ops_of lca)) then () 
        else 
          (admit();assert (length (ops_of s1') > length (ops_of lca));
           admit()))
     else admit())*) //done

#push-options "--z3rlimit 200"
let rec convergence1 (lca s1' s2:st) (o:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    not (mem_id (fst o) (ops_of s1')))
          (ensures eq (concrete_merge (v_of lca) (do (v_of s1') o) (v_of s2)) 
                      (concrete_merge (v_of s1') (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (do (v_of s1') o)))
          (decreases %[length (ops_of s1'); length (ops_of s2)]) =
  let ele = (fst o, get_ele o) in
  let lhs = (concrete_merge (v_of lca) (do (v_of s1') o) (v_of s2)) in
  let rhs = (concrete_merge (v_of s1') (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (do (v_of s1') o)) in
  let da = S.difference (do (v_of s1') o) (v_of lca) in
  let da' = S.difference (v_of s1') (v_of lca) in
  let db = S.difference (v_of s2) (v_of lca) in
  let i_rhs = S.intersection (v_of s1') (S.intersection (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (do (v_of s1') o)) in
  let da_rhs = S.difference (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (v_of s1') in
  let db_rhs = S.difference (do (v_of s1') o) (v_of s1') in
  let i' = S.intersection (v_of lca) (S.intersection (v_of s1') (v_of s2)) in
  let da_rhs = S.difference (do (v_of s1') o) (v_of s1') in
  if Add? (snd o) then 
    (if S.mem ele lhs then 
      (if S.mem ele da || S.mem ele db then
        (assert (not (S.mem ele (v_of lca)));
        if S.mem ele (v_of s1') then 
          ((*assert (S.mem ele da');
           assert (S.mem ele i_rhs);*) ())
        else ((*assert (S.mem ele rhs);*) ()))
      else if S.mem ele i' then 
        (if not (S.mem ele (v_of s1')) then () else ()))
      else if S.mem ele db then ()
    else if S.mem ele rhs then 
      (if S.mem ele db_rhs then 
        (let s1'' = inverse_st s1' in 
         assert (not (S.mem ele (v_of s1'))); 
         let pre, lastop = un_snoc (ops_of s1') in
         let db_new = S.difference (do (v_of s1'') o) (v_of lca) in
         lemma_mem_snoc pre lastop;
         lem_last (ops_of s1');
         if Add? (snd lastop) || Rem? (snd lastop) && get_ele lastop <> get_ele o then 
           (lem_diff (ops_of s1') (ops_of lca);
            inverse_diff_id_s1' (ops_of lca) (ops_of s1') (ops_of s2);
            convergence1 lca s1'' s2 o)
         else 
           (assert (S.mem ele rhs); 
            lem_diff (ops_of s1') (ops_of lca);
            inverse_diff_id_s1' (ops_of lca) (ops_of s1') (ops_of s2);
            convergence1 lca s1'' s2 o; 
            //assert (S.mem ele (v_of lca)); 
            assume (S.mem ele lhs);
            ())) //check
       else ()) //done
    else ()) //done
  else 
    (assert (Rem? (snd o)); admit();
     (*assert (forall e. S.mem e (concrete_merge (v_of s1') (concrete_merge (v_of lca) (v_of s1') (v_of s2)) (do (v_of s1') o)) ==>
                  S.mem e (concrete_merge (v_of lca) (do (v_of s1') o) (v_of s2)));*)
     if S.exists_s (v_of s1') (fun e -> snd e = get_ele o && S.mem e (v_of s2) && not (S.mem e (v_of lca))) then 
       (let s1'' = inverse_st s1' in 
        let pre, lastop = un_snoc (ops_of s1') in
        lem_diff (ops_of s1') (ops_of lca);
        
        let s2' = inverse_st s2 in        
        let pre2, lastop2 = un_snoc (ops_of s2) in
        lem_diff (ops_of s2) (ops_of lca);
        lem_inverse (ops_of lca) (ops_of s2);
        if ops_of s2' = ops_of lca then 
           (if Add? (snd lastop2) && get_ele lastop2 = get_ele o then 
             (inverse_diff_id_s1' (ops_of lca) (ops_of s1') (ops_of s2);
              convergence1 lca s1'' s2 o; 
              assert (not (S.mem (fst lastop2, get_ele lastop2) (v_of s1''))); 
              assert ((fst lastop, get_ele lastop) <> (fst lastop2, get_ele lastop2));
              assert (not (S.mem (fst lastop2, get_ele lastop2) (v_of s1')));
              ()) //done
            else convergence1 lca s1'' s2 o) //done
        else 
          (if Add? (snd lastop2) && get_ele lastop2 = get_ele o then 
            (lem_diff (ops_of s2) (ops_of lca);
             lem_diff (ops_of s1') (ops_of lca);
             lem_inverse (ops_of lca) (ops_of s2);
             inverse_diff_id_s1' (ops_of lca) (ops_of s1') (ops_of s2);
             inverse_diff_id_s2' (ops_of lca) (ops_of s1') (ops_of s2);
             convergence1 lca s1'' s2 o; 
             convergence1 lca s1' s2' o;
             assert (forall e. S.mem e (S.difference (v_of s2') (v_of lca)) /\ snd e = get_ele o ==> 
                          not (S.mem e (v_of s1')) /\ S.mem e lhs);
             convergence1 lca s1'' s2 lastop; 
             (*assert (forall e. S.mem e (S.difference (v_of s2) (v_of lca)) /\ snd e = get_ele o ==>
                          not (S.mem e (v_of s1'')));*)
             assert (fst lastop <> fst lastop2);
             //assert (not (S.mem (fst lastop2, get_ele lastop2) (v_of s1'))); 
             ())
           else 
             (inverse_diff_id_s2' (ops_of lca) (ops_of s1') (ops_of s2);
              convergence1 lca s1' s2' o)))
     else ()) //done

let rec convergence2 (lca s2 s3 lca' s1':st)
  : Lemma (requires consistent_branches lca' s3 s1' /\
                    consistent_branches lca s1' s2)
          (ensures eq (concrete_merge (v_of lca) (concrete_merge (v_of lca') (v_of s3) (v_of s1')) (v_of s2)) 
                      (concrete_merge (v_of s1') 
                                      (concrete_merge (v_of lca) (v_of s1') (v_of s2)) 
                                      (concrete_merge (v_of lca') (v_of s3) (v_of s1')))) 
          (decreases length (ops_of s3)) =
  if ops_of s3 = ops_of lca' then ()
  else 
    (let s3' = inverse_st s3 in
     let pre, lastop = un_snoc (ops_of s3) in
     lem_last (ops_of s3);
     lemma_mem_snoc pre lastop; 
     lem_inverse (ops_of lca') (ops_of s3);
     inverse_diff_id_s1' (ops_of lca') (ops_of s3) (ops_of s1');
     lastop_diff (ops_of lca') (ops_of s3);
     if Add? (snd lastop) then
       (assume (not (mem_id_s (fst lastop) (v_of lca)));
        convergence2 lca s2 s3' lca' s1')
     else
       (assume (merge_pre (v_of lca) (v_of s1') (v_of s2));
        convergence2 lca s2 s3' lca' s1')) 
#pop-options
