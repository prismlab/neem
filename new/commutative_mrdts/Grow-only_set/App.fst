module App

module S = Set_extended

#set-options "--query_stats"
// the concrete state type
type concrete_st = S.set nat

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
// (the only operation is Add, so nat is fine)
type app_op_t = nat

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
  S.add (snd op) s
  
let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()
           
//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res = First_then_second

// concrete merge operation
let concrete_merge (lca s1 s2:concrete_st) : Tot concrete_st =
  S.union lca (S.union s1 s2)

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

let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2)
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
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
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = S.set nat

// init state 
let init_st_s = S.empty

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s =
  S.add (snd op) s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////
//// Linearization properties //////

let conv_prop1 (s:concrete_st) (op1 op2:op_t)
  : Lemma (eq (do (do s op1) op2) (do (do s op2) op1)) = ()

let conv_prop2 (lca s1 s2:concrete_st) (op:op_t) 
  : Lemma (eq (do (concrete_merge lca s1 s2) op) (concrete_merge lca (do s1 op) s2)) = ()

let conv_prop3 (lca s1 s2:concrete_st) (op:op_t) 
  :  Lemma (eq (do (concrete_merge lca s1 s2) op) (concrete_merge lca s1 (do s2 op))) = 
  conv_prop2 lca s2 s1 op

let conv_prop4 (s:concrete_st)
  : Lemma (eq (concrete_merge s s s) s) = ()

let conv_prop5 (lca s1 s2:concrete_st) (op:op_t)
  : Lemma (eq (concrete_merge lca (do s1 op) (do s2 op)) (do (do (concrete_merge lca s1 s2) op) op)) = ()

////////////////////////////////////////////////////////////////
//// Linearization properties - intermediate merge //////

let inter_prop1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second)
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

let inter_prop2 (s s':concrete_st) (o1 o2:op_t) 
  : Lemma (requires eq (concrete_merge s (do s o2) s') (do s' o2))
          (ensures eq (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

let inter_prop3 (l a b c:concrete_st) (op op':op_t)
  : Lemma (requires eq (concrete_merge l a b) c /\ 
                    (forall (o:op_t). eq (concrete_merge l a (do b o)) (do c o)))
          (ensures eq (concrete_merge l a (do (do b op) op')) (do (do c op) op')) = ()

let inter_prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second /\
                    eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                      (do (do (do (do s o3') o3) o1) o2)) = ()

////////////////////////////////////////////////////////////////
//// Recursive merge condition //////

let rec_merge (s si si' sn sn':concrete_st)
  : Lemma (requires eq (concrete_merge s sn sn') (concrete_merge si sn (concrete_merge s si sn')) /\
                    eq (concrete_merge s sn sn') (concrete_merge si' sn' (concrete_merge s sn si')) /\
                    eq (concrete_merge s sn si') (concrete_merge si sn (concrete_merge s si si')) /\
                    eq (concrete_merge s si sn') (concrete_merge si' sn' (concrete_merge s si' si)))         
          (ensures (eq (concrete_merge s sn sn')
                       (concrete_merge (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn)))) = ()
          
////////////////////////////////////////////////////////////////
