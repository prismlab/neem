module App

module M = Map_extended
module S = FStar.Set

#set-options "--query_stats"

// the concrete state type
// It is a list of unique elements
type concrete_st = M.t nat (S.set nat)

//initial state
let init_st = M.const S.empty

let sel (s:concrete_st) k = if M.contains s k then M.sel s k else S.empty

let eq (a b:concrete_st) =
  (forall id. M.contains a id = M.contains b id /\
         S.equal (sel a id) (sel b id))

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
// (the only operation is Add, so nat * nat is fine)
type app_op_t = nat * nat

let key (op:op_t) = fst (snd op)

let value (op:op_t) = snd (snd op)

let do (s:concrete_st) (op:op_t) =
  let (ts,(k,v)) = op in
  M.upd s k (S.union (S.singleton v) (sel s k))

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res = First_then_second

// concrete merge operation
let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  let keys = S.union (M.domain lca) (S.union (M.domain s1) (M.domain s2)) in
  let u:concrete_st = M.const_on keys S.empty in
  M.iter_upd (fun k v -> S.union (sel lca k) (S.union (sel s1 k) (sel s2 k))) u

let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = ()

let linearizable_s1_0_s2_0_base_direct (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)       
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

#push-options "--z3rlimit 50"
let linearizable_gt0_s1 (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\
                    consistent_branches lca (inverse_st s1) s2 /\
                    consistent_branches lca (inverse_st s1) (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2)))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = ()

let linearizable_gt0_s2 (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\
                    consistent_branches lca s1 (inverse_st s2) /\
                    consistent_branches lca (inverse_st s1) (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2)))
          (ensures (let _, last2 = un_snoc (ops_of s2) in                   
                   eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = () 
#pop-options

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s_direct = concrete_st

// init state 
let init_st_s_direct = init_st

// apply an operation to a state 
let do_s_direct (s:concrete_st_s_direct) (op:op_t) : concrete_st_s_direct = 
  do s op

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm_direct (st_s:concrete_st_s_direct) (st:concrete_st) = st_s == st

//initial states are equivalent
let initial_eq_direct _
  : Lemma (ensures eq_sm_direct init_st_s_direct init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq_direct (st_s:concrete_st_s_direct) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm_direct st_s st)
          (ensures eq_sm_direct (do_s_direct st_s op) (do st op)) = ()
  
////////////////////////////////////////////////////////////////
//// Linearization properties //////

let merge1 (lca s1 s2:concrete_st)  =
  let keys = S.union (M.domain lca) (S.union (M.domain s1) (M.domain s2)) in
  let u:concrete_st = M.const_on keys S.empty in
  M.iter_upd (fun k v -> S.union (sel lca k) (S.union (sel s1 k) (sel s2 k))) u

let conv_prop1 (s:concrete_st) (op1 op2:op_t)
  : Lemma (eq (do (do s op1) op2) (do (do s op2) op1)) = ()

let conv_prop2 (lca s1 s2:concrete_st) (op:op_t) 
  : Lemma (eq (do (merge1 lca s1 s2) op) (merge1 lca (do s1 op) s2)) = ()

let conv_prop3 (lca s1 s2:concrete_st) (op:op_t) 
  :  Lemma (eq (do (merge1 lca s1 s2) op) (merge1 lca s1 (do s2 op))) = 
  conv_prop2 lca s2 s1 op

let conv_prop4 (s:concrete_st)
  : Lemma (eq (merge1 s s s) s) = ()

let conv_prop5 (lca s1 s2:concrete_st) (op:op_t)
  : Lemma (ensures eq (merge1 lca (do s1 op) (do s2 op)) (do (do (merge1 lca s1 s2) op) op)) = ()
  
////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////
//// Linearization properties - intermediate merge //////

#push-options "--z3rlimit 100"
let prop1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (ensures eq (merge1 (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

let prop2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires eq (merge1 s (do s o2) s') (do s' o2) /\
                    eq (merge1 l s (do l o3)) s')
          (ensures eq (merge1 (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

let prop3 (s s':concrete_st)
  : Lemma (requires eq (merge1 s s s') s' /\
                    (forall o2'. eq (merge1 s (do s o2') s') (do s' o2')))
          (ensures (forall o2 o2'. (fst o2 <> fst o2') ==> eq (merge1 s (do (do s o2') o2) s') (do (do s' o2') o2))) = ()

let lem_merge3 (l a b c:concrete_st) (op op':op_t) //cond3
  : Lemma 
    (requires eq (merge1 l a b) c /\ 
              (forall (o:op_t). eq (merge1 l a (do b o)) (do c o)))
    (ensures eq (merge1 l a (do (do b op) op')) (do (do c op) op')) = ()

let prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t)
  : Lemma (requires (exists a b. eq (merge1 l a b) s) /\ //extra
                    eq (merge1 (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (merge1 (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                   (do (do (do (do s o3') o3) o1) o2)) = ()

let lem_merge4 (s s':concrete_st) (op op':op_t) //cond4
  : Lemma (requires eq (merge1 (do s op) (do s' op) (do s op)) (do s' op))
          (ensures eq (merge1 (do s op) (do (do s' op') op) (do s op)) (do (do s' op') op)) = () 

let idempotence (s:concrete_st) //automatic
  : Lemma (eq (merge1 s s s) s) = ()

let prop5' (l s s':concrete_st) (o o3:op_t)
  : Lemma (requires eq (merge1 s s s') s' /\
                    eq (merge1 l s (do l o3)) s')
          (ensures eq (merge1 s s (do s' o)) (do s' o)) = ()
          
let prop5 (s s':concrete_st)
  : Lemma (requires (exists a b. eq (merge1 s a b) s')) //extra
          (ensures eq (merge1 s s s') s' /\ 
                   eq (merge1 s s' s) s') = ()
          
////////////////////////////////////////////////////////////////

(*let convergence1 (lca s1' s2:st) (o:op_t)
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
                                       (concrete_merge (v_of lca') (v_of s1') (v_of s2)))) = ()*)
