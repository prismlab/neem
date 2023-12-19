module App

module S = Set_extended

#set-options "--query_stats"
// the concrete state type
type concrete_st = S.t nat

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
  S.add (snd (snd op)) s

//conflict resolution
let rc (o1:op_t) (o2:op_t{distinct_ops o1 o2}) = Either

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  S.union l (S.union a b)

/////////////////////////////////////////////////////////////////////////////

let no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3))) = ()

let relaxed_comm (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

let non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = ()
         
let cond_comm (o1:op_t) (o2:op_t{distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2))}) (o3:op_t) = true

let cond_comm_base (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ cond_comm o1 o2 o3)
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

#push-options "--z3rlimit 50 --ifuel 3 --split_queries on_failure"
let cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:log)
  : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ cond_comm o1 o2 o3 /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3)) = ()

/////////////////////////////////////////////////////////////////////////////

let merge_comm (l a b:concrete_st)
  : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

let merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s) = ()

let fast_fwd_base (a:concrete_st) (op:op_t)
  : Lemma (ensures eq (do a op) (merge a a (do a op))) = ()

let fast_fwd_ind (a b:concrete_st) (o2 o2':op_t) (l:log)
  : Lemma (requires do b o2 == apply_log a l /\
                    eq (do b o2) (merge a a (do b o2)))
          (ensures eq (do (do b o2') o2) (merge a a (do (do b o2') o2))) = ()

let rc_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let rc_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

let comm_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o2' o1 /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures ((eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) ==>
                     eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) /\
                    (eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) ==>
                     eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l a (do (do b o2') o2)) o1)))) = ()

let comm_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o1' o2 /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                             
          (ensures ((eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) ==>
                     eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) /\
                    (eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) ==>
                     eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do a o1') (do b o2)) o1)))) = ()

let rc_base (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()
  
let comm_base (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2)
          (ensures (eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) ==>
                    eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) /\
                   (eq (merge l (do l o1) (do l o2)) (do (do l o2) o1) ==>
                    eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o2) o1))) = ()

let rc_intermediate1 (l:concrete_st) (o1 o2 o o':op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\ distinct_ops o' o2)
          (ensures eq (merge (do l o') (do (do l o') o1) (do (do (do l o) o') o2)) (do (do (do (do l o) o') o1) o2)) = ()

let rc_intermediate2 (l l' a b:concrete_st) (o1 o2 o o':op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\ distinct_ops o' o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do l' o1) o2) /\ 
                    eq (merge l (do a o') (do b o)) (do (do l' o) o'))
          (ensures eq (merge (do l o') (do (do a o') o1) (do (do (do b o) o') o2)) (do (do (do (do l' o) o') o1) o2)) = ()
          
let comm_intermediate1 (l:concrete_st) (o1 o2 o o' o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\
                    distinct_ops o' o1 /\ distinct_ops o' o2 /\ distinct_ops o3 o1 /\ 
                    eq (do (do l o2) o1) (do (do l o1) o2) /\ 
                    ~ (exists o3 a'. eq (do l o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do l o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))
          (ensures ((eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                     eq (merge (do l o') (do (do l o') o1) (do (do (do l o) o') o2)) (do (do (do (do l o) o') o1) o2)) ==>
      eq (merge (do (do l o3) o') (do (do (do l o3) o') o1) (do (do (do (do l o3) o) o') o2)) (do (do (do (do (do l o3) o) o') o1) o2)) /\
                   ((eq (merge l (do l o1) (do l o2)) (do (do l o2) o1) /\
                     eq (merge (do l o') (do (do l o') o1) (do (do (do l o) o') o2)) (do (do (do (do l o) o') o2) o1)) ==>
      eq (merge (do (do l o3) o') (do (do (do l o3) o') o1) (do (do (do (do l o3) o) o') o2)) (do (do (do (do (do l o3) o) o') o2) o1))) = ()

let comm_intermediate2 (l l' a b:concrete_st) (o1 o2 o o':op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ 
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\
                    distinct_ops o' o2 /\ distinct_ops o' o1 /\
                    eq (do (do l o2) o1) (do (do l o1) o2) /\ 
                    eq (merge l (do a o') (do b o)) (do (do l' o) o') /\
                    eq (merge l (do a o) (do b o')) (do (do l' o) o') /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    eq (merge (do l o') (do (do l o') o1) (do (do l o) o')) (do (do (do l o) o') o1))
          (ensures (eq (merge l (do a o1) (do b o2)) (do (do l' o1) o2) ==>
                    eq (merge (do l o') (do (do a o') o1) (do (do (do b o) o') o2)) (do (do (do (do l' o) o') o1) o2)) /\
                   (eq (merge l (do a o1) (do b o2)) (do (do l' o2) o1) ==>
                    eq (merge (do l o') (do (do a o') o1) (do (do (do b o) o') o2)) (do (do (do (do l' o) o') o2) o1))) = ()

////////////////////////////////////////////////////////////////

let inter_merge1 (l:concrete_st) (o o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o3 /\ Fst_then_snd? (rc o3 o1) /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2))
          (ensures eq (merge (do (do l o) o1) (do (do (do l o) o1) o2) (do (do (do l o) o3) o1)) (do (do (do (do l o) o3) o1) o2)) = ()

let inter_merge2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o3 /\ Fst_then_snd? (rc o3 o1) /\ 
                    //distinct_ops o2 o3 /\ Fst_then_snd? (rc o3 o2) /\
                    eq (merge l s (do l o3)) s' /\
                    eq (merge s (do s o2) s') (do s' o2))
          (ensures eq (merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

let inter_merge3 (l a b c:concrete_st) (op op':op_t) 
  : Lemma (requires eq (merge l a b) c /\
                    (forall (o:op_t). eq (merge l a (do b o)) (do c o)))
          (ensures eq (merge l a (do (do b op) op')) (do (do c op) op')) = ()

let inter_merge4 (l s:concrete_st) (o1 o2 o3 o4:op_t)
  : Lemma (requires distinct_ops o1 o3 /\ Fst_then_snd? (rc o3 o1) /\ 
                    //distinct_ops o2 o3 /\ Fst_then_snd? (rc o3 o2) /\
                    //distinct_ops o1 o4 /\ Fst_then_snd? (rc o4 o1) /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1)) (do (do (do (do s o4) o3) o1) o2)) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = S.t nat

// init state 
let init_st_s = S.empty

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s =
  S.add (snd (snd op)) s

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
