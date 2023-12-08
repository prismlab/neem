module App_user_rc

open FStar.Seq

#set-options "--query_stats"

// the concrete state type
val concrete_st : Type0

// init state
val init_st : concrete_st

// equivalence between 2 concrete states
val eq (a b:concrete_st) : Type0

val symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a)

val transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c)

val eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b)

// operation type
val app_op_t : eqtype

type op_t = pos (*timestamp*) & (nat (*replica ID*) & app_op_t)

let distinct_ops (op1 op2:op_t) = fst op1 =!= fst op2

type log = seq op_t

// apply an operation to a state
val do (s:concrete_st) (o:op_t) : concrete_st

let commutes_with (o1 o2:op_t) =
  forall s. eq (do (do s o1) o2) (do (do s o2) o1)
  
// applying a log of operations to a concrete state
let rec apply_log (x:concrete_st) (l:log) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |_ -> apply_log (do x (head l)) (tail l)  

// property of apply_log
let rec lem_apply_log (x:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (length l > 0 ==> apply_log x l == do (apply_log x (fst (un_snoc l))) (last l)))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_apply_log (do x (head l)) (tail l)
 
type rc_res =
  |Fst_then_snd //o1 -> o2
  |Snd_then_fst //o2 -> o1
  |Either

//conflict resolution
val rc (o1:op_t) (o2:op_t{distinct_ops o1 o2}) : rc_res

// concrete merge operation
val merge (l a b:concrete_st) : concrete_st

/////////////////////////////////////////////////////////////////////////////

val no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3)))

val relaxed_comm (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3))

val non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2)

val cond_comm (o1:op_t) (o2:op_t{distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2))}) (o3:op_t) : bool

val lem_cond_comm (s:concrete_st) (o1 o2 o3:op_t) (l:log)
  : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ cond_comm o1 o2 o3)
          (ensures eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3)) 
          
////////////////////////////////////////////////////////////////////////////

val merge_comm (l a b:concrete_st)
  : Lemma (ensures (eq (merge l a b) (merge l b a)))
                       
val merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s)

val fast_fwd_base (a:concrete_st) (op:op_t)
  : Lemma (ensures eq (do a op) (merge a a (do a op)))

val fast_fwd_ind (a b:concrete_st) (o2 o2':op_t) (l:log)
  : Lemma (requires do b o2 == apply_log a l /\
                    eq (do b o2) (merge a a (do b o2)))
          (ensures eq (do (do b o2') o2) (merge a a (do (do b o2') o2)))

val rc_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) 

val rc_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2))
          
val comm_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o2' o1 /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures ((eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) ==>
                     eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) \/
                    (eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) ==>
                     eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l a (do (do b o2') o2)) o1))))

val comm_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o1' o2 /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures ((eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) ==>
                     eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) \/
                    (eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) ==>
                     eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do a o1') (do b o2)) o1))))

val rc_base (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2))

val comm_base (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2)
          (ensures (eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) ==>
                    eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) /\
                   (eq (merge l (do l o1) (do l o2)) (do (do l o2) o1) ==>
                    eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o2) o1)))

val rc_intermediate (l:concrete_st) (o1 o2 o o':op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\ distinct_ops o' o2)
          (ensures eq (merge (do l o') (do (do l o') o1) (do (do (do l o) o') o2))
                      (do (do (do (do l o) o') o1) o2))
                      
val comm_intermediate (l:concrete_st) (o1 o2 o o':op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\ 
                    distinct_ops o' o1 /\ distinct_ops o' o2)
          (ensures eq (merge (do l o') (do (do l o') o1) (do (do (do l o) o') o2)) (do (do (do (do l o) o') o1) o2) /\
                   eq (merge (do l o') (do (do l o') o2) (do (do (do l o) o') o1)) (do (do (do (do l o) o') o2) o1))
                      
/////////////////////////////////////////////////////////////////////////////

val inter_merge1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o3 /\ Fst_then_snd? (rc o3 o1) /\ 
                    distinct_ops o2 o3 /\ Fst_then_snd? (rc o3 o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2))

val inter_merge2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o3 /\ Fst_then_snd? (rc o3 o1) /\ 
                    distinct_ops o2 o3 /\ Fst_then_snd? (rc o3 o2) /\
                    eq (merge l s (do l o3)) s' /\
                    eq (merge s (do s o2) s') (do s' o2))
          (ensures eq (merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2))

val inter_merge3 (l a b c:concrete_st) (op op':op_t) 
  : Lemma (requires eq (merge l a b) c /\
                    (forall (o:op_t). eq (merge l a (do b o)) (do c o)))
          (ensures eq (merge l a (do (do b op) op')) (do (do c op) op'))

val inter_merge4 (l s:concrete_st) (o1 o2 o3 o4:op_t)
  : Lemma (requires distinct_ops o1 o3 /\ Fst_then_snd? (rc o3 o1) /\ 
                    distinct_ops o2 o3 /\ Fst_then_snd? (rc o3 o2) /\
                    distinct_ops o1 o4 /\ Fst_then_snd? (rc o4 o1) /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1)) (do (do (do (do s o4) o3) o1) o2))

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
val concrete_st_s : Type0

// init state 
val init_st_s : concrete_st_s

// apply an operation to a state 
val do_s (st_s:concrete_st_s) (_:op_t) : concrete_st_s

// equivalence relation between the concrete states of sequential type and MRDT
val eq_sm (st_s:concrete_st_s) (st:concrete_st) : Type0

// initial states are equivalent
val initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st)

// equivalence between states of sequential type and MRDT at every operation
val do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op))

////////////////////////////////////////////////////////////////
