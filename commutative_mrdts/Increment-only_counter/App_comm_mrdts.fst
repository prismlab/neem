module App_comm_mrdts

#set-options "--query_stats"
// the concrete state type
type concrete_st = int

// init state
let init_st = 0

// equivalence between 2 concrete states
let eq (a b:concrete_st) = a = b

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
type app_op_t = unit (*since there is only inc op, we use unit*)

//pre-condition for do
let do_pre (s:concrete_st) (o:op_t) : prop = true

// apply an operation to a state
let do (s:concrete_st) (op:op_t{do_pre s op}) : concrete_st = s + 1

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b /\ do_pre a op)
           (ensures eq (do a op) (do b op)) = ()

//pre-condition for merge
let merge_pre (l a b:concrete_st) : prop = true

// concrete merge operation
let merge (l a:concrete_st) (b:concrete_st{merge_pre l a b}) : concrete_st =
  a + b - l

let merge_comm (l a b:st)
  : Lemma (requires cons_reps l a b /\ merge_pre (v_of l) (v_of a) (v_of b))
          (ensures merge_pre (v_of l) (v_of b) (v_of a) /\
                   (eq (merge (v_of l) (v_of a) (v_of b)) 
                       (merge (v_of l) (v_of b) (v_of a)))) = ()

let merge_idem (s:st)
  : Lemma (requires merge_pre (v_of s) (v_of s) (v_of s))
          (ensures eq (merge (v_of s) (v_of s) (v_of s)) (v_of s)) = ()

let fast_fwd (a b:st)
  : Lemma (requires cons_reps a a b /\ merge_pre (v_of a) (v_of a) (v_of b))
          (ensures eq (merge (v_of a) (v_of a) (v_of b)) (v_of b)) = ()
          
let lin_prop1 (s:concrete_st) (op1 op2:op_t)
  : Lemma (requires do_pre s op1 /\ do_pre s op2 /\ do_pre (do s op1) op2 /\ do_pre (do s op2) op1)
          (ensures eq (do (do s op1) op2) (do (do s op2) op1)) = ()

let lin_prop3 (l a b:concrete_st) (last2:op_t) 
  :  Lemma (requires do_pre b last2 /\ merge_pre l a b /\ merge_pre l a (do b last2) /\
                     do_pre (merge l a b) last2)
           (ensures eq (do (merge l a b) last2) (merge l a (do b last2))) = ()

let inter_merge1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    do_pre l o1 /\ do_pre l o3 /\ do_pre (do l o1) o2 /\ do_pre (do l o3) o1 /\ do_pre (do (do l o3) o1) o2 /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do l o3) o1))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

let inter_merge2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o2 <> fst o3 /\ fst o1 <> fst o3 /\
                    do_pre l o3 /\ do_pre l o2 /\ do_pre s' o2 /\ do_pre s o2 /\
                    merge_pre l s (do l o3) /\ merge_pre s (do s o2) s' /\
                    eq (merge l s (do l o3)) s' /\
                    eq (merge s (do s o2) s') (do s' o2) /\
                    do_pre s o1 /\ do_pre s' o1 /\ do_pre (do s o1) o2 /\ do_pre (do s' o1) o2 /\
                    merge_pre (do s o1) (do (do s o1) o2) (do s' o1))
          (ensures eq (merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

let inter_merge3 (l a b c:concrete_st) (op op':op_t) 
  : Lemma (requires merge_pre l a b /\ eq (merge l a b) c /\
                    (forall (o:op_t). do_pre b o /\ do_pre c o /\ merge_pre l a (do b o) ==> eq (merge l a (do b o)) (do c o)) /\
                    do_pre b op /\ do_pre c op /\ do_pre (do b op) op' /\ do_pre (do c op) op' /\
                    merge_pre l a (do (do b op) op'))
          (ensures eq (merge l a (do (do b op) op')) (do (do c op) op')) = ()

let inter_merge4 (l s:concrete_st) (o1 o2 o3 o4:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o4 /\ fst o2 <> fst o3 /\
                    do_pre l o1 /\ do_pre s o3 /\ do_pre (do l o1) o2 /\ do_pre (do s o3) o1 /\ do_pre (do (do s o3) o1) o2 /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do s o3) o1) /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2) /\
                    do_pre s o4 /\ do_pre (do s o4) o3 /\ do_pre (do (do s o4) o3) o1 /\ do_pre (do (do (do s o4) o3) o1) o2 /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1)) 
                      (do (do (do (do s o4) o3) o1) o2)) = ()
                      
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = nat

// init state 
let init_st_s = 0

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = s + 1

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st /\ do_pre st op)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////
