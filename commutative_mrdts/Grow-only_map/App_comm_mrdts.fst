module App_comm_mrdts

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

//pre-condition for do
let do_pre (s:concrete_st) (o:op_t) : prop = true

let do (s:concrete_st) (op:op_t{do_pre s op}) =
  let (ts, (_, (k,v))) = op in
  M.upd s k (S.union (S.singleton v) (sel s k))

#push-options "--ifuel 3"
let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b /\ do_pre a op)
           (ensures do_pre b op /\ eq (do a op) (do b op)) = ()

//pre-condition for merge
let merge_pre (l a b:concrete_st) : prop = true

// concrete merge operation
let merge (l a:concrete_st) (b:concrete_st{merge_pre l a b}) : concrete_st =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u:concrete_st = M.const_on keys S.empty in
  M.iter_upd (fun k v -> S.union (sel l k) (S.union (sel a k) (sel b k))) u

let merge_comm (l a b:st)
  : Lemma (requires cons_reps l a b /\ merge_pre (v_of l) (v_of a) (v_of b))
          (ensures merge_pre (v_of l) (v_of b) (v_of a) /\
                   (eq (merge (v_of l) (v_of a) (v_of b)) 
                       (merge (v_of l) (v_of b) (v_of a)))) = ()
 
let merge_idem (s:st)
  : Lemma (requires merge_pre (v_of s) (v_of s) (v_of s))
          (ensures eq (merge (v_of s) (v_of s) (v_of s)) (v_of s)) = ()

let rec fast_fwd (a b:st)
  : Lemma (requires cons_reps a a b /\ merge_pre (v_of a) (v_of a) (v_of b))
          (ensures eq (merge (v_of a) (v_of a) (v_of b)) (v_of b)) 
          (decreases length (ops_of b)) =
  if ops_of a = ops_of b then ()
  else 
    (let b' = inverse_st b in
     cons_reps_b' a a b;
     fast_fwd a b')

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
                    eq (merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1)) 
                      (do (do (do (do s o4) o3) o1) o2)) = admit()
                      
let inter_merge41 (l s:concrete_st) (o1 o2 o3 o4:op_t)
  : Lemma (requires (exists a b. eq (merge l a b) s) /\ //extra 
                    fst o1 <> fst o3 /\ fst o1 <> fst o4 /\ fst o2 <> fst o3 /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1)) 
                      (do (do (do (do s o4) o3) o1) o2)) = ()
                     
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = concrete_st

// init state 
let init_st_s = init_st

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = 
  do s op

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
