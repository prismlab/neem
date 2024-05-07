module App_alpha_map

module S = Set_extended
module M = Map_extended

open FStar.Seq

//concrete state type of simpler MRDT
val concrete_st_s : Type0
  
// the concrete state type of map
let concrete_st = M.t string concrete_st_s

//concrete state type of simpler MRDT
val init_st_s : concrete_st_s

// init state of map
let init_st = M.const init_st_s

let sel (s:concrete_st) (k:string) =
  if M.contains s k then M.sel s k else init_st_s

//equivalence between 2 states of simpler MRDT
let eq_s (s1 s2:concrete_st_s) : Type0 = s1 == s2

// equivalence between 2 concrete states
let eq (s1 s2:concrete_st) =
  (forall k. (M.contains s1 k = M.contains s2 k) /\ eq_s (sel s1 k) (sel s2 k))

let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b) = ()

//operation type of simpler MRDT
val op_s : eqtype 

// operation type
type app_op_t =
  |Set : string (*key*) -> op_s -> app_op_t 

type op_t = pos (*timestamp*) & (nat (*replica ID*) & app_op_t)

let get_rid (_,(rid,_)) = rid

let distinct_ops (op1 op2:op_t) = fst op1 =!= fst op2

type log = seq op_t

//do function of simpler MRDT
val do_s (s:concrete_st_s) (o:(nat & (nat & op_s))) : concrete_st_s

//convert map operation to simpler MRDT operation
let get_op_s (o:op_t) : (nat & (nat & op_s)) =
  match o with
  |ts, (rid, Set _ o) -> (ts,(rid,o))

let get_key (_,(_,Set k _)) = k

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  let k = get_key o in
  M.upd s k (do_s (sel s k) (get_op_s o))

let commutes_with (o1 o2:op_t) =
  forall s. eq (do (do s o1) o2) (do (do s o2) o1)

// applying a log of operations to a concrete state
let rec apply_log (x:concrete_st) (l:log) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |_ -> apply_log (do x (head l)) (tail l)  
  
//conflict resolution type
type rc_res =
  |Fst_then_snd //o1 -> o2
  |Snd_then_fst //o2 -> o1
  |Either

//conflict resolution of simpler MRDT
val rc_s (o1 o2:(nat & (nat & op_s))) : rc_res

//conflict resolution of map
let rc (o1 o2:op_t) : rc_res = Either

//three-way merge of simpler MRDT
val merge_s (l a b:concrete_st_s) : concrete_st_s

// concrete merge operation of map
let merge (l a b:concrete_st) : concrete_st =
  let eles = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on eles init_st_s in
  M.iter_upd (fun k v -> merge_s (sel l k) (sel a k) (sel b k)) u

/////////////////////////////////////////////////////////////////////////////

val rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2)

val no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3)))

val cond_comm_base (s:concrete_st) (o1 o2:op_t) (o3:op_t{distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3})
    : (b:bool{(Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3))) ==> eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)})

val cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:seq op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3 /\ cond_comm_base s o1 o2 o3 /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3))
                  
////////////////////////////////////////////////////////////////////////////

//merge is commutative
val merge_comm (l a b:concrete_st)
  : Lemma (ensures (eq (merge l a b) (merge l b a)))

//merge is idempotent
val merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s)

////////////////////////////////////////////////////////////////////////////

//helper lemmas
val lemma_do (s:concrete_st) (o:op_t)
  : Lemma (ensures (forall k. k = get_key o ==> eq_s (sel (do s o) k) (do_s (sel s k) (get_op_s o))))

val lemma_merge (l a b:concrete_st)
  : Lemma (ensures (forall k. eq_s (sel (merge l a b) k) (merge_s (sel l k) (sel a k) (sel b k))) )

(*Two OP COMM*)
//////////////// 

//simpler MRDT lemma (Already proved for Grows-only set)
val comm_ind_right_s (l a b:concrete_st_s) (o1 o2' o2:(nat & (nat & op_s)))
  : Lemma (requires Either? (rc_s o1 o2) /\
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s (merge_s l a b) o2) o1))
          (ensures eq_s (merge_s l (do_s a o1) (do_s (do_s b o2') o2)) (do_s (do_s (merge_s l a (do_s b o2')) o2) o1))

val comm_ind_right_ne (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Either? (rc_s (get_op_s o1) (get_op_s o2)) /\
                     ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o2') /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) 
          
let comm_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Either? (rc_s (get_op_s o1) (get_op_s o2)) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) =
  let k = get_key o2' in
  let l' = sel l k in let a' = sel a k in let b' = sel b k in 
  lemma_merge l a b;
  if get_key o2 = get_key o1 && get_key o1 = k then 
    comm_ind_right_s l' a' b' (get_op_s o1) (get_op_s o2') (get_op_s o2)
  else comm_ind_right_ne l a b o1 o2' o2

//simpler MRDT lemma (Already proved for Grows-only set)
val comm_ind_left_s (l a b:concrete_st_s) (o1 o2' o2:(nat & (nat & op_s)))
  : Lemma (requires Either? (rc_s o1 o2) /\
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s (merge_s l a b) o2) o1))
          (ensures eq_s (merge_s l (do_s (do_s a o2') o1) (do_s b o2)) (do_s (do_s (merge_s l (do_s a o2') b) o2) o1))

val comm_ind_left_ne (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Either? (rc_s (get_op_s o1) (get_op_s o2)) /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o2') /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1))                    
          (ensures eq (merge l (do (do a o2') o1) (do b o2)) (do (do (merge l (do a o2') b) o2) o1)) 
          
let comm_ind_left (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Either? (rc_s (get_op_s o1) (get_op_s o2)) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1))                    
          (ensures eq (merge l (do (do a o2') o1) (do b o2)) (do (do (merge l (do a o2') b) o2) o1)) =
  let k = get_key o2' in
  let l' = sel l k in let a' = sel a k in let b' = sel b k in 
  lemma_merge l a b;
  if get_key o2 = get_key o1 && get_key o1 = k then 
    comm_ind_left_s l' a' b' (get_op_s o1) (get_op_s o2') (get_op_s o2)
  else comm_ind_left_ne l a b o1 o2' o2

//simpler MRDT lemma (Already proved for Grows-only set)
val comm_ind_lca_s (l:concrete_st_s) (ol o1 o2:(nat & (nat & op_s)))
  : Lemma (requires Either? (rc_s o1 o2) /\
                    eq_s (merge_s l (do_s l o1) (do_s l o2)) (do_s (do_s l o2) o1))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s l ol) o1) (do_s (do_s l ol) o2)) (do_s (do_s (do_s l ol) o2) o1))

val comm_ind_lca_ne (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Either? (rc_s (get_op_s o1) (get_op_s o2)) /\
                    ~ (get_key ol = get_key o1 /\ get_key ol = get_key o2) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) 
          
let comm_ind_lca (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Either? (rc_s (get_op_s o1) (get_op_s o2)) /\ 
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) =
  let k = get_key ol in
  let l' = sel l k in
  if get_key ol = get_key o1 && get_key ol = get_key o2 then
    comm_ind_lca_s l' (get_op_s ol) (get_op_s o1) (get_op_s o2)
  else comm_ind_lca_ne l ol o1 o2

val comm_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2))

