module App_optional_type

module S = Set_extended
module M = Map_extended

open FStar.Seq

//concrete state type of value MRDT
val concrete_st_v : Type0

let cf = (int * bool)

// the concrete state type
type concrete_st_ew = M.t nat cf // (replica_id, ctr, flag) //replica ids are unique

// the concrete state type of map
let concrete_st = concrete_st_ew & concrete_st_v

//concrete state type of value MRDT
val init_st_v : concrete_st_v

let init_st_ew = M.const (0, false)

// init state of map
let init_st = init_st_ew, init_st_v

let sel (s:concrete_st_ew) (k:nat) =
  if M.contains s k then M.sel s k else (0,false)

//equivalence between 2 states of value MRDT
let eq_v (s1 s2:concrete_st_v) : Type0 = s1 == s2

let eq_cf (s1 s2:cf) : Type0 = s1 == s2

let eq_ew (s1 s2:concrete_st_ew) : Type0 = 
  (forall k. (M.contains s1 k = M.contains s2 k) /\ (sel s1 k == sel s2 k)) 

// equivalence between 2 concrete states
let eq (s1 s2:concrete_st) =
 eq_ew (fst s1) (fst s2) /\
 eq_v (snd s1) (snd s2)

let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b) = ()

//operation type of value MRDT
val app_op_v : eqtype 

// operation type of map
type app_op_t =
  |Set : app_op_v -> app_op_t 
  |Unset : app_op_v -> app_op_t

type op_v = pos (*timestamp*) & (nat (*replica ID*) & app_op_v)

type op_t = pos (*timestamp*) & (nat (*replica ID*) & app_op_t)

let get_rid (_,(rid,_)) = rid

let distinct_ops (ts1,_) (ts2,_) = ts1 =!= ts2

type log = seq op_t

//do function of value MRDT
val do_v (s:concrete_st_v) (o:op_v) : concrete_st_v

//convert map operation to value MRDT operation
let get_op_v (o:op_t) : op_v =
  match o with
  |ts, (rid, Set o) -> (ts,(rid,o))
  |ts, (rid, Unset o) -> (ts,(rid,o))

let do_ew (s:concrete_st_ew) (o:op_t) : concrete_st_ew =
  match o with
  |ts, (rid, Set _) -> M.upd s rid (fst (sel s rid) + 1, true)
  |ts, (rid, Unset _) -> M.map_val (fun (c,f) -> (c, false)) s
  
// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |ts, (rid, Set _) -> M.upd (fst s) rid (fst (sel (fst s) rid) + 1, true), do_v (snd s) (get_op_v o)
  |ts, (rid, Unset _) -> M.map_val (fun (c,f) -> (c, false)) (fst s), do_v (snd s) (get_op_v o)

let commutes_with_v (o1 o2:op_v) =
  forall s. eq_v (do_v (do_v s o1) o2) (do_v (do_v s o2) o1)
  
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

//conflict resolution of value MRDT
val rc_v (o1 o2:op_v) : rc_res

//conflict resolution of map
let rc (o1 o2:op_t) : rc_res = 
  match snd (snd o1), snd (snd o2) with
  |Set _, Unset _ -> Snd_then_fst
  |Unset _, Set _ -> Fst_then_snd
  |_ -> rc_v (get_op_v o1) (get_op_v o2)

//three-way merge of simpler MRDT
val merge_v (l a b:concrete_st_v) : concrete_st_v

let merge_flag (l a b:cf) : bool =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac > lc
          else bc > lc

// concrete merge operation
let merge_cf (l a b:cf) : cf =
  (fst a + fst b - fst l, merge_flag l a b)
  
// concrete merge operation
let merge_ew (l a b:concrete_st_ew) : concrete_st_ew =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun k v -> merge_cf (sel l k) (sel a k) (sel b k)) u
  
// concrete merge operation of map
let merge (l a b:concrete_st) : concrete_st =
  merge_ew (fst l) (fst a) (fst b), merge_v (snd l) (snd a) (snd b)
  
/////////////////////////////////////////////////////////////////////////////

val rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) 
          
val no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3)))

val cond_comm_base (s:concrete_st) (o1 o2 o3:op_t) 
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ distinct_ops o1 o3 /\
                    Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3))

val cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:seq op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3 /\ 
                    Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)) /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3))
                  
////////////////////////////////////////////////////////////////////////////

//merge is commutative
val merge_comm_v (l a b: concrete_st_v) 
  : Lemma (ensures eq_v (merge_v l a b) (merge_v l b a))
          [SMTPat (merge_v l a b)]
 
let merge_comm (l a b:concrete_st)
  : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

//merge is idempotent
val merge_idem_v (s: concrete_st_v) 
  : Lemma (ensures eq_v (merge_v s s s) s)
          [SMTPat (merge_v s s s)]
          
let merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s) = ()

//////////////////////////////////////////////////////////////////////////

(*Two OP RC*)
//////////////// 
#set-options "--z3rlimit 100 --ifuel 3"
val rc_ind_right_v (l a b:concrete_st_v) (o1 o2 o2':op_v) 
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (merge_v l (do_v a o1) b) o2))
          (ensures eq_v (merge_v l (do_v a o1) (do_v (do_v b o2') o2)) (do_v (merge_v l (do_v a o1) (do_v b o2')) o2))

val rc_ind_right_ne (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    ~ (Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2))) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2))              

let rc_ind_right (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) =
  if Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) then 
    rc_ind_right_v (snd l) (snd a) (snd b) (get_op_v o1) (get_op_v o2) (get_op_v o2')
  else rc_ind_right_ne l a b o1 o2 o2'

val rc_ind_left_v (l a b:concrete_st_v) (o1 o2 o1':op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\  
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (merge_v l (do_v a o1) b) o2))
          (ensures eq_v (merge_v l (do_v (do_v a o1') o1) (do_v b o2)) (do_v (merge_v l (do_v (do_v a o1') o1) b) o2))

val rc_ind_left_ew (l a b:concrete_st_ew) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\  
                    eq_ew (merge_ew l (do_ew a o1) (do_ew b o2)) (do_ew (merge_ew l (do_ew a o1) b) o2))
          (ensures eq_ew (merge_ew l (do_ew (do_ew a o1') o1) (do_ew b o2)) (do_ew (merge_ew l (do_ew (do_ew a o1') o1) b) o2))
          
val rc_ind_left_ne (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\  
                    ~ (Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2))) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) 

let rc_ind_left (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) =
  if Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) then 
    (rc_ind_left_v (snd l) (snd a) (snd b) (get_op_v o1) (get_op_v o2) (get_op_v o1');
     rc_ind_left_ew (fst l) (fst a) (fst b) o1 o2 o1')
  else rc_ind_left_ne l a b o1 o2 o1'

val rc_ind_lca_v (l:concrete_st_v) (o1 o2 o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq_v (merge_v l (do_v l o1) (do_v l o2)) (do_v (do_v l o1) o2))
          (ensures eq_v (merge_v (do_v l o) (do_v (do_v l o) o1) (do_v (do_v l o) o2)) (do_v (do_v (do_v l o) o1) o2))

val rc_ind_lca_ne (l:concrete_st) (o1 o2 o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o /\ distinct_ops o o2 /\
                    ~ (Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2))) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2))
          
//Special case of rc_intermediate_v1
let rc_ind_lca (l:concrete_st) (o1 o2 o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) =
  if Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) then 
    rc_ind_lca_v (snd l) (get_op_v o1) (get_op_v o2) (get_op_v o)
  else rc_ind_lca_ne l o1 o2 o
          
val rc_base (o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2))

val rc_inter_base_right_v (l a b c:concrete_st_v) (o1 o2 ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2) /\
                    eq_v (merge_v l (do_v a ol) (do_v b ob)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))

val rc_inter_base_right_ew (l a b c:concrete_st_ew) (o1 o2 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew c ol) o1) o2) /\
                    eq_ew (merge_ew l (do_ew a o1) (do_ew b o2)) (do_ew (do_ew c o1) o2) /\
                    eq_ew (merge_ew l (do_ew a ol) (do_ew b ob)) (do_ew (do_ew c ob) ol)) //***EXTRA***
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew (do_ew b ob) ol) o2)) (do_ew (do_ew (do_ew (do_ew c ob) ol) o1) o2))
          
val rc_inter_base_right_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          
let rc_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) =
  if Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) then 
    (rc_inter_base_right_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ob) (get_op_v ol);
     rc_inter_base_right_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ob ol)
  else rc_inter_base_right_ne l a b c o1 o2 ob ol

val rc_inter_base_left_v (l a b c:concrete_st_v) (o1 o2 ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2) /\
                    eq_v (merge_v l (do_v a ob) (do_v b ol)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))

val rc_inter_base_left_ew (l a b c:concrete_st_ew) (o1 o2 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew c ol) o1) o2) /\
                    eq_ew (merge_ew l (do_ew a o1) (do_ew b o2)) (do_ew (do_ew c o1) o2) /\
                    eq_ew (merge_ew l (do_ew a ob) (do_ew b ol)) (do_ew (do_ew c ob) ol)) //***EXTRA***
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew (do_ew a ob) ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew (do_ew c ob) ol) o1) o2))
          
val rc_inter_base_left_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          
let rc_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) =
  if Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) then 
    (rc_inter_base_left_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ob) (get_op_v ol);
     rc_inter_base_left_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ob ol)
  else rc_inter_base_left_ne l a b c o1 o2 ob ol

val rc_inter_right_v (l a b c:concrete_st_v) (o1 o2 ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))
      (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v (do_v b o) ob) ol) o2)) (do_v (do_v (do_v (do_v (do_v c o) ob) ol) o1) o2))

val rc_inter_right_ew (l a b c:concrete_st_ew) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew (do_ew b ob) ol) o2)) (do_ew (do_ew (do_ew (do_ew c ob) ol) o1) o2))
      (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew (do_ew (do_ew b o) ob) ol) o2)) (do_ew (do_ew (do_ew (do_ew (do_ew c o) ob) ol) o1) o2))

val rc_inter_right_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) &&
     (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2))
      
let rc_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) =
  if Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) &&
     (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol))) then 
    (rc_inter_right_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ob) (get_op_v ol) (get_op_v o);
     rc_inter_right_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ob ol o)
  else rc_inter_right_ne l a b c o1 o2 ob ol o

val rc_inter_left_v (l a b c:concrete_st_v) (o1 o2 ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))
      (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v (do_v a o) ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v (do_v c o) ob) ol) o1) o2))

val rc_inter_left_ew (l a b c:concrete_st_ew) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew (do_ew a ob) ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew (do_ew c ob) ol) o1) o2))
      (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew (do_ew (do_ew a o) ob) ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew (do_ew (do_ew c o) ob) ol) o1) o2))

val rc_inter_left_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) /\ (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)))) /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) 
      
let rc_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) =
  if Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) && 
    (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol))) then 
    (rc_inter_left_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ob) (get_op_v ol) (get_op_v o);
     rc_inter_left_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ob ol o)
  else rc_inter_left_ne l a b c o1 o2 ob ol o

//CHECK!!
val rc_inter_lca_v (l a b c:concrete_st_v) (o1 o2 ol oi o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    Fst_then_snd? (rc_v o ol) /\ 
                    Fst_then_snd? (rc_v o oi) /\
                    eq_v (merge_v (do_v l oi) (do_v (do_v a oi) o1) (do_v (do_v b oi) o2)) (do_v (do_v (do_v c oi) o1) o2) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2))
    (ensures eq_v (merge_v (do_v (do_v l oi) ol) (do_v (do_v (do_v a oi) ol) o1) (do_v (do_v (do_v b oi) ol) o2)) (do_v (do_v (do_v (do_v c oi) ol) o1) o2))

val rc_inter_lca_ew (l a b c:concrete_st_ew) (o1 o2 ol oi o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\
                    eq_ew (merge_ew (do_ew l oi) (do_ew (do_ew a oi) o1) (do_ew (do_ew b oi) o2)) (do_ew (do_ew (do_ew c oi) o1) o2) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew c ol) o1) o2))
    (ensures eq_ew (merge_ew (do_ew (do_ew l oi) ol) (do_ew (do_ew (do_ew a oi) ol) o1) (do_ew (do_ew (do_ew b oi) ol) o2)) (do_ew (do_ew (do_ew (do_ew c oi) ol) o1) o2))

val rc_inter_lca_ne (l a b c:concrete_st) (o1 o2 ol oi o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    ~ (Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)) &&
    Fst_then_snd? (rc_v (get_op_v o) (get_op_v oi))) /\
                    Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
           (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2))   
           
// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let rc_inter_lca (l a b c:concrete_st) (o1 o2 ol oi o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\  
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) =
  if Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)) &&
    Fst_then_snd? (rc_v (get_op_v o) (get_op_v oi)) then 
    (rc_inter_lca_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ol) (get_op_v oi) (get_op_v o);
    rc_inter_lca_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ol oi o)
  else rc_inter_lca_ne l a b c o1 o2 ol oi o

(*One op*)
///////////////
val one_op_ind_right_v (l a b:concrete_st_v) (o2 o2':op_v) 
  : Lemma (requires distinct_ops o2 o2' /\ 
                    eq_v (merge_v l a (do_v b o2)) (do_v (merge_v l a b) o2))
           (ensures eq_v (merge_v l a (do_v (do_v b o2') o2)) (do_v (merge_v l a (do_v b o2')) o2))

let one_op_ind_right (l a b:concrete_st) (o2 o2':op_t)
   : Lemma (requires distinct_ops o2 o2' /\ eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2)) =
  one_op_ind_right_v (snd l) (snd a) (snd b) (get_op_v o2) (get_op_v o2')

val one_op_ind_left_v (l a b:concrete_st_v) (o1 o1':op_v) 
  : Lemma (requires distinct_ops o1 o1' /\ 
                    eq_v (merge_v l (do_v a o1) b) (do_v (merge_v l a b) o1))
           (ensures eq_v (merge_v l (do_v (do_v a o1') o1) b) (do_v (merge_v l (do_v a o1') b) o1))

let one_op_ind_left (l a b:concrete_st) (o1 o1':op_t)
   : Lemma (requires distinct_ops o1 o1' /\ eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) =
  one_op_ind_left_v (snd l) (snd a) (snd b) (get_op_v o1) (get_op_v o1')

val one_op_ind_lca_v (l:concrete_st_v) (o2 o:op_v) 
  : Lemma (requires distinct_ops o2 o /\ 
                    eq_v (merge_v l l (do_v l o2)) (do_v l o2))
          (ensures eq_v (merge_v (do_v l o) (do_v l o) (do_v (do_v l o) o2)) (do_v (do_v l o) o2)) 

let one_op_ind_lca (l:concrete_st) (o2 o:op_t)
  : Lemma (requires distinct_ops o2 o /\ eq (merge l l (do l o2)) (do l o2))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o2)) (do (do l o) o2)) =
  one_op_ind_lca_v (snd l) (get_op_v o2) (get_op_v o)

val one_op_base (o2:op_t)
  : Lemma (ensures eq (merge init_st init_st (do init_st o2)) (do init_st o2))

val one_op_inter_base_right_v (l a b c:concrete_st_v) (o2 ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ol) o2)) (do_v (do_v c ol) o2) /\
                    eq_v (merge_v l a (do_v b o2)) (do_v c o2) /\
                    eq_v (merge_v l (do_v a ol) (do_v b ob)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v c ob) ol) o2))

val one_op_inter_base_right_ne (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    ~ (Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          
let one_op_inter_base_right (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) =
  if Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) then 
    one_op_inter_base_right_v (snd l) (snd a) (snd b) (snd c) (get_op_v o2) (get_op_v ob) (get_op_v ol)
  else one_op_inter_base_right_ne l a b c o2 ob ol

val one_op_inter_base_left_v (l a b c:concrete_st_v) (o2 ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ol) o2)) (do_v (do_v c ol) o2) /\
                    //(Fst_then_snd? (rc_v ob o2) ==> eq_v (merge_v l (do_v a o2) (do_v b ob)) (do_v (merge_v l a (do_v b ob)) o2)) /\ //***EXTRA***
                    eq_v (merge_v l a (do_v b o2)) (do_v c o2) /\
                    eq_v (merge_v l (do_v a ob) (do_v b o2)) (do_v (do_v c ob) o2) /\ //EXTRA!! 
                    eq_v (merge_v l (do_v a ob) (do_v b ol)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ob) ol) o2))

val one_op_inter_base_left_ne (l a b c:concrete_st) (ob ol o2:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops ol o2 /\
                    ~ (Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //***EXTRA***
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ //EXTRA!! 
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          
let one_op_inter_base_left (l a b c:concrete_st) (ob ol o2:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops ol o2 /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //***EXTRA***
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ //EXTRA!! 
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) = 
  if Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) then 
    one_op_inter_base_left_v (snd l) (snd a) (snd b) (snd c) (get_op_v o2) (get_op_v ob) (get_op_v ol)
  else one_op_inter_base_left_ne l a b c ob ol o2

val one_op_inter_right_v (l a b c:concrete_st_v) (o2 ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v c ob) ol) o2))
      (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v (do_v (do_v b o) ob) ol) o2)) (do_v (do_v (do_v (do_v c o) ob) ol) o2))

val one_op_inter_right_ew (l a b c:concrete_st_ew) (o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew a ol) (do_ew (do_ew (do_ew b ob) ol) o2)) (do_ew (do_ew (do_ew c ob) ol) o2))
      (ensures eq_ew (merge_ew (do_ew l ol) (do_ew a ol) (do_ew (do_ew (do_ew (do_ew b o) ob) ol) o2)) (do_ew (do_ew (do_ew (do_ew c o) ob) ol) o2))
      
val one_op_inter_right_ne (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    ~ (Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) /\ (~ (Either? (rc_v (get_op_v o) (get_op_v ob))) \/ Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2))
          
let one_op_inter_right (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) =
  if Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) && (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol))) then 
     (one_op_inter_right_v (snd l) (snd a) (snd b) (snd c) (get_op_v o2) (get_op_v ob) (get_op_v ol) (get_op_v o);
      one_op_inter_right_ew (fst l) (fst a) (fst b) (fst c) o2 ob ol o)
  else one_op_inter_right_ne l a b c o2 ob ol o
          
val one_op_inter_left_v (l a b c:concrete_st_v) (o2 ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ob) ol) o2))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a o) ob) ol) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c o) ob) ol) o2))

val one_op_inter_left_ew (l a b c:concrete_st_ew) (o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ob) ol) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew c ob) ol) o2))
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew (do_ew a o) ob) ol) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew (do_ew c o) ob) ol) o2))

val one_op_inter_left_ne (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    ~ (Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) /\ (~ (Either? (rc_v (get_op_v o) (get_op_v ob))) \/ Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2))
          
let one_op_inter_left (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) =
  if Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) && (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol))) then 
     (one_op_inter_left_v (snd l) (snd a) (snd b) (snd c) (get_op_v o2) (get_op_v ob) (get_op_v ol) (get_op_v o);
      one_op_inter_left_ew (fst l) (fst a) (fst b) (fst c) o2 ob ol o)
  else one_op_inter_left_ne l a b c o2 ob ol o

val one_op_inter_lca_v (l a b c:concrete_st_v) (o2 ol oi o:op_v)
  : Lemma (requires distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\ 
                    Fst_then_snd? (rc_v o ol) /\ 
                    Fst_then_snd? (rc_v o oi) /\
                    eq_v (merge_v (do_v l oi) (do_v a oi) (do_v (do_v b oi) o2)) (do_v (do_v c oi) o2) /\
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ol) o2)) (do_v (do_v c ol) o2))
    (ensures eq_v (merge_v (do_v (do_v l oi) ol) (do_v (do_v a oi) ol) (do_v (do_v (do_v b oi) ol) o2)) (do_v (do_v (do_v c oi) ol) o2))

val one_op_inter_lca_ew (l a b c:concrete_st_ew) (o2 ol oi o:op_t)
  : Lemma (requires distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\ 
                    Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\
                    eq_ew (merge_ew (do_ew l oi) (do_ew a oi) (do_ew (do_ew b oi) o2)) (do_ew (do_ew c oi) o2) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew a ol) (do_ew (do_ew b ol) o2)) (do_ew (do_ew c ol) o2))
    (ensures eq_ew (merge_ew (do_ew (do_ew l oi) ol) (do_ew (do_ew a oi) ol) (do_ew (do_ew (do_ew b oi) ol) o2)) (do_ew (do_ew (do_ew c oi) ol) o2))

val one_op_inter_lca_ne (l a b c:concrete_st) (o2 ol oi o:op_t)
  : Lemma (requires distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\ 
                    ~ (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)) /\ Fst_then_snd? (rc_v (get_op_v o) (get_op_v oi))) /\
                    Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\ 
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) 
          
// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let one_op_inter_lca (l a b c:concrete_st) (o2 ol oi o:op_t)
  : Lemma (requires distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\ 
                    Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\ 
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) =
  if Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)) && Fst_then_snd? (rc_v (get_op_v o) (get_op_v oi)) then 
    (one_op_inter_lca_v (snd l) (snd a) (snd b) (snd c) (get_op_v o2) (get_op_v ol) (get_op_v oi) (get_op_v o);
     one_op_inter_lca_ew (fst l) (fst a) (fst b) (fst c) o2 ol oi o)
  else one_op_inter_lca_ne l a b c o2 ol oi o

(*Zero op *)
///////////////
val zero_op_inter_base_right_v (l a b c:concrete_st_v) (ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v b ol)) (do_v c ol) /\
                    eq_v (merge_v l a b) c /\
                    eq_v (merge_v l (do_v a ol) (do_v b ob)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ob) ol)) (do_v (do_v c ob) ol))

val zero_op_inter_base_right_ne (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    ~ (Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) 
          
// because we proved that e_i^l rcp eb is not possible.
//e_i^l vis eb is not possible
// so either eb rcp e_i^l or eb rct e_i^l is possible
let zero_op_inter_base_right (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) =
  if Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) then 
    zero_op_inter_base_right_v (snd l) (snd a) (snd b) (snd c) (get_op_v ob) (get_op_v ol)
  else zero_op_inter_base_right_ne l a b c ob ol

val zero_op_inter_base_left_v (l a b c:concrete_st_v) (ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v b ol)) (do_v c ol) /\
                    eq_v (merge_v l a b) c /\
                    eq_v (merge_v l (do_v a ob) (do_v b ol)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v b ol)) (do_v (do_v c ob) ol))

val zero_op_inter_base_left_ne (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    ~ (Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do b ol) ) (do (do c ob) ol))
                    
let zero_op_inter_base_left (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do b ol) ) (do (do c ob) ol)) =
  if Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) then 
    zero_op_inter_base_left_v (snd l) (snd a) (snd b) (snd c) (get_op_v ob) (get_op_v ol)
  else zero_op_inter_base_left_ne l a b c ob ol

val zero_op_inter_right_v (l a b c:concrete_st_v) (ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ob) ol)) (do_v (do_v c ob) ol))
          (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v (do_v b o) ob) ol)) (do_v (do_v (do_v c o) ob) ol)) 

val zero_op_inter_right_ew (l a b c:concrete_st_ew) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew a ol) (do_ew (do_ew b ob) ol)) (do_ew (do_ew c ob) ol))
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew a ol) (do_ew (do_ew (do_ew b o) ob) ol)) (do_ew (do_ew (do_ew c o) ob) ol)) 
          
val zero_op_inter_right_ne (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) /\ (~ (Either? (rc_v (get_op_v o) (get_op_v ob))) \/ Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol))  
          
let zero_op_inter_right (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol)) =
  if Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) && (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol))) then 
    (zero_op_inter_right_v (snd l) (snd a) (snd b) (snd c) (get_op_v ob) (get_op_v ol) (get_op_v o);
     zero_op_inter_right_ew (fst l) (fst a) (fst b) (fst c) ob ol o)
  else zero_op_inter_right_ne l a b c ob ol o

val zero_op_inter_left_v (l a b c:concrete_st_v) (ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v b ol)) (do_v (do_v c ob) ol))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a o) ob) ol) (do_v b ol)) (do_v (do_v (do_v c o) ob) ol)) 

val zero_op_inter_left_ew (l a b c:concrete_st_ew) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ob) ol) (do_ew b ol)) (do_ew (do_ew c ob) ol))
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew (do_ew a o) ob) ol) (do_ew b ol)) (do_ew (do_ew (do_ew c o) ob) ol)) 

val zero_op_inter_left_ne (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) /\ (~ (Either? (rc_v (get_op_v o) (get_op_v ob))) \/ Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol))
          
let zero_op_inter_left (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol)) =
  if Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) && (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol))) then 
    (zero_op_inter_left_v (snd l) (snd a) (snd b) (snd c) (get_op_v ob) (get_op_v ol) (get_op_v o);
     zero_op_inter_left_ew (fst l) (fst a) (fst b) (fst c) ob ol o)
  else zero_op_inter_left_ne l a b c ob ol o

val zero_op_inter_lca_v1_v (l a b c:concrete_st_v) (ol o':op_v)
  : Lemma (requires Fst_then_snd? (rc_v o' ol) /\ eq_v (merge_v l a b) c)
          (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v b ol)) (do_v c ol))

val zero_op_inter_lca_v1_ne (l a b c:concrete_st) (ol o':op_t)
  : Lemma (requires Fst_then_snd? (rc o' ol) /\ eq (merge l a b) c /\
                    ~ (Fst_then_snd? (rc_v (get_op_v o') (get_op_v ol))))
          (ensures eq (merge (do l ol) (do a ol) (do b ol)) (do c ol))
          
// In general, the event "o" below should be such that these exists o', (rc o' o)
let zero_op_inter_lca_v1 (l a b c:concrete_st) (ol o':op_t)
  : Lemma (requires Fst_then_snd? (rc o' ol) /\ eq (merge l a b) c)
          (ensures eq (merge (do l ol) (do a ol) (do b ol)) (do c ol)) =
  if Fst_then_snd? (rc_v (get_op_v o') (get_op_v ol)) then 
    zero_op_inter_lca_v1_v (snd l) (snd a) (snd b) (snd c) (get_op_v ol) (get_op_v o')
  else zero_op_inter_lca_v1_ne l a b c ol o'

val zero_op_inter_lca_v2_v (l a b c:concrete_st_v) (ol oi o:op_v)
  : Lemma (requires distinct_ops ol oi /\
                    Fst_then_snd? (rc_v o ol) /\ 
                    Fst_then_snd? (rc_v o oi) /\ 
                    eq_v (merge_v (do_v l oi) (do_v a oi) (do_v b oi)) (do_v c oi)  /\
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v b ol)) (do_v c ol))
          (ensures eq_v (merge_v (do_v (do_v l oi) ol) (do_v (do_v a oi) ol) (do_v (do_v b oi) ol)) (do_v (do_v c oi) ol))

val zero_op_inter_lca_v2_ne (l a b c:concrete_st) (ol oi o:op_t)
  : Lemma (requires distinct_ops ol oi /\
                    ~ (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)) /\ Fst_then_snd? (rc_v (get_op_v o) (get_op_v oi))) /\
                    Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\
                    eq (merge (do l oi) (do a oi) (do b oi)) (do c oi)  /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol))
          
// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let zero_op_inter_lca_v2 (l a b c:concrete_st) (ol oi o:op_t)
  : Lemma (requires distinct_ops ol oi /\
                    Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\
                    eq (merge (do l oi) (do a oi) (do b oi)) (do c oi)  /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol)) =
  if Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)) && Fst_then_snd? (rc_v (get_op_v o) (get_op_v oi)) then 
    zero_op_inter_lca_v2_v (snd l) (snd a) (snd b) (snd c) (get_op_v ol) (get_op_v oi) (get_op_v o)
  else zero_op_inter_lca_v2_ne l a b c ol oi o
          
(*Two OP COMM*)
//////////////// 

val comm_ind_right_v (l a b:concrete_st_v) (o1 o2' o2:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\
                    //(Fst_then_snd? (rc_v o2' o1) ==> (eq_v (merge_v l (do_v a o1) (do_v b o2')) (do_v (merge_v l a (do_v b o2')) o1))) /\
                    ~ (Fst_then_snd? (rc_v o1 o2')) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v (merge_v l a b) o2) o1))
          (ensures eq_v (merge_v l (do_v a o1) (do_v (do_v b o2') o2)) (do_v (do_v (merge_v l a (do_v b o2')) o2) o1))

val comm_ind_right_ew (l a b:concrete_st_ew) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                    //(Fst_then_snd? (rc_ew o2' o1) ==> (eq_ew (merge_ew l (do_ew a o1) (do_ew b o2')) (do_ew (merge_ew l a (do_ew b o2')) o1))) /\
                    ~ (Fst_then_snd? (rc o1 o2')) /\
                    eq_ew (merge_ew l (do_ew a o1) (do_ew b o2)) (do_ew (do_ew (merge_ew l a b) o2) o1))
          (ensures eq_ew (merge_ew l (do_ew a o1) (do_ew (do_ew b o2') o2)) (do_ew (do_ew (merge_ew l a (do_ew b o2')) o2) o1))
          
val comm_ind_right_ne (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    ~ (Either? (rc_v (get_op_v o1) (get_op_v o2)) /\ 
                       (Snd_then_fst? (rc_v (get_op_v o1) (get_op_v o2')) \/ Either? (rc_v (get_op_v o1) (get_op_v o2')))) /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) /\
                    ~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) 
          
let comm_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) /\
                    ~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) =
  if Either? (rc_v (get_op_v o1) (get_op_v o2)) && (Snd_then_fst? (rc_v (get_op_v o1) (get_op_v o2')) || Either? (rc_v (get_op_v o1) (get_op_v o2'))) then
    (comm_ind_right_v (snd l) (snd a) (snd b) (get_op_v o1) (get_op_v o2') (get_op_v o2);
     comm_ind_right_ew (fst l) (fst a) (fst b) o1 o2' o2) 
  else comm_ind_right_ne l a b o1 o2' o2

val comm_ind_left_v (l a b:concrete_st_v) (o1 o2 o1':op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\
                    //(Fst_then_snd? (rc_v o1' o2) ==> (eq_v (merge_v l (do_v a o1') (do_v b o2)) (do_v (merge_v l (do_v a o1') b) o2))) /\
                    ~ (Fst_then_snd? (rc_v o2 o1')) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v (merge_v l a b) o2) o1))
          (ensures eq_v (merge_v l (do_v (do_v a o1') o1) (do_v b o2)) (do_v (do_v (merge_v l (do_v a o1') b) o2) o1))

val comm_ind_left_ew (l a b:concrete_st_ew) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                    //(Fst_then_snd? (rc_ew o1' o2) ==> (eq_ew (merge_ew l (do_ew a o1') (do_ew b o2)) (do_ew (merge_ew l (do_ew a o1') b) o2))) /\
                    ~ (Fst_then_snd? (rc o2 o1')) /\
                    eq_ew (merge_ew l (do_ew a o1) (do_ew b o2)) (do_ew (do_ew (merge_ew l a b) o2) o1))
          (ensures eq_ew (merge_ew l (do_ew (do_ew a o1') o1) (do_ew b o2)) (do_ew (do_ew (merge_ew l (do_ew a o1') b) o2) o1))
          
val comm_ind_left_ne (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    ~ (Either? (rc_v (get_op_v o1) (get_op_v o2)) /\ 
                       (Snd_then_fst? (rc_v (get_op_v o2) (get_op_v o1')) \/ Either? (rc_v (get_op_v o2) (get_op_v o1')))) /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o1' o2) ==> (eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o1')) /\
                    ~ (exists o3 b'. eq (do (do b o1') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (do (merge l (do a o1') b) o2) o1))
          
let comm_ind_left (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o1' o2) ==> (eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o1')) /\
                    ~ (exists o3 b'. eq (do (do b o1') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (do (merge l (do a o1') b) o2) o1)) =
  if Either? (rc_v (get_op_v o1) (get_op_v o2)) && (Snd_then_fst? (rc_v (get_op_v o2) (get_op_v o1')) || Either? (rc_v (get_op_v o2) (get_op_v o1'))) then
    (comm_ind_left_v (snd l) (snd a) (snd b) (get_op_v o1) (get_op_v o2) (get_op_v o1');
     comm_ind_left_ew (fst l) (fst a) (fst b) o1 o2 o1') 
  else comm_ind_left_ne l a b o1 o2 o1'

val comm_ind_lca_v (l:concrete_st_v) (ol o1 o2:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\
                    eq_v (merge_v l (do_v l o1) (do_v l o2)) (do_v (do_v l o2) o1))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v l ol) o1) (do_v (do_v l ol) o2)) (do_v (do_v (do_v l ol) o2) o1))

val comm_ind_lca_ne (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    ~ (Either? (rc_v (get_op_v o1) (get_op_v o2))) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) 
          
let comm_ind_lca (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) =
  if Either? (rc_v (get_op_v o1) (get_op_v o2)) then 
    comm_ind_lca_v (snd l) (get_op_v ol) (get_op_v o1) (get_op_v o2)
  else comm_ind_lca_ne l ol o1 o2

val comm_base_v (o1 o2:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\ distinct_ops o1 o2)
          (ensures eq_v (merge_v init_st_v (do_v init_st_v o1) (do_v init_st_v o2)) (do_v (do_v init_st_v o1) o2))

val comm_base_ew (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq_ew (merge_ew init_st_ew (do_ew init_st_ew o1) (do_ew init_st_ew o2)) (do_ew (do_ew init_st_ew o1) o2))

val comm_base_ne (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ distinct_ops o1 o2 /\
                    ~ (Either? (rc_v (get_op_v o1) (get_op_v o2))))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2))
          
let comm_base (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) =
  if Either? (rc_v (get_op_v o1) (get_op_v o2)) then 
    (comm_base_v (get_op_v o1) (get_op_v o2);
     comm_base_ew o1 o2)
  else comm_base_ne o1 o2

val comm_inter_base_right_v (l a b c:concrete_st_v) (o1 o2 ob ol:op_v) 
  : Lemma (requires Either? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2) /\ 
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2) /\
                    eq_v (merge_v l (do_v a o1) (do_v (do_v b ob) o2)) (do_v (do_v (merge_v l a (do_v b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ob) ol)) (do_v (do_v c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))

val comm_inter_base_right_ew (l a b c:concrete_st_ew) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew c ol) o1) o2) /\ 
                    eq_ew (merge_ew l (do_ew a o1) (do_ew b o2)) (do_ew (do_ew c o1) o2) /\
                    eq_ew (merge_ew l (do_ew a o1) (do_ew (do_ew b ob) o2)) (do_ew (do_ew (merge_ew l a (do_ew b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq_ew (merge_ew (do_ew l ol) (do_ew a ol) (do_ew (do_ew b ob) ol)) (do_ew (do_ew c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew (do_ew b ob) ol) o2)) (do_ew (do_ew (do_ew (do_ew c ob) ol) o1) o2))
          
val comm_inter_base_right_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (Either? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (do (merge l a (do b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) 
          
let comm_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (do (merge l a (do b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) =
  if Either? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) then 
    (comm_inter_base_right_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ob) (get_op_v ol);
     comm_inter_base_right_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ob ol)
  else comm_inter_base_right_ne l a b c o1 o2 ob ol
          
val comm_inter_base_left_v (l a b c:concrete_st_v) (o1 o2 ob ol:op_v) 
  : Lemma (requires Either? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2) /\ 
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2) /\
                    eq_v (merge_v l (do_v (do_v a ob) o1) (do_v b o2)) (do_v (do_v (merge_v l (do_v a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v b ol)) (do_v (do_v c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))

val comm_inter_base_left_ew (l a b c:concrete_st_ew) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew c ol) o1) o2) /\ 
                    eq_ew (merge_ew l (do_ew a o1) (do_ew b o2)) (do_ew (do_ew c o1) o2) /\
                    eq_ew (merge_ew l (do_ew (do_ew a ob) o1) (do_ew b o2)) (do_ew (do_ew (merge_ew l (do_ew a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ob) ol) (do_ew b ol)) (do_ew (do_ew c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew (do_ew a ob) ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew (do_ew c ob) ol) o1) o2))
          
val comm_inter_base_left_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (Either? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do (do a ob) o1) (do b o2)) (do (do (merge l (do a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))

let comm_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do (do a ob) o1) (do b o2)) (do (do (merge l (do a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) =
 if Either? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) then 
    (comm_inter_base_left_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ob) (get_op_v ol);
     comm_inter_base_left_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ob ol)
  else comm_inter_base_left_ne l a b c o1 o2 ob ol

val comm_inter_right_v (l a b c:concrete_st_v) (o1 o2 ob ol o:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v (do_v b o) ob) ol) o2)) (do_v (do_v (do_v (do_v (do_v c o) ob) ol) o1) o2))

val comm_inter_right_ew (l a b c:concrete_st_ew) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew (do_ew b ob) ol) o2)) (do_ew (do_ew (do_ew (do_ew c ob) ol) o1) o2))
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew (do_ew (do_ew b o) ob) ol) o2)) (do_ew (do_ew (do_ew (do_ew (do_ew c o) ob) ol) o1) o2))
          
val comm_inter_right_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (Either? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) /\ 
     (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) \/ Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) \/ Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2))
  
let comm_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) =
  if Either? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) && 
     (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol))) then 
    (comm_inter_right_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ob) (get_op_v ol) (get_op_v o);
     comm_inter_right_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ob ol o)
  else comm_inter_right_ne l a b c o1 o2 ob ol o

val comm_inter_left_v (l a b c:concrete_st_v) (o1 o2 ob ol o:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v (do_v a o) ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v (do_v c o) ob) ol) o1) o2))

val comm_inter_left_ew (l a b c:concrete_st_ew) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew (do_ew a ob) ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew (do_ew c ob) ol) o1) o2))
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew (do_ew (do_ew a o) ob) ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew (do_ew (do_ew c o) ob) ol) o1) o2))
          
val comm_inter_left_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (Either? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) /\ 
     (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) \/ Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) \/ Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2))
  
let comm_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) =
  if Either? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol)) && 
     (Fst_then_snd? (rc_v (get_op_v o) (get_op_v ob)) || Snd_then_fst? (rc_v (get_op_v o) (get_op_v ob)) || Fst_then_snd? (rc_v (get_op_v o) (get_op_v ol))) then 
    (comm_inter_left_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ob) (get_op_v ol) (get_op_v o);
     comm_inter_left_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ob ol o)
  else comm_inter_left_ne l a b c o1 o2 ob ol o

val comm_inter_lca_v (l a b c:concrete_st_v) (o1 o2 ol o':op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\ distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    Fst_then_snd? (rc_v o' ol) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2))

val comm_inter_lca_ew (l a b c:concrete_st_ew) (o1 o2 ol o':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    Fst_then_snd? (rc o' ol) /\
                    eq_ew (merge_ew l (do_ew a o1) (do_ew b o2)) (do_ew (do_ew c o1) o2))
          (ensures eq_ew (merge_ew (do_ew l ol) (do_ew (do_ew a ol) o1) (do_ew (do_ew b ol) o2)) (do_ew (do_ew (do_ew c ol) o1) o2))
          
val comm_inter_lca_ne (l a b c:concrete_st) (o1 o2 ol o':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    Fst_then_snd? (rc o' ol) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) 
          
let comm_inter_lca (l a b c:concrete_st) (o1 o2 ol o':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    ~ (Either? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v o') (get_op_v ol))) /\
                    Fst_then_snd? (rc o' ol) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) =
  if Either? (rc_v (get_op_v o1) (get_op_v o2)) && Fst_then_snd? (rc_v (get_op_v o') (get_op_v ol)) then 
    (comm_inter_lca_v (snd l) (snd a) (snd b) (snd c) (get_op_v o1) (get_op_v o2) (get_op_v ol) (get_op_v o');
     comm_inter_lca_ew (fst l) (fst a) (fst b) (fst c) o1 o2 ol o')
  else comm_inter_lca_ne l a b c o1 o2 ol o'
