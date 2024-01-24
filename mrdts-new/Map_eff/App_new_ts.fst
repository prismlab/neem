module App_new_ts

module S = Set_extended
module M = Map_extended

#set-options "--query_stats"

let cf = (int * bool)

// concrete state of ew flag
type concrete_st_e = M.t nat cf // (replica_id, ctr, flag) //replica ids are unique

// concrete state of lww reg
type concrete_st_l = (nat & nat) // timestamp, value

// the concrete state type
type concrete_st = M.t nat (concrete_st_l & concrete_st_e) //value is a pair of lww reg and ew flag

// init state of ew flag
let init_st_e : concrete_st_e = M.const (0, false)

// init state of lww regs
let init_st_l : concrete_st_l = (0,0)

// init state
let init_st : concrete_st = M.const (init_st_l, init_st_e)

let sel_k (s:concrete_st) k = if M.contains s k then M.sel s k else (init_st_l, init_st_e)

let sel_id (s:M.t nat cf) id = if M.contains s id then M.sel s id else (0, false)

let key_id (s:concrete_st) (k id:nat) =
  M.contains s k /\ M.contains (snd (sel_k s k)) id

// equivalence relation of ew flag
let eq_e (a b:concrete_st_e) =
  (forall id. (M.contains a id = M.contains b id) /\ (sel_id a id == sel_id b id))

// equivalence relation of lww reg
let eq_l (a b:concrete_st_l) = a = b
  
// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  (forall k. M.contains a k = M.contains b k) /\
  (forall k. M.contains a k ==> eq_l (fst (sel_k a k)) (fst (sel_k b k))) /\
  (forall k. M.contains a k ==> eq_e (snd (sel_k a k)) (snd (sel_k b k)))

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
  |Set : nat -> nat -> app_op_t //key-value pair
  |Del : nat -> app_op_t //key

let get_key o =
  match o with
  |(_,(_,Set k _)) -> k
  |(_,(_,Del k)) -> k

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
 match o with
  |(ts, (rid, Set k v)) -> M.upd s k ((ts,v), (M.upd (snd (sel_k s k)) rid (fst (sel_id (snd (sel_k s k)) rid) + 1, true)))
  |(_, (rid, Del k)) -> M.upd s k (fst (sel_k s k), (M.map_val (fun (c,f) -> (c, false)) (snd (sel_k s k))))

//conflict resolution
let rc (o1:op_t) (o2:op_t(*{distinct_ops o1 o2}*)) =
  match o1, o2 with
  |(ts1,(rid1,Set k1 v1)),(ts2,(rid2,Set k2 v2)) -> if k1 = k2 then Ts_order else Either
  |(_,(_,Set k1 _)),(_,(_,Del k2)) -> if k1 = k2 then Snd_then_fst else Either
  |(_,(_,Del k1)),(_,(_,Set k2 _)) -> if k1 = k2 then Fst_then_snd else Either
  |_ -> Either

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
  
// concrete merge operation of ew flag
let merge_ew (l a b:concrete_st_e) : concrete_st_e =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun k v -> merge_cf (sel_id l k) (sel_id a k) (sel_id b k)) u

// concrete merge operation of lww reg
let merge_l (l a b:concrete_st_l) : concrete_st_l =
  if fst a < fst b then b else a

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let eles = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on eles init_st in
  M.iter_upd (fun k v -> (merge_l (fst (sel_k l k)) (fst (sel_k a k)) (fst (sel_k b k)),
                       merge_ew (snd (sel_k l k)) (snd (sel_k a k)) (snd (sel_k b k)))) u

/////////////////////////////////////////////////////////////////////////////

let no_rc_chain (o1 o2 o3:op_t)
  : Lemma (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3))) = ()

#push-options "--z3rlimit 100 --max_ifuel 3 --split_queries on_failure"
let relaxed_comm (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)) /\ ~ (Ts_order? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

let non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = 
  assert (((Set? (snd (snd o1)) /\ Del? (snd (snd o2)) /\ get_key o1 = get_key o2) \/ 
           (Del? (snd (snd o1)) /\ Set? (snd (snd o2)) /\ get_key o1 = get_key o2)) ==>
           ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))); ()

let cond_comm (o1:op_t) (o2:op_t{distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ ~ (Ts_order? (rc o1 o2))}) (o3:op_t) = 
  assert (get_key o1 = get_key o2); 
  if Del? (snd (snd o3)) && get_key o1 = get_key o3 then true else false

let cond_comm_base (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ ~ (Ts_order? (rc o1 o2)) /\ cond_comm o1 o2 o3)
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

let cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:log)
  : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ ~ (Ts_order? (rc o1 o2)) /\ cond_comm o1 o2 o3 /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3)) = ()
          
/////////////////////////////////////////////////////////////////////////////

// Merge commutativity
let merge_comm (l a b:concrete_st)
   : Lemma (ensures (eq (merge l a b) (merge l b a))) = admit()

// Merge idempotence
let merge_idem (s:concrete_st)
   : Lemma (ensures eq (merge s s s) s) = ()

(*Two OP RC*)
//////////////// 
let rc_ind_right' (l a b:concrete_st) (o1 o2' o2:op_t)
   : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                     eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) /\
                     (forall k. eq_l (fst (sel_k (merge l (do a o1) (do (do b o2') o2)) k)) 
                                (fst (sel_k (do (merge l (do a o1) (do b o2')) o2) k)) /\
                           eq_e (snd (sel_k (merge l (do a o1) (do (do b o2') o2)) k)) 
                                (snd (sel_k (do (merge l (do a o1) (do b o2')) o2) k))))
           (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let rc_ind_left' (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) /\
                    (forall k. eq_l (fst (sel_k (merge l (do (do a o1') o1) (do b o2)) k)) 
                               (fst (sel_k (do (merge l (do (do a o1') o1) b) o2) k)) /\
                          eq_e (snd (sel_k (merge l (do (do a o1') o1) (do b o2)) k)) 
                               (snd (sel_k (do (merge l (do (do a o1') o1) b) o2) k))))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()
          
//Special case of rc_intermediate_v1
let rc_ind_lca' (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o) (do (do l o) o1) (do (do l o) o2)) k))
                               (fst (sel_k (do (do (do l o) o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o) (do (do l o) o1) (do (do l o) o2)) k))
                               (snd (sel_k (do (do (do l o) o1) o2) k))))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()

let rc_base' (o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let rc_inter_base_right' (l s1 s2 s3:concrete_st) (o o' o1 o2:op_t) 
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\
                    distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge l (do s1 o') (do s2 o)) (do (do s3 o) o') /\ //***EXTRA***
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) k))
                               (fst (sel_k (do (do (do (do s3 o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) k))
                               (snd (sel_k (do (do (do (do s3 o) o') o1) o2) k))))                              
          (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2)) = ()
          
let rc_inter_base_left' (l s1 s2 s3:concrete_st) (o o' o1 o2:op_t) 
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\
                    distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge l (do s1 o) (do s2 o')) (do (do s3 o) o') /\ //***EXTRA***
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) k))
                               (fst (sel_k (do (do (do (do s3 o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) k))
                               (snd (sel_k (do (do (do (do s3 o) o') o1) o2) k))))
          (ensures eq (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) (do (do (do (do s3 o) o') o1) o2)) = ()
          
let rc_inter_right' (l s1 s2 s3:concrete_st) (o1 o2 o o' o_n:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\  
                    distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\
                    get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                    ((~ (commutes_with o_n o)) \/ Fst_then_snd? (rc o_n o') \/ (Ts_order? (rc o_n o') (*/\ fst o_n < fst o'*))) /\
                    eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) k))
                               (fst (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) k))
                               (snd (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k))))
      (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) (do (do (do (do (do s3 o_n) o) o') o1) o2)) = ()

let rc_inter_left' (l s1 s2 s3:concrete_st) (o1 o2 o o' o_n:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\  
                    distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                    ((~ (commutes_with o_n o)) \/ Fst_then_snd? (rc o_n o') \/ (Ts_order? (rc o_n o') (*/\ fst o_n < fst o'*))) /\
                    eq (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) (do (do (do (do s3 o) o') o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) k))
                               (fst (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) k))
                               (snd (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k))))
      (ensures eq (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) (do (do (do (do (do s3 o_n) o) o') o1) o2)) = ()

let rc_inter_lca' (l s1 s2 s3:concrete_st) (o1 o2 o' o_n:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    (exists o. Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    (exists o. Fst_then_snd? (rc o o_n) \/ (Ts_order? (rc o o_n) (*/\ fst o < fst o_n*))) /\ 
                    eq (merge (do l o_n) (do (do s1 o_n) o1) (do (do s2 o_n) o2)) (do (do (do s3 o_n) o1) o2) /\
                    eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do (do l o_n) o') (do (do (do s1 o_n) o') o1) (do (do (do s2 o_n) o') o2)) k))
                               (fst (sel_k (do (do (do (do s3 o_n) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do (do l o_n) o') (do (do (do s1 o_n) o') o1) (do (do (do s2 o_n) o') o2)) k))
                               (snd (sel_k (do (do (do (do s3 o_n) o') o1) o2) k))))
    (ensures eq (merge (do (do l o_n) o') (do (do (do s1 o_n) o') o1) (do (do (do s2 o_n) o') o2)) (do (do (do (do s3 o_n) o') o1) o2)) = ()

(*Two OP TS_order*)
//////////////// 
let ts_ind_right' (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) /\
                    (forall k. eq_l (fst (sel_k (merge l (do a o1) (do (do b o2') o2)) k))
                               (fst (sel_k (do (merge l (do a o1) (do b o2')) o2) k)) /\
                          eq_e (snd (sel_k (merge l (do a o1) (do (do b o2') o2)) k))
                               (snd (sel_k (do (merge l (do a o1) (do b o2')) o2) k))))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let ts_ind_left' (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) /\
                    (forall k. eq_l (fst (sel_k (merge l (do (do a o1') o1) (do b o2)) k))
                               (fst (sel_k (do (merge l (do (do a o1') o1) b) o2) k)) /\
                          eq_e (snd (sel_k (merge l (do (do a o1') o1) (do b o2)) k))
                               (snd (sel_k (do (merge l (do (do a o1') o1) b) o2) k))))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

//Special case of rc_intermediate_v1
let ts_ind_lca' (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2 /\ fst o1 < fst o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o) (do (do l o) o1) (do (do l o) o2)) k))
                               (fst (sel_k (do (do (do l o) o1) o2)k)) /\
                          eq_e (snd (sel_k (merge (do l o) (do (do l o) o1) (do (do l o) o2)) k))
                               (snd (sel_k (do (do (do l o) o1) o2) k))))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()

let ts_base' (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let ts_inter_base_right' (l s1 s2 s3:concrete_st) (o o' o1 o2:op_t) 
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge l (do s1 o') (do s2 o)) (do (do s3 o) o') /\ //***EXTRA***
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) k))
                               (fst (sel_k (do (do (do (do s3 o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) k))
                               (snd (sel_k (do (do (do (do s3 o) o') o1) o2) k))))
          (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2)) = ()

let ts_inter_base_left' (l s1 s2 s3:concrete_st) (o o' o1 o2:op_t) 
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge l (do s1 o) (do s2 o')) (do (do s3 o) o') /\ //***EXTRA***
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) k))
                               (fst (sel_k (do (do (do (do s3 o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) k))
                               (snd (sel_k (do (do (do (do s3 o) o') o1) o2) k))))
          (ensures eq (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) (do (do (do (do s3 o) o') o1) o2)) = ()

let ts_inter_right' (l s1 s2 s3:concrete_st) (o1 o2 o o' o_n:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                    ((~ (commutes_with o_n o)) \/ Fst_then_snd? (rc o_n o') \/ (Ts_order? (rc o_n o') /\ fst o_n < fst o')) /\
                    eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) k))
                               (fst (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) k))
                               (snd (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k))))
      (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) (do (do (do (do (do s3 o_n) o) o') o1) o2)) = ()

let ts_inter_left' (l s1 s2 s3:concrete_st) (o1 o2 o o' o_n:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\ 
                    distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                    ((~ (commutes_with o_n o)) \/ Fst_then_snd? (rc o_n o') \/ (Ts_order? (rc o_n o') (*/\ fst o_n < fst o'*))) /\
                    eq (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) (do (do (do (do s3 o) o') o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) k))
                               (fst (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) k))
                               (snd (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k))))
      (ensures eq (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) (do (do (do (do (do s3 o_n) o) o') o1) o2)) = ()

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let ts_inter_lca' (l s1 s2 s3:concrete_st) (o1 o2 o' o_n:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    (exists o. Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    (exists o. Fst_then_snd? (rc o o_n) \/ (Ts_order? (rc o o_n) (*/\ fst o < fst o_n*))) /\ 
                    eq (merge (do l o_n) (do (do s1 o_n) o1) (do (do s2 o_n) o2)) (do (do (do s3 o_n) o1) o2) /\
                    eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do (do l o_n) o') (do (do (do s1 o_n) o') o1) (do (do (do s2 o_n) o') o2))  k))
                               (fst (sel_k (do (do (do (do s3 o_n) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do (do l o_n) o') (do (do (do s1 o_n) o') o1) (do (do (do s2 o_n) o') o2))  k))
                               (snd (sel_k (do (do (do (do s3 o_n) o') o1) o2) k))))
    (ensures eq (merge (do (do l o_n) o') (do (do (do s1 o_n) o') o1) (do (do (do s2 o_n) o') o2)) (do (do (do (do s3 o_n) o') o1) o2)) = ()

(*One op*)
///////////////
let one_op_ind_right' (l a b c:concrete_st) (o1 o1':op_t)
   : Lemma (requires eq (merge l a (do b o1)) (do (merge l a b) o1) /\
                     (forall k. eq_l (fst (sel_k (merge l a (do (do b o1') o1)) k))
                               (fst (sel_k (do (merge l a (do b o1')) o1) k)) /\
                          eq_e (snd (sel_k (merge l a (do (do b o1') o1)) k))
                               (snd (sel_k (do (merge l a (do b o1')) o1) k))))
           (ensures eq (merge l a (do (do b o1') o1)) (do (merge l a (do b o1')) o1)) = ()

let one_op_ind_lca' (l:concrete_st) (o o1:op_t)
  : Lemma (requires eq (merge l l (do l o1)) (do l o1) /\ fst o < fst o1 /\
                    (forall k. eq_l (fst (sel_k (merge (do l o) (do l o) (do (do l o) o1)) k))
                               (fst (sel_k (do (do l o) o1) k)) /\
                          eq_e (snd (sel_k (merge (do l o) (do l o) (do (do l o) o1)) k))
                               (snd (sel_k (do (do l o) o1) k))))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o1)) (do (do l o) o1)) = ()

let one_op_base' (o1:op_t)
  : Lemma (ensures eq (merge init_st init_st (do init_st o1)) (do init_st o1)) = ()

let one_op_inter_base_right' (l s1 s2 s3:concrete_st) (o o' o1:op_t) 
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    eq (merge (do l o') (do s1 o') (do (do s2 o') o1)) (do (do s3 o') o1) /\
                    eq (merge l s1 (do s2 o1)) (do s3 o1) /\
                    eq (merge l (do s1 o') (do s2 o)) (do (do s3 o) o') /\ //***EXTRA***
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do s1 o') (do (do (do s2 o) o') o1)) k))
                               (fst (sel_k (do (do (do s3 o) o') o1) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do s1 o') (do (do (do s2 o) o') o1)) k))
                               (snd (sel_k (do (do (do s3 o) o') o1) k))))
          (ensures eq (merge (do l o') (do s1 o') (do (do (do s2 o) o') o1)) (do (do (do s3 o) o') o1)) = ()

let one_op_inter_left' (l s1 s2 s3:concrete_st) (o1 o o':op_t) (o_n:op_t(*{~ (commutes_with o_n o)}*))
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                    ((~ (commutes_with o_n o)) \/ Fst_then_snd? (rc o_n o') \/ (Ts_order? (rc o_n o') (*/\ fst o_n < fst o'*))) /\
                    eq (merge (do l o') (do (do s1 o) o') (do (do s2 o') o1)) (do (do (do s3 o) o') o1) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do (do s1 o_n) o) o') (do (do s2 o') o1)) k))
                               (fst (sel_k (do (do (do (do s3 o_n) o) o') o1) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do (do s1 o_n) o) o') (do (do s2 o') o1)) k))
                               (snd (sel_k (do (do (do (do s3 o_n) o) o') o1) k)))) 
          (ensures eq (merge (do l o') (do (do (do s1 o_n) o) o') (do (do s2 o') o1)) (do (do (do (do s3 o_n) o) o') o1)) = ()

let one_op_inter_lca' (l s1 s2 s3:concrete_st) (o1 o' o_n:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    (exists o. Fst_then_snd? (rc o o_n) \/ (Ts_order? (rc o o_n) (*/\ fst o < fst o_n*))) /\ 
                    eq (merge (do l o_n) (do s1 o_n) (do (do s2 o_n) o1)) (do (do s3 o_n) o1) /\
                    eq (merge (do l o') (do s1 o') (do (do s2 o') o1)) (do (do s3 o') o1) /\
                    (forall k. eq_l (fst (sel_k (merge (do (do l o_n) o') (do (do s1 o_n) o') (do (do (do s2 o_n) o') o1)) k))
                               (fst (sel_k (do (do (do s3 o_n) o') o1) k)) /\
                          eq_e (snd (sel_k (merge (do (do l o_n) o') (do (do s1 o_n) o') (do (do (do s2 o_n) o') o1)) k))
                               (snd (sel_k (do (do (do s3 o_n) o') o1) k)))) 
          (ensures eq (merge (do (do l o_n) o') (do (do s1 o_n) o') (do (do (do s2 o_n) o') o1)) (do (do (do s3 o_n) o') o1)) = ()

(*Zero op *)
///////////////
let zero_op_inter_base_right' (l s1 s2 s3:concrete_st) (o o':op_t) 
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    eq (merge (do l o') (do s1 o') (do s2 o')) (do s3 o') /\
                    eq (merge l s1 s2) s3 /\
                    eq (merge l (do s1 o') (do s2 o)) (do (do s3 o) o') /\ //***EXTRA***
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do s1 o') (do (do s2 o) o')) k))
                               (fst (sel_k (do (do s3 o) o') k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do s1 o') (do (do s2 o) o')) k))
                               (snd (sel_k (do (do s3 o) o') k)))) 
          (ensures eq (merge (do l o') (do s1 o') (do (do s2 o) o')) (do (do s3 o) o')) = ()

let zero_op_inter_base_left' (l s1 s2 s3:concrete_st) (o o' o1':op_t) 
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    distinct_ops o1' o' /\ (Fst_then_snd? (rc o1' o') \/ (Ts_order? (rc o1' o') (*/\ fst o1' < fst o'*))) /\ 
                    eq (merge (do l o') (do s1 o') (do s2 o')) (do s3 o') /\
                    eq (merge l s1 s2) s3 /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do s1 o1') o') (do (do s2 o) o')) k))
                               (fst (sel_k (do (do (do s3 o1') o) o') k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do s1 o1') o') (do (do s2 o) o')) k))
                               (snd (sel_k (do (do (do s3 o1') o) o') k)))) 
          (ensures eq (merge (do l o') (do (do s1 o1') o') (do (do s2 o) o')) (do (do (do s3 o1') o) o')) = ()

let zero_op_inter_right' (l s1 s2 s3:concrete_st) (o o':op_t) (o_n:op_t(*{~ (commutes_with o_n o)}*))
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                    ((~ (commutes_with o_n o)) \/ Fst_then_snd? (rc o_n o') \/ (Ts_order? (rc o_n o') (*/\ fst o_n < fst o'*))) /\
                    eq (merge (do l o') (do s1 o') (do (do s2 o) o')) (do (do s3 o) o') /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do s1 o') (do (do (do s2 o_n) o) o'))k))
                               (fst (sel_k (do (do (do s3 o_n) o) o') k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do s1 o') (do (do (do s2 o_n) o) o')) k))
                               (snd (sel_k (do (do (do s3 o_n) o) o') k)))) 
          (ensures eq (merge (do l o') (do s1 o') (do (do (do s2 o_n) o) o')) (do (do (do s3 o_n) o) o')) = ()

let zero_op_inter_left' (l s1 s2 s3:concrete_st) (o o':op_t) (o_n:op_t(*{~ (commutes_with o_n o)}*))
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                    ((~ (commutes_with o_n o)) \/ Fst_then_snd? (rc o_n o') \/ (Ts_order? (rc o_n o') (*/\ fst o_n < fst o'*))) /\
                    eq (merge (do l o') (do (do s1 o) o') (do s2 o')) (do (do s3 o) o') /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do (do s1 o_n) o) o') (do s2 o')) k))
                               (fst (sel_k (do (do (do s3 o_n) o) o') k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do (do s1 o_n) o) o') (do s2 o')) k))
                               (snd (sel_k (do (do (do s3 o_n) o) o') k))))
          (ensures eq (merge (do l o') (do (do (do s1 o_n) o) o') (do s2 o')) (do (do (do s3 o_n) o) o')) = ()

// In general, the event "o" below should be such that these exists o', (rc o' o)
let zero_op_inter_lca_v1' (l s1 s2 s3:concrete_st) (o:op_t)
  : Lemma (requires (exists o'. Fst_then_snd? (rc o' o) \/ (Ts_order? (rc o' o) (*/\ fst o' < fst o*))) /\ eq (merge l s1 s2) s3 /\
                    (forall k. eq_l (fst (sel_k (merge (do l o) (do s1 o) (do s2 o)) k))
                               (fst (sel_k (do s3 o) k)) /\
                          eq_e (snd (sel_k (merge (do l o) (do s1 o) (do s2 o)) k))
                               (snd (sel_k (do s3 o) k))))
          (ensures eq (merge (do l o) (do s1 o) (do s2 o)) (do s3 o)) = ()

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let zero_op_inter_lca_v2' (l s1 s2 s3:concrete_st) (o' o_n:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    (exists o. Fst_then_snd? (rc o o_n) \/ (Ts_order? (rc o o_n) (*/\ fst o < fst o_n*))) /\
                    eq (merge (do l o_n) (do s1 o_n) (do s2 o_n)) (do s3 o_n)  /\
                    eq (merge (do l o') (do s1 o') (do s2 o')) (do s3 o') /\
                    (forall k. eq_l (fst (sel_k (merge (do (do l o_n) o') (do (do s1 o_n) o') (do (do s2 o_n) o')) k))
                               (fst (sel_k (do (do s3 o_n) o') k)) /\
                          eq_e (snd (sel_k (merge (do (do l o_n) o') (do (do s1 o_n) o') (do (do s2 o_n) o')) k))
                               (snd (sel_k (do (do s3 o_n) o') k))))
          (ensures eq (merge (do (do l o_n) o') (do (do s1 o_n) o') (do (do s2 o_n) o')) (do (do s3 o_n) o')) = ()

(* 2 op Comm  *)
///////////////////

let comm_ind_right' (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o2' o1 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) /\
                    ~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    (forall k. eq_l (fst (sel_k (merge l (do a o1) (do (do b o2') o2)) k))
                               (fst (sel_k (do (do (merge l a (do b o2')) o2) o1) k)) /\
                          eq_e (snd (sel_k (merge l (do a o1) (do (do b o2') o2)) k))
                               (snd (sel_k (do (do (merge l a (do b o2')) o2) o1) k))))                
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()

let comm_ind_left' (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o2' o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o2) ==> (eq (merge l (do a o2') (do b o2)) (do (merge l (do a o2') b) o2))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o2')) /\
                    ~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    (forall k. eq_l (fst (sel_k (merge l (do (do a o2') o1) (do b o2)) k))
                               (fst (sel_k (do (do (merge l (do a o2') b) o2) o1) k)) /\
                          eq_e (snd (sel_k (merge l (do (do a o2') o1) (do b o2)) k))
                               (snd (sel_k (do (do (merge l (do a o2') b) o2) o1) k))))                    
          (ensures eq (merge l (do (do a o2') o1) (do b o2)) (do (do (merge l (do a o2') b) o2) o1)) = ()

let comm_ind_lca' (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o) (do (do l o) o1) (do (do l o) o2)) k))
                               (fst (sel_k (do (do (do l o) o2) o1) k)) /\
                          eq_e (snd (sel_k (merge (do l o) (do (do l o) o1) (do (do l o) o2)) k))
                               (snd (sel_k (do (do (do l o) o2) o1) k)))) 
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o2) o1)) = ()

let comm_base' (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_inter_base_right' (l s1 s2 s3:concrete_st) (o o' o1 o2:op_t) 
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    distinct_ops o1 o2 /\ Either? (rc o1 o2) /\
                    distinct_ops o' o1 /\ distinct_ops o' o2 /\
                    eq (merge l (do s1 o1) (do (do s2 o) o2)) (do (do (merge l s1 (do s2 o)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2) /\ 
                    eq (merge (do l o') (do s1 o') (do (do s2 o) o')) (do (do s3 o) o') /\ //comes from intermediate_base_zero_op
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) k))
                               (fst (sel_k (do (do (do (do s3 o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) k))
                               (snd (sel_k (do (do (do (do s3 o) o') o1) o2) k)))) 
          (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2)) = ()

let comm_inter_base_left' (l s1 s2 s3:concrete_st) (o o' o1 o2:op_t) 
  : Lemma (requires distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') (*/\ fst o < fst o'*))) /\ 
                    distinct_ops o1 o2 /\ Either? (rc o1 o2) /\
                    distinct_ops o' o1 /\ distinct_ops o' o2 /\
                    eq (merge l (do (do s1 o) o1) (do s2 o2)) (do (do (merge l (do s1 o) s2) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2) /\ 
                    eq (merge (do l o') (do (do s1 o) o') (do s2 o')) (do (do s3 o) o') /\ //comes from intermediate_base_zero_op
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) k))
                               (fst (sel_k (do (do (do (do s3 o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) k))
                               (snd (sel_k (do (do (do (do s3 o) o') o1) o2) k))))
          (ensures eq (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) (do (do (do (do s3 o) o') o1) o2)) = ()

let comm_inter_right' (l s1 s2 s3:concrete_st) (o1 o2 o o':op_t) (o_n:op_t{~ (commutes_with o_n o)})
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\  
                    distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') /\ fst o < fst o')) /\ 
                    get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                    distinct_ops o_n o' /\ Either? (rc o_n o') /\ 
                    eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) k))
                               (fst (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) k))
                               (snd (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k))))
          (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) (do (do (do (do (do s3 o_n) o) o') o1) o2)) = ()

let comm_inter_left' (l s1 s2 s3:concrete_st) (o1 o2 o o':op_t) (o_n:op_t{~ (commutes_with o_n o)})
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\  
                    distinct_ops o o' /\ (Fst_then_snd? (rc o o') \/ (Ts_order? (rc o o') /\ fst o < fst o')) /\ 
                    get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                    distinct_ops o_n o' /\ Either? (rc o_n o') /\ 
                    //eq (merge (do l o') (do (do (do s1 o_n) o') o1) (do (do s2 o') o2)) (do (do (do (do s3 o_n) o') o1) o2) /\ //***EXTRA***
                    eq (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) (do (do (do (do s3 o) o') o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) k))
                               (fst (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) k))
                               (snd (sel_k (do (do (do (do (do s3 o_n) o) o') o1) o2) k))))
          (ensures eq (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) (do (do (do (do (do s3 o_n) o) o') o1) o2)) = ()

let comm_inter_lca' (l s1 s2 s3:concrete_st) (o1 o2 o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o1 o /\ distinct_ops o o2 /\
                    (exists o'. Fst_then_snd? (rc o' o) \/ (Ts_order? (rc o' o) (*/\ fst o' < fst o*))) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    (forall k. eq_l (fst (sel_k (merge (do l o) (do (do s1 o) o1) (do (do s2 o) o2)) k))
                               (fst (sel_k (do (do (do s3 o) o1) o2) k)) /\
                          eq_e (snd (sel_k (merge (do l o) (do (do s1 o) o1) (do (do s2 o) o2)) k))
                               (snd (sel_k (do (do (do s3 o) o1) o2) k))))
          (ensures eq (merge (do l o) (do (do s1 o) o1) (do (do s2 o) o2)) (do (do (do s3 o) o1) o2)) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
let concrete_st_s' = M.t nat nat

// init state 
let init_st_s' : concrete_st_s' = M.const_on (S.empty) 0

// apply an operation to a state 
let do_s' (st_s:concrete_st_s') (o:op_t) : concrete_st_s' =
  match o with
  |(ts, (rid, Set k v)) -> M.upd st_s k v
  |(_, (rid, Del k)) -> M.del st_s k 

// equivalence relation between the concrete states of sequential type and MRDT
let eq_sm' (st_s:concrete_st_s') (st:concrete_st) =
  (forall k. (M.contains st k /\ (exists rid. snd (sel_id (snd (sel_k st k)) rid) = true)) <==> M.contains st_s k) /\
  (forall k. M.contains st_s k ==> M.sel st_s k = snd (fst (sel_k st k)))

// initial states are equivalent
let initial_eq' (_:unit)
  : Lemma (ensures eq_sm' init_st_s' init_st) = ()

// equivalence between states of sequential type and MRDT at every operation
let do_eq' (st_s:concrete_st_s') (st:concrete_st) (op:op_t)   
  : Lemma (requires eq_sm' st_s st)
          (ensures eq_sm' (do_s' st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////
