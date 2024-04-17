module App_new_ts

module S = Set_extended
module M = Map_extended

#set-options "--query_stats"

// concrete state of lww reg
type concrete_st_l = (nat & nat) // timestamp, value

// concrete state of ew flag
type concrete_st_e = M.t nat (int * bool) //map of rid, (counter, flag)

let concrete_st = concrete_st_l & concrete_st_e

// init state of lww regs
let init_st_l : concrete_st_l = (0,0)

// init state of ew flag
let init_st_e = M.const (0, false)

let init_st = (init_st_l, init_st_e)

let sel_id (s:concrete_st_e) k = if M.contains s k then M.sel s k else (0, false)

// equivalence relation of lww reg
let eq_l (a b:concrete_st_l) = a = b

// equivalence relation of ew flag
let eq_e (a b:concrete_st_e) =
  (forall id. (M.contains a id = M.contains b id) /\ (sel_id a id == sel_id b id))

let eq (a b:concrete_st) =
  eq_e (snd a) (snd b) /\
  ((exists id. M.contains (snd a) id /\ snd (sel_id (snd a) id) = true) ==> fst a = fst b)
  
let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b) = ()

type op_l : eqtype =
  |Write : nat (*value*) -> op_l

type op_e:eqtype = 
  |Enable 
  |Disable

type op_s : eqtype =
   op_l & op_e

// operation type
type app_op_t:eqtype =
  |Set : nat (* register value *) -> app_op_t 
  |Unset
  
(*let do_l (s:concrete_st_l) (o:(nat & (nat & op_s))) : concrete_st_l =
  match o with
  |(ts,(_,(Some(Write v),_))) -> (ts,v)
  |(_,((_,(None,_)))) -> s*)

let do_l (s:concrete_st_l) (o:(nat & (nat & op_l))) : concrete_st_l =
  let (ts,(_,(Write v))) = o in (ts, v)
  
  (*match o with
  |(ts,(_,(Some(Write v),_))) -> (ts,v)
  |(_,((_,(None,_)))) -> s*)
  
let do_e (s:concrete_st_e) (o:(nat & (nat & op_e))) : concrete_st_e =
  match o with
  |(_,(rid,Enable)) -> M.upd s rid (fst (sel_id s rid) + 1, true)
  |(_,(_,Disable)) ->  M.map_val (fun (c,f) -> (c, false)) s

//let do_s (s:concrete_st_s) (o:(nat & (nat & op_s))) : concrete_st_s =
  //(do_l (fst s) o, do_e (snd s) o)

let get_op_l (o:op_t) : (nat & (nat & op_l)) =
  match o with
  |(ts,(rid,(Set v))) -> (ts,(rid,Write v))
  |(ts,(rid,Unset)) -> (0,(rid,Write 0))
  
let get_op_e (o:op_t) : (nat & (nat & op_e)) =
  match o with
  |(ts,(rid,(Set v))) -> (ts,(rid,Enable))
  |(ts,(rid,Unset)) -> (ts,(rid,Disable))
  
let do (s:concrete_st) (o:op_t) : concrete_st =
  (do_l (fst s) (get_op_l o), do_e (snd s) (get_op_e o))

let rc_l (o1 o2:(nat & (nat & op_l))) = Ts_order

let rc_e (o1 o2:(nat & (nat & op_e))) =
  if Enable? (snd (snd o1)) && Disable? (snd (snd o2)) then Snd_then_fst 
  else if Disable? (snd (snd o1)) && Enable? (snd (snd o2)) then Fst_then_snd
  else Either


//conflict resolution
let rc (o1:op_t) (o2:op_t(*{distinct_ops o1 o2}*)) =
  match o1, o2 with
  |(ts1,(_,Set _)),(ts2,(_,Set _)) -> Ts_order
  |(_,(_,Set _)),(_,(_,Unset)) -> Snd_then_fst
  |(_,(_,Unset)),(_,(_,Set _)) -> Fst_then_snd
  |_ -> Either

let commutes_with_s (o1 o2:(nat & (nat & op_e))) =
  forall s. eq_e (do_e (do_e s o1) o2) (do_e (do_e s o2) o1)
  
// concrete merge operation of lww reg
let merge_l (l a b:concrete_st_l) : concrete_st_l =
  if fst a < fst b then b else a
  
let merge_flag (l a b:(int & bool)) : bool =
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
let merge_cf (l a b:(int * bool)) : (int * bool) =
  (fst a + fst b - fst l, merge_flag l a b)
  
// concrete merge operation
let merge_e (l a b:concrete_st_e) : concrete_st_e =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun k v -> merge_cf (sel_id l k) (sel_id a k) (sel_id b k)) u

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  (merge_l (fst l) (fst a) (fst b), merge_e (snd l) (snd a) (snd b))

/////////////////////////////////////////////////////////////////////////////

let no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3))) = ()

let relaxed_comm (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o1 o2) /\ 
                    ~ (Either? (rc o2 o3)) /\ ~ (Ts_order? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

#push-options "--z3rlimit 100 --max_ifuel 3 --split_queries on_failure"
let non_comm_help (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures (Set? (snd (snd o1)) \/ Set? (snd (snd o2)) ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1)))) = ()

let non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = 
  non_comm_help o1 o2

let cond_comm (o1:op_t) (o2:op_t{distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) (*/\ ~ (Ts_order? (rc o1 o2)*)}) (o3:op_t) = 
  if Unset? (snd (snd o3)) then true else false

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
  : Lemma (ensures (eq (merge l a b) (merge l b a))) = admit() //can be done with pre-cond for lww reg

let merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s) = ()

(*Two OP RCp*)
//////////////// 
let rc_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let rc_ind_right_base (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2))
          (ensures eq (merge l (do l o1) (do l o2)) (do (merge l (do l o1) l) o2)) = ()
          
(*let ts_ind_right' (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()*)

let rc_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = 
  assert (eq_e (snd (merge l (do a o1') (do b o2))) (snd (do (merge l (do a o1') b) o2))); //test - can be removed
  assert (eq_e (snd (merge l (do (do a o1) o1') (do b o2))) (snd (do (merge l (do (do a o1) o1') b) o2))); //test - can be removed 
  ()

(*let ts_ind_left' (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ 
                    (Fst_then_snd? (rc o1' o2) ==> eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2)) /\ //EXTRA!!
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()*)
          
//Special case of rc_intermediate_v1
let rc_ind_lca (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2)) = ()
          
let rc_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

#push-options "--z3rlimit 300 --max_ifuel 3"
let rc_inter_base_right'1 (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\                 
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let lo (o1 o2:op_t) =
  (get_rid o1 = get_rid o2 /\ ~ (Either? (rc o1 o2)) /\ fst o1 < fst o2) \/
  (get_rid o1 <> get_rid o2 /\ //~ (exists o3. get_rid o2 = get_rid o3 /\ ~ (Either? (rc o2 o3))) /\ 
   (Fst_then_snd? (rc o1 o2) \/ Ts_order? (rc o1 o2)))
  
let rc_inter_base_right'2 (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Ts_order? (rc ob ol) /\ fst ob < fst ol /\
                    distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ get_rid ob <> get_rid ol /\
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                    eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2) /\                 
                    eq (merge l (do l ol) (do l ob)) (do (do l ob) ol))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do (do l ob) ol) o2)) (do (do (do (do l ob) ol) o1) o2)) = ()

let rc_inter_base_left_e1 (l s1 s2 s3:concrete_st_e) (ob ol o1 o2:(nat & (nat & op_e))) 
  : Lemma (requires fst ob =!= fst ol /\ Fst_then_snd? (rc_e ob ol) /\
                    fst o1 =!= fst o2 /\ Fst_then_snd? (rc_e o1 o2) /\
                    eq_e (merge_e l (do_e s1 o1) (do_e s2 o2)) (do_e (do_e s3 o1) o2) /\
               eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e s2 ol) o2)) (do_e (do_e (do_e s3 ol) o1) o2) /\                 
                    eq_e (merge_e l (do_e s1 ob) (do_e s2 ol)) (do_e (do_e s3 ob) ol))
          (ensures eq_e (merge_e (do_e l ol) (do_e (do_e (do_e s1 ob) ol) o1) (do_e (do_e s2 ol) o2)) 
                        (do_e (do_e (do_e (do_e s3 ob) ol) o1) o2)) = ()

let rc_inter_base_left_e2 (l s1 s2 s3:concrete_st_e) (ob ol o1 o2:(nat & (nat & op_e))) 
  : Lemma (requires fst ob =!= fst ol /\ Enable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\
                    fst o1 =!= fst o2 /\ Fst_then_snd? (rc_e o1 o2) /\
                    eq_e (merge_e l (do_e s1 o1) (do_e s2 o2)) (do_e (do_e s3 o1) o2) /\
               eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e s2 ol) o2)) (do_e (do_e (do_e s3 ol) o1) o2) /\                 
                    eq_e (merge_e l (do_e s1 ob) (do_e s2 ol)) (do_e (do_e s3 ob) ol))
          (ensures eq_e (merge_e (do_e l ol) (do_e (do_e (do_e s1 ob) ol) o1) (do_e (do_e s2 ol) o2)) 
                        (do_e (do_e (do_e (do_e s3 ob) ol) o1) o2)) = ()
                        
let rc_inter_base_left' (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\
                    eq (merge l (do s1 ob) (do s2 ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let rc_inter_right'1 (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\  
                    distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
  (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

let rc_inter_right'2 (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\  
                    distinct_ops ob ol /\ Ts_order? (rc ob ol) /\ //get_rid ob <> get_rid ol /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    (~ (commutes_with o ob) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
  (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

let rc_inter_left'1 (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\  
                    distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

let rc_inter_left'2 (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\  
                    distinct_ops ob ol /\ Ts_order? (rc ob ol) /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()
      
let rc_inter_lca' (l s1 s2 s3:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    (exists o. Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi) \/ (Ts_order? (rc o oi) /\ fst o < fst oi)) /\ 
                    eq (merge (do l oi) (do (do s1 oi) o1) (do (do s2 oi) o2)) (do (do (do s3 oi) o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do s1 oi) ol) o1) (do (do (do s2 oi) ol) o2)) (do (do (do (do s3 oi) ol) o1) o2)) = ()
    
(*Two OP RCt*)
//////////////// 

let ts_ind_right' (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let ts_ind_left_l (l a b:concrete_st_l) (o1 o1' o2:(nat & (nat & op_l)))
  : Lemma (requires eq_l (merge_l l (do_l a o1) (do_l b o2)) (do_l (merge_l l (do_l a o1) b) o2))
          (ensures eq_l (merge_l l (do_l (do_l a o1') o1) (do_l b o2)) (do_l (merge_l l (do_l (do_l a o1') o1) b) o2)) = ()

let ts_ind_left_e (l a b:concrete_st_e) (o1 o1' o2:(nat & (nat & op_e)))
  : Lemma (requires fst o1 =!= fst o2 /\ Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\
                    (Fst_then_snd? (rc_e o1' o2) ==> eq_e (merge_e l (do_e (do_e a o1) o1') (do_e b o2)) 
                                                          (do_e (merge_e l (do_e (do_e a o1) o1') b) o2)) /\ //EXTRA!! from rc_ind_left
                    eq_e (merge_e l (do_e a o1) (do_e b o2)) (do_e (merge_e l (do_e a o1) b) o2))
          (ensures eq_e (merge_e l (do_e (do_e a o1') o1) (do_e b o2)) (do_e (merge_e l (do_e (do_e a o1') o1) b) o2)) = ()
          
let ts_ind_left' (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    get_rid o1 <> get_rid o2 /\ get_rid o1' <> get_rid o2 /\
                    (Fst_then_snd? (rc o1' o2) ==> eq (merge l (do (do a o1) o1') (do b o2)) (do (merge l (do (do a o1) o1') b) o2)) /\ //EXTRA!! from rc_ind_left
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = 
  ()//ts_ind_left_l (fst l) (fst a) (fst b) (get_op_l o1) (get_op_l o1') (get_op_l o2);
  //ts_ind_left_e (snd l) (snd a) (snd b) (get_op_e o1) (get_op_e o1') (get_op_e o2)

//Special case of rc_intermediate_v1
let ts_ind_lca' (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\ fst o1 < fst o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2)) = ()

let ts_base' (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let ts_inter_base_right_l (l s1 s2 s3:concrete_st_l) (ob ol o1 o2:(nat & (nat & op_l))) 
  : Lemma (requires eq_l (merge_l (do_l l ol) (do_l (do_l s1 ol) o1) (do_l (do_l s2 ol) o2)) (do_l (do_l (do_l s3 ol) o1) o2))
          (ensures eq_l (merge_l (do_l l ol) (do_l (do_l s1 ol) o1) (do_l (do_l (do_l s2 ob) ol) o2)) 
                        (do_l (do_l (do_l (do_l s3 ob) ol) o1) o2)) = ()

let ts_inter_base_right_e1 (l s1 s2 s3:concrete_st_e) (ob ol o1 o2:(nat & (nat & op_e))) 
  : Lemma (requires Fst_then_snd? (rc_e ob ol) /\ Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\
                    //eq_e (merge_e l (do_e s1 o1) (do_e (do_e s2 ob) o2)) (do_e (do_e (merge_e l s1 (do_e s2 ob)) o2) o1) /\ //EXTRA!! comes from comm_ind_right
          (Fst_then_snd? (rc_e ob o1) ==> (eq_e (merge_e l (do_e s1 o1) (do_e s2 ob)) (do_e (merge_e l s1 (do_e s2 ob)) o1))) /\ //EXTRA!!
                    eq_e (merge_e l (do_e s1 o1) (do_e s2 o2)) (do_e (do_e s3 o1) o2) /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e s2 ol) o2)) (do_e (do_e (do_e s3 ol) o1) o2) /\
                    eq_e (merge_e l (do_e s1 ol) (do_e s2 ob)) (do_e (do_e s3 ob) ol)) //***EXTRA***
          (ensures eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e (do_e s2 ob) ol) o2)) 
                        (do_e (do_e (do_e (do_e s3 ob) ol) o1) o2)) = ()

let ts_inter_base_right_e2 (l s1 s2 s3:concrete_st_e) (ob ol o1 o2:(nat & (nat & op_e))) 
  : Lemma (requires Enable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\ Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\
                    //eq_e (merge_e l (do_e s1 o1) (do_e (do_e s2 ob) o2)) (do_e (do_e (merge_e l s1 (do_e s2 ob)) o2) o1) /\ //EXTRA!! comes from comm_ind_right
                    (Fst_then_snd? (rc_e ob o1) ==> (eq_e (merge_e l (do_e s1 o1) (do_e s2 ob)) (do_e (merge_e l s1 (do_e s2 ob)) o1))) /\ //EXTRA!!
                    eq_e (merge_e l (do_e s1 o1) (do_e s2 o2)) (do_e (do_e s3 o1) o2) /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e s2 ol) o2)) (do_e (do_e (do_e s3 ol) o1) o2) /\
                    eq_e (merge_e l (do_e s1 ol) (do_e s2 ob)) (do_e (do_e s3 ob) ol)) //***EXTRA***
          (ensures eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e (do_e s2 ob) ol) o2)) 
                        (do_e (do_e (do_e (do_e s3 ob) ol) o1) o2)) = ()
                        
let ts_inter_base_right'1 (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                    eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2) /\
                    eq (merge l (do l ol) (do l ob)) (do (do l ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do (do l ob) ol) o2)) (do (do (do (do l ob) ol) o1) o2)) = ()

let ts_inter_base_right'2 (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Ts_order? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                    eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2) /\
                    eq (merge l (do l ol) (do l ob)) (do (do l ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do (do l ob) ol) o2)) (do (do (do (do l ob) ol) o1) o2)) = ()
          
let ts_inter_base_left_l (l s1 s2 s3:concrete_st_l) (ob ol o1 o2:(nat & (nat & op_l))) 
  : Lemma (requires eq_l (merge_l (do_l l ol) (do_l (do_l s1 ol) o1) (do_l (do_l s2 ol) o2)) (do_l (do_l (do_l s3 ol) o1) o2))
          (ensures eq_l (merge_l (do_l l ol) (do_l (do_l (do_l s1 ob) ol) o1) (do_l (do_l s2 ol) o2)) 
                        (do_l (do_l (do_l (do_l s3 ob) ol) o1) o2)) = ()

let ts_inter_base_left_e1 (l s1 s2 s3:concrete_st_e) (ob ol o1 o2:(nat & (nat & op_e))) 
  : Lemma (requires Fst_then_snd? (rc_e ob ol) /\ Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\
                    //eq_e (merge_e l (do_e (do_e s1 ob) o1) (do_e s2 o2)) (do_e (do_e (merge_e l (do_e s1 ob) s2) o2) o1) /\ //EXTRA!! comes from comm_ind_left
            (Fst_then_snd? (rc_e ob o2) ==> eq_e (merge_e l (do_e s1 ob) (do_e s2 o2)) (do_e (merge_e l (do_e s1 ob) s2) o2)) /\ //EXTRA!!
                    eq_e (merge_e l (do_e s1 o1) (do_e s2 o2)) (do_e (do_e s3 o1) o2) /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e s2 ol) o2)) (do_e (do_e (do_e s3 ol) o1) o2) /\
                    eq_e (merge_e l (do_e s1 ob) (do_e s2 ol)) (do_e (do_e s3 ob) ol)) //***EXTRA***
          (ensures eq_e (merge_e (do_e l ol) (do_e (do_e (do_e s1 ob) ol) o1) (do_e (do_e s2 ol) o2)) 
                        (do_e (do_e (do_e (do_e s3 ob) ol) o1) o2)) = ()

let ts_inter_base_left_e2 (l s1 s2 s3:concrete_st_e) (ob ol o1 o2:(nat & (nat & op_e))) 
  : Lemma (requires Enable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\ Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\
                    //eq_e (merge_e l (do_e (do_e s1 ob) o1) (do_e s2 o2)) (do_e (do_e (merge_e l (do_e s1 ob) s2) o2) o1) /\ //EXTRA!! comes from comm_ind_left
                    eq_e (merge_e l (do_e s1 o1) (do_e s2 o2)) (do_e (do_e s3 o1) o2) /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e s2 ol) o2)) (do_e (do_e (do_e s3 ol) o1) o2) /\
                    eq_e (merge_e l (do_e s1 ob) (do_e s2 ol)) (do_e (do_e s3 ob) ol)) //***EXTRA***
          (ensures eq_e (merge_e (do_e l ol) (do_e (do_e (do_e s1 ob) ol) o1) (do_e (do_e s2 ol) o2)) 
                        (do_e (do_e (do_e (do_e s3 ob) ol) o1) o2)) = ()

let ts_inter_base_left'1 (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                    eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2) /\
                    eq (merge l (do l ob) (do l ol)) (do (do l ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do l ob) ol) o1) (do (do l ol) o2)) (do (do (do (do l ob) ol) o1) o2)) = ()

let ts_inter_base_left'2 (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Ts_order? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                    eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2) /\
                    eq (merge l (do l ob) (do l ol)) (do (do l ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do l ob) ol) o1) (do (do l ol) o2)) (do (do (do (do l ob) ol) o1) o2)) = ()

let ts_inter_right_l (l s1 s2 s3:concrete_st_l) (o1 o2 ob ol o:(nat & (nat & op_l)))
  : Lemma (requires eq_l (merge_l (do_l l ol) (do_l (do_l s1 ol) o1) (do_l (do_l (do_l s2 ob) ol) o2)) 
                         (do_l (do_l (do_l (do_l s3 ob) ol) o1) o2))
          (ensures eq_l (merge_l (do_l l ol) (do_l (do_l s1 ol) o1) (do_l (do_l (do_l (do_l s2 o) ob) ol) o2)) 
                        (do_l (do_l (do_l (do_l (do_l s3 o) ob) ol) o1) o2)) = ()

let ts_inter_right_e1 (l s1 s2 s3:concrete_st_e) (o1 o2 ob ol o:(nat & (nat & op_e)))
  : Lemma (requires Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\
                    Fst_then_snd? (rc_e ob ol) /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (((Disable? (snd (snd o)) /\ Enable? (snd (snd ob))) \/ (Enable? (snd (snd o)) /\ Disable? (snd (snd ob))) \/
                      (Enable? (snd (snd o)) /\ Enable? (snd (snd ob)))) \/
                      Fst_then_snd? (rc_e o ol) \/ (Enable? (snd (snd o)) /\ Enable? (snd (snd ol)) /\ fst o < fst ol)) /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e (do_e s2 ob) ol) o2)) 
                         (do_e (do_e (do_e (do_e s3 ob) ol) o1) o2))
      (ensures eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e (do_e (do_e s2 o) ob) ol) o2)) 
                    (do_e (do_e (do_e (do_e (do_e s3 o) ob) ol) o1) o2)) = ()

#set-options "--z3rlimit 300 --ifuel 3"
let ts_inter_right_e2 (l s1 s2 s3:concrete_st_e) (o1 o2 ob ol o:(nat & (nat & op_e)))
  : Lemma (requires Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\
                    Enable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\
                    get_rid o <> get_rid ol /\ get_rid o2 = get_rid ob /\ get_rid o = get_rid o2 /\ get_rid o1 <> get_rid o2 /\ //EXTRA!!
                    Either? (rc_e o ol) /\ 
                    (((Disable? (snd (snd o)) /\ Enable? (snd (snd ob))) \/ (Enable? (snd (snd o)) /\ Disable? (snd (snd ob))) \/
                      (Enable? (snd (snd o)) /\ Enable? (snd (snd ob)))) \/
                      Fst_then_snd? (rc_e o ol) \/ (Enable? (snd (snd o)) /\ Enable? (snd (snd ol)) /\ fst o < fst ol)) /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e (do_e s2 ob) ol) o2)) 
                         (do_e (do_e (do_e (do_e s3 ob) ol) o1) o2))
      (ensures eq_e (merge_e (do_e l ol) (do_e (do_e s1 ol) o1) (do_e (do_e (do_e (do_e s2 o) ob) ol) o2)) 
                    (do_e (do_e (do_e (do_e (do_e s3 o) ob) ol) o1) o2)) = ()
                    
let ts_inter_right'1 (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    //get_rid o <> get_rid ol /\ 
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    //distinct_ops o ol /\ Either? (rc o ol) /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

let lo' (o1 o2:op_t) =
  (get_rid o1 = get_rid o2 /\ fst o1 < fst o2 /\ ~ (Either? (rc o1 o2))) \/
  (get_rid o1 <> get_rid o2 /\ ~ (exists o3. fst o2 < fst o3 /\ get_rid o2 = get_rid o3 /\ ~ (Either? (rc o2 o3))) /\ 
   (Fst_then_snd? (rc o1 o2) \/ (Ts_order? (rc o1 o2) /\ fst o1 < fst o2)))

let lo_mod (o1 o2 o3:op_t) =
  (get_rid o1 = get_rid o2 /\ ~ (Either? (rc o1 o2))) \/
  (get_rid o1 <> get_rid o2 /\ ~ (get_rid o2 = get_rid o3 /\ ~ (Either? (rc o2 o3))) /\ 
   (Fst_then_snd? (rc o1 o2) \/ Ts_order? (rc o1 o2)))

#set-options "--z3rlimit 500 --ifuel 5"
let ts_inter_right' (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    distinct_ops ob ol /\ Ts_order? (rc ob ol) /\ fst ob < fst ol /\ get_rid ob <> get_rid ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid ob /\ get_rid o1 <> get_rid o2 /\ get_rid o <> get_rid o1 /\ //EXTRA!!
                    Set? (snd (snd o)) /\
                    (Either? (rc o o1) \/ lo o o1) /\
                    (Either? (rc o o2) \/ lo o o2) /\
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    (Either? (rc ob o2) \/ lo ob o2) /\
                    (Either? (rc ol o1) \/ lo ol o1) /\
                    (Either? (rc ol o2) \/ lo ol o2) /\
                    (Either? (rc o ob) \/ lo' o ob) /\
                    (Either? (rc o ol) \/ lo' o ol) /\
                    (Either? (rc ob ol) \/ lo' ob ol) /\
                    //get_rid o2 = get_rid ob /\
                    eq (merge (do l ol) (do (do l ol) o1) (do (do (do (do l o) ob) ol) o2)) (do (do (do (do (do l o) ob) ol) o1) o2) /\
                    ((Fst_then_snd? (rc o1 o2) \/ Either? (rc o1 o2)) ==> eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 o) ob) ol)) (do (do (do (do s3 o) ob) ol) o1) /\
                    eq (merge (do l ol) (do s1 ol) (do (do (do s2 o) ob) ol)) (do (do (do s3 o) ob) ol) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol) /\
                    eq (merge l s1 (do (do s2 o1) o2)) (do (merge l s1 (do s2 o1)) o2) /\
                    eq (merge l (do (do s1 o1) o2) s2) (do (merge l (do s1 o1) s2) o2) /\
                    eq (merge (do l ol) (do (do s2 ol) o1) (do (do (do (do s1 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) /\
                    eq (merge l (do s1 o1) (do (do s2 ob) o2)) (do (merge l (do s1 o1) (do s2 ob)) o2) /\               
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq_e (snd (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2))) (snd (do (do (do (do (do s3 o) ob) ol) o1) o2))) = admit()

#set-options "--z3rlimit 500 --ifuel 5"
let ts_inter_right'2 (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    distinct_ops ob ol /\ Ts_order? (rc ob ol) /\ fst ob < fst ol /\ get_rid ob <> get_rid ol /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ get_rid o1 <> get_rid o /\
                    (Either? (rc ob o1) \/ lo ob o1) /\ (Either? (rc ob o2) \/ lo ob o2) /\
                    (Either? (rc ol o1) \/ lo ol o1) /\ (Either? (rc ol o2) \/ lo ol o2) /\
                    (Either? (rc o o1) \/ lo o o1) /\ (Either? (rc o o2) \/ lo o o2) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq_e (snd (merge l (do s1 o2) (do s2 o1))) (snd (do (do s3 o1) o2)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol) /\
                    eq_e (snd (merge l (do s1 ob) (do s2 ol))) (snd (do (do s3 ob) ol)) /\
                    eq (merge l (do s1 o1) (do (do s2 o) o2)) (do (merge l (do s1 o1) (do s2 o)) o2) /\
                    eq (merge l (do s1 o1) (do (do s2 ob) o2)) (do (merge l (do s1 o1) (do s2 ob)) o2) /\
                    eq (merge l (do s1 o1) (do (do s2 ol) o2)) (do (merge l (do s1 o1) (do s2 ol)) o2) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l o2) (do (do s1 o2) ob) (do (do (do s2 o1) o2) ol)) (do (do (do (do s3 o1) o2) ob) ol) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2) )
      (ensures eq_e (snd (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2))) (snd (do (do (do (do (do s3 o) ob) ol) o1) o2))) = admit();
  (*if Set? (snd (snd o)) && get_rid o = get_rid o2 && get_rid ob = get_rid o2 then admit() //done
  else if Set? (snd (snd o)) && get_rid o = get_rid o2 && get_rid ob <> get_rid o2 then admit() //done
  else*) if Set? (snd (snd o)) && get_rid o <> get_rid o2 && get_rid ob = get_rid o2 then () //not done
  (*else if Set? (snd (snd o)) && get_rid o <> get_rid o2 && get_rid ob <> get_rid o2 then admit() //not done
  else if Unset? (snd (snd o)) && get_rid o = get_rid o2 && get_rid ob = get_rid o2 then admit() //not done
  else if Unset? (snd (snd o)) && get_rid o = get_rid o2 && get_rid ob <> get_rid o2 then admit() //not done
  else if Unset? (snd (snd o)) && get_rid o <> get_rid o2 && get_rid ob = get_rid o2 then admit()*) //not done
  else admit() //not done

let ts_inter_left_l (l s1 s2 s3:concrete_st_l) (o1 o2 ob ol o:(nat & (nat & op_l)))
  : Lemma (requires eq_l (merge_l (do_l l ol) (do_l (do_l (do_l s1 ob) ol) o1) (do_l (do_l s2 ol) o2)) 
                         (do_l (do_l (do_l (do_l s3 ob) ol) o1) o2))
          (ensures eq_l (merge_l (do_l l ol) (do_l (do_l (do_l (do_l s1 o) ob) ol) o1) (do_l (do_l s2 ol) o2)) 
                        (do_l (do_l (do_l (do_l (do_l s3 o) ob) ol) o1) o2)) = ()

let ts_inter_left_e1 (l s1 s2 s3:concrete_st_e) (o1 o2 ob ol o:(nat & (nat & op_e)))
  : Lemma (requires Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\
                    Fst_then_snd? (rc_e ob ol) /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (((Disable? (snd (snd o)) /\ Enable? (snd (snd ob))) \/ (Enable? (snd (snd o)) /\ Disable? (snd (snd ob))) \/
                      (Enable? (snd (snd o)) /\ Enable? (snd (snd ob)))) \/
                      Fst_then_snd? (rc_e o ol) \/ (Enable? (snd (snd o)) /\ Enable? (snd (snd ol)) /\ fst o < fst ol)) /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e (do_e s1 ob) ol) o1) (do_e (do_e s2 ol) o2)) 
                         (do_e (do_e (do_e (do_e s3 ob) ol) o1) o2))
      (ensures eq_e (merge_e (do_e l ol) (do_e (do_e (do_e (do_e s1 o) ob) ol) o1) (do_e (do_e s2 ol) o2)) 
                    (do_e (do_e (do_e (do_e (do_e s3 o) ob) ol) o1) o2)) = ()

let ts_inter_left'1 (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    //get_rid o <> get_rid ol /\ 
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    //distinct_ops o ol /\ Either? (rc o ol) /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

#set-options "--z3rlimit 500 --ifuel 5"
let ts_inter_left'2 (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    distinct_ops ob ol /\ Ts_order? (rc ob ol) /\ fst ob < fst ol /\
                    //get_rid o <> get_rid ol /\ 
                    get_rid o1 <> get_rid o2 /\ get_rid o1 <> get_rid ob /\ 
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    (Either? (rc ol o1) \/ lo ol o1) /\
                    (Either? (rc o o1) \/ lo o o1) /\
                    (Either? (rc ob o2) \/ lo ob o2) /\
                    (Either? (rc ol o2) \/ lo ol o2) /\
                    (Either? (rc o o2) \/ lo o o2) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do s2 ol)) (do (do (do s3 ob) ol) o1) /\ //EXTRA!! comes from one_op_inter_base_right'
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o2) (do s2 ol)) (do (do (do s3 ob) ol) o2) /\ //EXTRA!! comes from one_op_inter_base_right'
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o) (do s2 ol)) (do (do (do s3 ob) ol) o) /\ //EXTRA!! comes from one_op_inter_base_right'
                    (Fst_then_snd? (rc o1 o2) ==> eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                    eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2) /\
                    eq (merge l (do l ob) (do l ol)) (do (do l ob) ol) /\
                    eq (merge (do l ol) (do (do (do (do l o) ob) ol) o1) (do (do l ol) o2)) (do (do (do (do (do l o) ob) ol) o1) o2) /\
                    //distinct_ops o ol /\ Either? (rc o ol) /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = admit()
      
let ts_inter_lca' (l s1 s2 s3:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    (exists o. Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi) \/ (Ts_order? (rc o oi) /\ fst o < fst oi)) /\ 
                    eq (merge (do l oi) (do (do s1 oi) o1) (do (do s2 oi) o2)) (do (do (do s3 oi) o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do s1 oi) ol) o1) (do (do (do s2 oi) ol) o2)) (do (do (do (do s3 oi) ol) o1) o2)) = ()

(**One op*)
///////////////
let one_op_ind_right' (l a b c:concrete_st) (o2 o2':op_t)
   : Lemma (requires eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2)) = () //done

let one_op_ind_left' (l a b c:concrete_st) (o1 o1':op_t)
   : Lemma (requires eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) = () //done

let one_op_ind_lca' (l:concrete_st) (ol o1:op_t)
  : Lemma (requires eq (merge l (do l o1) l) (do l o1) /\ fst ol < fst o1)
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do l ol)) (do (do l ol) o1)) = () //done

let one_op_base' (o1:op_t)
  : Lemma (ensures eq (merge init_st (do init_st o1) init_st) (do init_st o1)) = () //done

let one_op_inter_base_right' (l s1 s2 s3:concrete_st) (ob ol o1:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    eq (merge l s1 (do s2 o1)) (do s3 o1) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ol) o1)) (do (do s3 ol) o1) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do s1 ol) (do (do (do s2 ob) ol) o1)) (do (do (do s3 ob) ol) o1)) = () //done

let one_op_inter_base_left' (l s1 s2 s3:concrete_st) (ob ol o1:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    eq (merge l s1 (do s2 o1)) (do s3 o1) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ol) o1)) (do (do s3 ol) o1) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol) /\ //***EXTRA***
                    eq (merge l (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol) /\ //***EXTRA***
                    (Fst_then_snd? (rc ob o1) ==> eq (merge l (do s1 o1) (do s2 ob)) (do (merge l s1 (do s2 ob)) o1))) //***EXTRA*** 
          (ensures eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1)) = () //done

let one_op_inter_right'1 (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid ob /\ get_rid o <> get_rid o1 /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ob) ol) ) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 o) ob) ol)) (do (do (do (do s3 o) ob) ol) o1)) = ()

let one_op_inter_right'2_base (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Ts_order? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid ob /\ get_rid o <> get_rid o1 /\ //EXTRA!!
                    (Either? (rc ob o1) \/ lo ob o1) /\
                    //(Either? (rc o o1) \/ lo o o1) /\
                    //(Either? (rc ol o1) \/ lo ol o1) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ob) ol) ) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do (do l o) ob) ol)) (do (do (do (do l o) ob) ol) o1)) = ()

let one_op_inter_right'2 (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Ts_order? (rc ob ol) /\ fst ob < fst ol /\ get_rid ob <> get_rid ol /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid ob /\ get_rid o1 <> get_rid o /\
                    (Either? (rc o o1) \/ lo o o1) /\
                    (forall o2. ((Either? (rc o1 o2) \/ lo o1 o2) /\ get_rid o1 <> get_rid o2) ==> eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) /\ //rc_inter_right
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ob) ol) ) (do (do (do s3 ob) ol) o1))
          (ensures eq_e (snd (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 o) ob) ol))) (snd (do (do (do (do s3 o) ob) ol) o1))) = ()

(*let one_op_inter_right'1 (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ob) ol) ) (do (do (do s3 ob) ol) o1))
          (ensures eq_e (snd (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 o) ob) ol))) (snd (do (do (do (do s3 o) ob) ol) o1))) = () 

let one_op_inter_right'2 (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires Ts_order? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 = get_rid ob /\ get_rid o = get_rid o1 /\ //EXTRA!!
                    ~ (exists e. (~ (commutes_with e o1) /\ get_rid e = get_rid o1) \/ 
                            (get_rid e <> get_rid o1 /\ (Fst_then_snd? (rc o1 e) \/ Ts_order? (rc o1 e)))) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ob) ol) ) (do (do (do s3 ob) ol) o1))
          (ensures eq_e (snd (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 o) ob) ol))) (snd (do (do (do (do s3 o) ob) ol) o1))) = 
  if Set? (snd (snd o)) && Unset? (snd (snd o1)) then () //done
  else if Set? (snd (snd o)) && Unset? (snd (snd o1)) then () //done
  else if Unset? (snd (snd o)) && Set? (snd (snd o1)) then () //done
  else ()
            
let one_op_inter_right'_e (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 = get_rid ob /\ get_rid o = get_rid o1 /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    ~ (exists e. (~ (commutes_with e o1) /\ get_rid e = get_rid o1) \/ 
                            (get_rid e <> get_rid o1 /\ (Fst_then_snd? (rc o1 e) \/ Ts_order? (rc o1 e)))) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ob) ol) ) (do (do (do s3 ob) ol) o1))
          (ensures eq_e (snd (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 o) ob) ol))) (snd (do (do (do (do s3 o) ob) ol) o1))) = 
  if Fst_then_snd? (rc ob ol) then one_op_inter_right'1 l s1 s2 s3 o1 ob ol o 
  else one_op_inter_right'2 l s1 s2 s3 o1 ob ol o

let one_op_inter_right' (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 = get_rid ob /\ get_rid o = get_rid o1 /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    ~ (exists e. (~ (commutes_with e o1) /\ get_rid e = get_rid o1) \/ 
                            (get_rid e <> get_rid o1 /\ (Fst_then_snd? (rc o1 e) \/ Ts_order? (rc o1 e)))) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ob) ol) ) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 o) ob) ol)) (do (do (do (do s3 o) ob) ol) o1)) = 
  one_op_inter_right'_e l s1 s2 s3 o1 ob ol o

let one_op_inter_left'1 (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do (do s2 ol) o1)) (do (do (do (do s3 o) ob) ol) o1)) = ()

let one_op_inter_left'2e (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires Ts_order? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 = get_rid ob /\ get_rid o = get_rid o1 /\ //EXTRA!!
                    ~ (exists e. (~ (commutes_with e o1) /\ get_rid e = get_rid o1) \/ 
                            (get_rid e <> get_rid o1 /\ (Fst_then_snd? (rc o1 e) \/ Ts_order? (rc o1 e)))) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1))
          (ensures eq_e (snd (merge (do l ol) (do (do (do s1 o) ob) ol) (do (do s2 ol) o1))) (snd (do (do (do (do s3 o) ob) ol) o1))) = 
  if Set? (snd (snd o)) && Unset? (snd (snd o1)) then () //done
  else if Set? (snd (snd o)) && Unset? (snd (snd o1)) then () //done
  else if Unset? (snd (snd o)) && Set? (snd (snd o1)) then () //done
  else ()

let one_op_inter_left'2 (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires Ts_order? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 = get_rid ob /\ get_rid o = get_rid o1 /\ //EXTRA!!
                    ~ (exists e. (~ (commutes_with e o1) /\ get_rid e = get_rid o1) \/ 
                            (get_rid e <> get_rid o1 /\ (Fst_then_snd? (rc o1 e) \/ Ts_order? (rc o1 e)))) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do (do s2 ol) o1)) (do (do (do (do s3 o) ob) ol) o1)) = 
  one_op_inter_left'2e l s1 s2 s3 o1 ob ol o
          
let one_op_inter_left' (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 = get_rid ob /\ get_rid o = get_rid o1 /\ //EXTRA!!
                    ~ (exists e. (~ (commutes_with e o1) /\ get_rid e = get_rid o1) \/ 
                            (get_rid e <> get_rid o1 /\ (Fst_then_snd? (rc o1 e) \/ Ts_order? (rc o1 e)))) /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do (do s2 ol) o1)) (do (do (do (do s3 o) ob) ol) o1)) = 
  if Fst_then_snd? (rc ob ol) then one_op_inter_left'1 l s1 s2 s3 o1 ob ol o 
  else one_op_inter_left'2 l s1 s2 s3 o1 ob ol o*)

let one_op_inter_left'1 (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid ob /\ get_rid o <> get_rid o1 /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do (do s2 ol) o1)) (do (do (do (do s3 o) ob) ol) o1)) = ()

let one_op_inter_left'2 (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Ts_order? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid ob /\ get_rid o <> get_rid o1 /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do (do s2 ol) o1)) (do (do (do (do s3 o) ob) ol) o1)) = admit()

let one_op_inter_left'2_mod (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Ts_order? (rc ob ol)  /\ fst ob < fst ol /\ get_rid ob <> get_rid ol /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    get_rid o1 <> get_rid ob /\ get_rid o <> get_rid o1 /\ //EXTRA!!
                    (Either? (rc o o1) \/ lo o o1) /\
                    (forall o2. ((Either? (rc o1 o2) \/ lo o1 o2) /\ get_rid o1 <> get_rid o2) ==> eq (merge (do l ol) (do (do (do s1 ob) ol) o2) (do (do s2 ol) o1)) (do (do (do (do s3 ob) ol) o1) o2)) /\ //rc_inter_right
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1))
          (ensures eq_e (snd (merge (do l ol) (do (do (do s1 o) ob) ol) (do (do s2 ol) o1))) (snd (do (do (do (do s3 o) ob) ol) o1))) = 
  one_op_inter_right'2 l s2 s1 s3 o1 ob ol o
          
// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let one_op_inter_lca' (l s1 s2 s3:concrete_st) (o1 ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi) \/ (Ts_order? (rc o oi) /\ fst o < fst oi)) /\ 
                    eq (merge (do l oi) (do s1 oi) (do (do s2 oi) o1)) (do (do s3 oi) o1) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ol) o1)) (do (do s3 ol) o1))
          (ensures eq (merge (do (do l oi) ol) (do (do s1 oi) ol) (do (do (do s2 oi) ol) o1)) (do (do (do s3 oi) ol) o1)) = ()

(*Zero op *)
///////////////
// because we proved that e_i^l rcp eb is not possible.
//e_i^l vis eb is not possible
// so either eb rcp e_i^l or eb rct e_i^l is possible
let zero_op_inter_base_right' (l s1 s2 s3:concrete_st) (ob ol:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    eq (merge l s1 s2) s3 /\
                    eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol)) = ()

let zero_op_inter_base_left' (l s1 s2 s3:concrete_st) (ob ol:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    eq (merge l s1 s2) s3 /\
                    eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol) /\
                    eq (merge l (do s1 ob) (do s2 ol)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol)) = ()

(*let zero_op_inter_right_l (l s1 s2 s3:concrete_st_l) (ob ol o:(nat & (nat & op_l)))
  : Lemma (requires eq_l (merge_l (do_l l ol) (do_l s1 ol) (do_l (do_l s2 ob) ol)) (do_l (do_l s3 ob) ol))
          (ensures eq_l (merge_l (do_l l ol) (do_l s1 ol) (do_l (do_l (do_l s2 o) ob) ol)) (do_l (do_l (do_l s3 o) ob) ol)) = ()

let zero_op_inter_right_e1 (l s1 s2 s3:concrete_st_e) (ob ol o:(nat & (nat & op_e)))
  : Lemma (requires Fst_then_snd? (rc_e ob ol) /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (((Disable? (snd (snd o)) /\ Enable? (snd (snd ob))) \/ (Enable? (snd (snd o)) /\ Disable? (snd (snd ob))) \/
                      (Enable? (snd (snd o)) /\ Enable? (snd (snd ob)))) \/
                      Fst_then_snd? (rc_e o ol) \/ (Enable? (snd (snd o)) /\ Enable? (snd (snd ol)) /\ fst o < fst ol)) /\
                    eq_e (merge_e (do_e l ol) (do_e s1 ol) (do_e (do_e s2 ob) ol)) (do_e (do_e s3 ob) ol))
          (ensures eq_e (merge_e (do_e l ol) (do_e s1 ol) (do_e (do_e (do_e s2 o) ob) ol)) (do_e (do_e (do_e s3 o) ob) ol)) = ()

let zero_op_inter_right_e2 (l s1 s2 s3:concrete_st_e) (ob ol o:(nat & (nat & op_e)))
  : Lemma (requires Enable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    eq_e (merge_e (do_e l ol) (do_e s1 ol) (do_e (do_e (do_e s2 ob) ol) o)) (do_e (do_e (do_e s3 ob) ol) o) /\ //EXTRA!! comes from one_op_inter_base_right'
                    (((Disable? (snd (snd o)) /\ Enable? (snd (snd ob))) \/ (Enable? (snd (snd o)) /\ Disable? (snd (snd ob))) \/
                      (Enable? (snd (snd o)) /\ Enable? (snd (snd ob)))) \/
                      Fst_then_snd? (rc_e o ol) \/ (Enable? (snd (snd o)) /\ Enable? (snd (snd ol)) /\ fst o < fst ol)) /\
                    eq_e (merge_e (do_e l ol) (do_e s1 ol) (do_e (do_e s2 ob) ol)) (do_e (do_e s3 ob) ol))
          (ensures eq_e (merge_e (do_e l ol) (do_e s1 ol) (do_e (do_e (do_e s2 o) ob) ol)) (do_e (do_e (do_e s3 o) ob) ol)) = ()
          
let zero_op_inter_right' (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    eq (merge (do l ol) (do s1 ol) (do (do (do s2 ob) ol) o)) (do (do (do s3 ob) ol) o) /\ //EXTRA!! comes from one_op_inter_base_right'
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do s1 ol) (do (do (do s2 o) ob) ol)) (do (do (do s3 o) ob) ol)) =
  zero_op_inter_right_l (fst l) (fst s1) (fst s2) (fst s3) (get_op_l ob) (get_op_l ol) (get_op_l o);
  if Fst_then_snd? (rc ob ol) then
    zero_op_inter_right_e1 (snd l) (snd s1) (snd s2) (snd s3) (get_op_e ob) (get_op_e ol) (get_op_e o)
  else zero_op_inter_right_e2 (snd l) (snd s1) (snd s2) (snd s3) (get_op_e ob) (get_op_e ol) (get_op_e o)*)

let zero_op_inter_right'1 (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do s1 ol) (do (do (do s2 o) ob) ol)) (do (do (do s3 o) ob) ol)) = ()

let zero_op_inter_right'2 (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Ts_order? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    eq (merge (do l ol) (do s1 ol) (do (do (do s2 ob) ol) o)) (do (do (do s3 ob) ol) o) /\ //EXTRA!! comes from one_op_inter_base_right'
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do s1 ol) (do (do (do s2 o) ob) ol)) (do (do (do s3 o) ob) ol)) = ()
          
(*let zero_op_inter_left_e1 (l s1 s2 s3:concrete_st_e) (ob ol o:(nat & (nat & op_e)))
  : Lemma (requires Fst_then_snd? (rc_e ob ol) /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (((Disable? (snd (snd o)) /\ Enable? (snd (snd ob))) \/ (Enable? (snd (snd o)) /\ Disable? (snd (snd ob))) \/
                      (Enable? (snd (snd o)) /\ Enable? (snd (snd ob)))) \/
                      Fst_then_snd? (rc_e o ol) \/ (Enable? (snd (snd o)) /\ Enable? (snd (snd ol)) /\ fst o < fst ol)) /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e s1 ob) ol) (do_e s2 ol)) (do_e (do_e s3 ob) ol))
          (ensures eq_e (merge_e (do_e l ol) (do_e (do_e (do_e s1 o) ob) ol) (do_e s2 ol)) (do_e (do_e (do_e s3 o) ob) ol)) = ()

let zero_op_inter_left_e2 (l s1 s2 s3:concrete_st_e) (ob ol o:(nat & (nat & op_e)))
  : Lemma (requires Enable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //get_rid o = get_rid ob /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e (do_e s1 ob) ol) o) (do_e s2 ol)) (do_e (do_e (do_e s3 ob) ol) o) /\ //EXTRA!!
                    //eq_e (merge_e l (do_e (do_e s1 ob) ol) (do_e s2 ol)) (do_e (do_e s3 ob) ol) /\ //EXTRA!!
                    //eq_e (merge_e (do_e l ol) (do_e s1 ol) (do_e (do_e (do_e s2 ob) ol) o)) (do_e (do_e (do_e s3 ob) ol) o) /\ //EXTRA!! comes from one_op_inter_base_right'
                    (((Disable? (snd (snd o)) /\ Enable? (snd (snd ob))) \/ (Enable? (snd (snd o)) /\ Disable? (snd (snd ob))) \/
                      (Enable? (snd (snd o)) /\ Enable? (snd (snd ob)))) \/
                      Fst_then_snd? (rc_e o ol) \/ (Enable? (snd (snd o)) /\ Enable? (snd (snd ol)) /\ fst o < fst ol)) /\
                    eq_e (merge_e (do_e l ol) (do_e (do_e s1 ob) ol) (do_e s2 ol)) (do_e (do_e s3 ob) ol))
          (ensures eq_e (merge_e (do_e l ol) (do_e (do_e (do_e s1 o) ob) ol) (do_e s2 ol)) (do_e (do_e (do_e s3 o) ob) ol)) = ()
          
let zero_op_inter_left' (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o_n,ol must be concurrent*) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o) (do s2 ol)) (do (do (do s3 ob) ol) o) /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do s2 ol)) (do (do (do s3 o) ob) ol)) = 
  if Fst_then_snd? (rc ob ol) then
    zero_op_inter_left_e1 (snd l) (snd s1) (snd s2) (snd s3) (get_op_e ob) (get_op_e ol) (get_op_e o)
  else zero_op_inter_left_e2 (snd l) (snd s1) (snd s2) (snd s3) (get_op_e ob) (get_op_e ol) (get_op_e o)*)

let zero_op_inter_left'1 (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do s2 ol)) (do (do (do s3 o) ob) ol)) = ()

let zero_op_inter_left'2 (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Ts_order? (rc ob ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o) (do s2 ol)) (do (do (do s3 ob) ol) o) /\ //EXTRA!!
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do s2 ol)) (do (do (do s3 o) ob) ol)) = ()

// In general, the event "ol" below should be such that these exists o', (rc o' ol)
let zero_op_inter_lca_v1' (l s1 s2 s3:concrete_st) (ol:op_t)
  : Lemma (requires (exists o'. Fst_then_snd? (rc o' ol) \/ (Ts_order? (rc o' ol) /\ fst o' < fst ol)) /\ eq (merge l s1 s2) s3)
          (ensures eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol)) = ()

// In general, the events ol,o_n, below should be such that these exists o, (rc o ol)
let zero_op_inter_lca_v2' (l s1 s2 s3:concrete_st) (ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi) \/ (Ts_order? (rc o oi) /\ fst o < fst oi)) /\
                    eq (merge (do l oi) (do s1 oi) (do s2 oi)) (do s3 oi)  /\
                    eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol))
          (ensures eq (merge (do (do l oi) ol) (do (do s1 oi) ol) (do (do s2 oi) ol)) (do (do s3 oi) ol)) = ()

(* 2 op Comm  *)
///////////////////

let comm_ind_right' (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o2' o1 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) )
                    //~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()

let comm_ind_left' (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o2' o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o2) ==> (eq (merge l (do a o2') (do b o2)) (do (merge l (do a o2') b) o2))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o2')))
                    //~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o2') o1) (do b o2)) (do (do (merge l (do a o2') b) o2) o1)) = ()

let comm_ind_lca' (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base' (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_inter_base_right' (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    distinct_ops o1 o2 /\ Either? (rc o1 o2) /\
                    distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\ 
                    eq (merge l (do s1 o1) (do (do s2 ob) o2)) (do (do (merge l s1 (do s2 ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let comm_inter_base_left' (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    distinct_ops o1 o2 /\ Either? (rc o1 o2) /\
                    distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\ 
                    eq (merge l (do (do s1 ob) o1) (do s2 o2)) (do (do (merge l (do s1 ob) s2) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let comm_inter_right' (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\  
                    distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    distinct_ops o ol /\ //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

let comm_inter_left' (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\  
                    distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    distinct_ops o ol /\ //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

let comm_inter_lca' (l s1 s2 s3:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    (exists o'. Fst_then_snd? (rc o' ol) \/ (Ts_order? (rc o' ol) /\ fst o' < fst ol)) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2)) = ()

////////////////////////////////////////////////////////////////
