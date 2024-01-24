module App_new_ts

#set-options "--query_stats"

// the concrete state type
type concrete_st = int

// init state
let init_st = 0

// equivalence between 2 concrete states
let eq (a b:concrete_st) = a = b

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
  |Inc
  |Dec

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =  
  if snd (snd o) = Inc then s + 1 else s - 1

//conflict resolution
let rc (o1 o2:op_t) = Either

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  a + b - l
   
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

let cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:log)
  : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ cond_comm o1 o2 o3 /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3)) = ()
  
/////////////////////////////////////////////////////////////////////////////
// Merge commutativity
let merge_comm (l a b:concrete_st)
   : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

// Merge idempotence
let merge_idem (s:concrete_st)
   : Lemma (ensures eq (merge s s s) s) = ()

(*Two OP RCp*)
//////////////// 
let rc_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let rc_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

//Special case of rc_intermediate_v1
let rc_ind_lca (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2)) = ()

let rc_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

// because we proved that e_i^l rcp e is not possible. e_i^l is o' e is o here.
//e_i^l vis e is not possible
// so either e rcp e_i^l or e rct e_i^l is possible
let rc_inter_base_right (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\                 
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let rc_inter_base_left (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\
                    eq (merge l (do s1 ob) (do s2 ol)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()
          
let rc_inter_right (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\  
                    distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
  (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()
  
let rc_inter_left (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\  
                    distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let rc_inter_lca (l s1 s2 s3:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    (exists o. Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi) \/ (Ts_order? (rc o oi) /\ fst o < fst oi)) /\ 
                    eq (merge (do l oi) (do (do s1 oi) o1) (do (do s2 oi) o2)) (do (do (do s3 oi) o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do s1 oi) ol) o1) (do (do (do s2 oi) ol) o2)) (do (do (do (do s3 oi) ol) o1) o2)) = ()

(*Two OP RCt*)
//////////////// 
let ts_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let ts_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

//Special case of rc_intermediate_v1
let ts_ind_lca (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\ fst o1 < fst o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2)) = ()

let ts_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let ts_inter_base_right (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let ts_inter_base_left (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\
                    eq (merge l (do s1 ob) (do s2 ol)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let ts_inter_right (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

let ts_inter_left (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\ 
                    distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let ts_inter_lca (l s1 s2 s3:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Ts_order? (rc o1 o2) /\ fst o1 < fst o2 /\
                    (exists o. Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi) \/ (Ts_order? (rc o oi) /\ fst o < fst oi)) /\ 
                    eq (merge (do l oi) (do (do s1 oi) o1) (do (do s2 oi) o2)) (do (do (do s3 oi) o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do s1 oi) ol) o1) (do (do (do s2 oi) ol) o2)) (do (do (do (do s3 oi) ol) o1) o2)) = ()
    
(*One op*)
///////////////
let one_op_ind_right (l a b c:concrete_st) (o2 o2':op_t)
   : Lemma (requires eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2)) = ()
           
let one_op_ind_left (l a b c:concrete_st) (o1 o1':op_t)
   : Lemma (requires eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) = ()
           
let one_op_ind_lca (l:concrete_st) (ol o1:op_t)
  : Lemma (requires eq (merge l (do l o1) l) (do l o1) /\ fst ol < fst o1)
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do l ol)) (do (do l ol) o1)) = ()

let one_op_base (o1:op_t)
  : Lemma (ensures eq (merge init_st (do init_st o1) init_st) (do init_st o1)) = ()

let one_op_inter_base_right (l s1 s2 s3:concrete_st) (ob ol o1:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    eq (merge l s1 (do s2 o1)) (do s3 o1) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ol) o1)) (do (do s3 ol) o1) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do s1 ol) (do (do (do s2 ob) ol) o1)) (do (do (do s3 ob) ol) o1)) = ()

let one_op_inter_base_left (l s1 s2 s3:concrete_st) (ob ol o1:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    eq (merge l s1 (do s2 o1)) (do s3 o1) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ol) o1)) (do (do s3 ol) o1) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol) /\ //***EXTRA***
                    eq (merge l (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol) /\ //***EXTRA***
                    (Fst_then_snd? (rc ob o1) ==> eq (merge l (do s1 o1) (do s2 ob)) (do (merge l s1 (do s2 ob)) o1))) //***EXTRA*** 
          (ensures eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1)) = ()

let one_op_inter_right (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ob) ol) ) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 o) ob) ol) ) (do (do (do (do s3 o) ob) ol) o1)) = ()

let one_op_inter_left (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do (do s2 ol) o1)) (do (do (do (do s3 o) ob) ol) o1)) = ()

// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let one_op_inter_lca (l s1 s2 s3:concrete_st) (o1 ol oi:op_t)
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
let zero_op_inter_base_right (l s1 s2 s3:concrete_st) (ob ol:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    eq (merge l s1 s2) s3 /\
                    eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol)) = ()

let zero_op_inter_base_left (l s1 s2 s3:concrete_st) (ob ol:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    eq (merge l s1 s2) s3 /\
                    eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol) /\
                    eq (merge l (do s1 ob) (do s2 ol)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol)) = ()

let zero_op_inter_right (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do s1 ol) (do (do (do s2 o) ob) ol)) (do (do (do s3 o) ob) ol)) = ()

let zero_op_inter_left (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o_n,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do s2 ol)) (do (do (do s3 o) ob) ol)) = ()

// In general, the event "ol" below should be such that these exists o', (rc o' ol)
let zero_op_inter_lca_v1 (l s1 s2 s3:concrete_st) (ol:op_t)
  : Lemma (requires (exists o'. Fst_then_snd? (rc o' ol) \/ (Ts_order? (rc o' ol) /\ fst o' < fst ol)) /\ eq (merge l s1 s2) s3)
          (ensures eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol)) = ()

// In general, the events ol,o_n, below should be such that these exists o, (rc o ol)
let zero_op_inter_lca_v2 (l s1 s2 s3:concrete_st) (ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi) \/ (Ts_order? (rc o oi) /\ fst o < fst oi)) /\
                    eq (merge (do l oi) (do s1 oi) (do s2 oi)) (do s3 oi)  /\
                    eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol))
          (ensures eq (merge (do (do l oi) ol) (do (do s1 oi) ol) (do (do s2 oi) ol)) (do (do s3 oi) ol)) = ()

(* 2 op Comm  *)
///////////////////

let comm_ind_right (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o2' o1 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) /\
                    ~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()

let comm_ind_left (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o2' o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o2) ==> (eq (merge l (do a o2') (do b o2)) (do (merge l (do a o2') b) o2))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o2')) /\
                    ~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o2') o1) (do b o2)) (do (do (merge l (do a o2') b) o2) o1)) = ()

let comm_ind_lca (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()
          
let comm_inter_base_right (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    distinct_ops o1 o2 /\ Either? (rc o1 o2) /\
                    distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\ 
                    eq (merge l (do s1 o1) (do (do s2 ob) o2)) (do (do (merge l s1 (do s2 ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let comm_inter_base_left (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    distinct_ops o1 o2 /\ Either? (rc o1 o2) /\
                    distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\ 
                    eq (merge l (do (do s1 ob) o1) (do s2 o2)) (do (do (merge l (do s1 ob) s2) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let comm_inter_right (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\  
                    distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    distinct_ops o ol /\ //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()
          
let comm_inter_left (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\  
                    distinct_ops ob ol /\ (Fst_then_snd? (rc ob ol) \/ (Ts_order? (rc ob ol) /\ fst ob < fst ol)) /\ 
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    distinct_ops o ol /\ //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol) \/ (Ts_order? (rc o ol) /\ fst o < fst ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = ()

let comm_inter_lca (l s1 s2 s3:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    (exists o'. Fst_then_snd? (rc o' ol) \/ (Ts_order? (rc o' ol) /\ fst o' < fst ol)) /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2)) = ()

////////////////////////////////////////////////////////////////
////Equivalence of  MRDT & Sequential implementation  //////

// the concrete state 
let concrete_st_s = int

// init state 
let init_st_s = 0

// apply an operation to a state 
let do_s (st_s:concrete_st_s) (o:op_t) = 
  match snd (snd o) with
  |Inc -> st_s + 1
  |Dec -> st_s - 1

// equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  st_s = st

// initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()
         
////////////////////////////////////////////////////////////////
