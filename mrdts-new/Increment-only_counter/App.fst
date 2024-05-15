module App

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
type app_op_t:eqtype = unit //as the only operation is Inc

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st = s + 1

//conflict resolution
let rc (o1 o2:op_t) = Either

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  a + b - l
   
/////////////////////////////////////////////////////////////////////////////

let rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = ()
          
let no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3))) = ()

let cond_comm_base (s:concrete_st) (o1 o2 o3:op_t) 
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ distinct_ops o1 o3 /\
                    Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

let cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:seq op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3 /\ 
                    Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)) /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3)) = ()
  
/////////////////////////////////////////////////////////////////////////////
// Merge commutativity
let merge_comm (l a b:concrete_st)
   : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

// Merge idempotence
let merge_idem (s:concrete_st)
   : Lemma (ensures eq (merge s s s) s) = ()

(*Two OP RC*)
//////////////// 
let rc_ind_right (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let rc_ind_left (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

//Special case of rc_intermediate_v1
let rc_ind_lca (l:concrete_st) (o1 o2 o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()

let rc_base (o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let rc_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let rc_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()
          
let rc_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let rc_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let rc_inter_lca (l a b c:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) = ()

(*One op*)
///////////////
let one_op_ind_right (l a b c:concrete_st) (o2 o2':op_t)
   : Lemma (requires eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2)) = ()

let one_op_ind_left (l a b c:concrete_st) (o1 o1':op_t)
   : Lemma (requires eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) = ()
           
let one_op_ind_lca (l:concrete_st) (o2 o:op_t)
  : Lemma (requires eq (merge l l (do l o2)) (do l o2))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o2)) (do (do l o) o2)) = () 

let one_op_base (o2:op_t)
  : Lemma (ensures eq (merge init_st init_st (do init_st o2)) (do init_st o2)) = ()

let one_op_inter_base_right (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) = ()

let one_op_inter_base_left (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //***EXTRA***
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ //EXTRA!! 
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) = ()

let one_op_inter_right (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) = ()
          
let one_op_inter_left (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) = ()

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let one_op_inter_lca (l a b c:concrete_st) (o2 ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) = ()

(*Zero op *)
///////////////
// because we proved that e_i^l rcp eb is not possible.
//e_i^l vis eb is not possible
// so either eb rcp e_i^l or eb rct e_i^l is possible
let zero_op_inter_base_right (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) = () 

let zero_op_inter_base_left (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do b ol) ) (do (do c ob) ol)) = () 

let zero_op_inter_right (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol)) = ()

let zero_op_inter_left (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol)) = ()

// In general, the event "o" below should be such that these exists o', (rc o' o)
let zero_op_inter_lca_v1 (l a b c:concrete_st) (ol:op_t)
  : Lemma (requires (exists o'. Fst_then_snd? (rc o' ol)) /\ eq (merge l a b) c)
          (ensures eq (merge (do l ol) (do a ol) (do b ol)) (do c ol)) = ()

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let zero_op_inter_lca_v2 (l a b c:concrete_st) (ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\
                    eq (merge (do l oi) (do a oi) (do b oi)) (do c oi)  /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol)) = ()

(* 2 op Comm  *)
///////////////////

let comm_ind_right (l a b c:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) /\
                    ~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()

let comm_ind_left (l a b c:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o1' o2) ==> (eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o1')) /\
                    ~ (exists o3 b'. eq (do (do b o1') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (do (merge l (do a o1') b) o2) o1)) = ()

let comm_ind_lca (l:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (do (merge l a (do b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do (do a ob) o1) (do b o2)) (do (do (merge l (do a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let comm_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let comm_inter_lca (l a b c:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    (exists o'. Fst_then_snd? (rc o' ol)) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) = ()

////////////////////////////////////////////////////////////////
////Equivalence of  MRDT & Sequential implementation  //////

// the concrete state 
let concrete_st_s = int

// init state 
let init_st_s = 0

// apply an operation to a state 
let do_s (st_s:concrete_st_s) (_:op_t) = st_s + 1

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
