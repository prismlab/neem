module App_alpha_map

module S = Set_extended
module M = Map_extended

#set-options "--query_stats"

// concrete state of simpler MRDT (Grow-only set)
let concrete_st_v = S.t nat

// init state of gset
let init_st_v : concrete_st_v = S.empty

//operation type of gset
type app_op_v : eqtype =
  |Add : nat (*value*) -> app_op_v

let get_ele (_,(_,Add e)) = e

////do function of gset
let do_v (s:concrete_st_v) (o:op_v) =
  match o with
  |(_,(_,Add e)) -> S.add e s

//conflict resolution of gset
let rc_v (o1 o2:op_v) : rc_res = Either

//three-way merge of gset
let merge_v (l a b:concrete_st_v) : concrete_st_v =
  S.union l (S.union a b)

/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 100 --ifuel 3"
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

////////////////////////////////////////////////////////////////////////////

let merge_comm_v (l a b: concrete_st_v) 
  : Lemma (ensures eq_v (merge_v l a b) (merge_v l b a)) = ()
  
let merge_idem_v (s: concrete_st_v) 
  : Lemma (ensures eq_v (merge_v s s s) s) = ()

////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 100 --ifuel 3"
(*Two OP RC*)
//////////////// 
let rc_ind_right_v (l a b:concrete_st_v) (o1 o2 o2':op_v) 
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (merge_v l (do_v a o1) b) o2))
          (ensures eq_v (merge_v l (do_v a o1) (do_v (do_v b o2') o2)) (do_v (merge_v l (do_v a o1) (do_v b o2')) o2)) = ()

let rc_ind_left_v (l a b:concrete_st_v) (o1 o2 o1':op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\  
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (merge_v l (do_v a o1) b) o2))
          (ensures eq_v (merge_v l (do_v (do_v a o1') o1) (do_v b o2)) (do_v (merge_v l (do_v (do_v a o1') o1) b) o2)) = ()
          
let rc_ind_lca_v (l:concrete_st_v) (o1 o2 o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq_v (merge_v l (do_v l o1) (do_v l o2)) (do_v (do_v l o1) o2))
          (ensures eq_v (merge_v (do_v l o) (do_v (do_v l o) o1) (do_v (do_v l o) o2)) (do_v (do_v (do_v l o) o1) o2)) = ()

let rc_base (o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()
          
let rc_inter_base_right_v (l a b c:concrete_st_v) (o1 o2 ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2) /\
                    eq_v (merge_v l (do_v a ol) (do_v b ob)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2)) = ()

let rc_inter_base_right_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (get_key o2 = get_key ob /\ Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()
          
let rc_inter_base_left_v (l a b c:concrete_st_v) (o1 o2 ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2) /\
                    eq_v (merge_v l (do_v a ob) (do_v b ol)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))= ()

let rc_inter_base_left_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (get_key o1 = get_key ob /\ Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()
          
let rc_inter_right_v (l a b c:concrete_st_v) (o1 o2 ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    ((~ (commutes_with_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))
      (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v (do_v b o) ob) ol) o2)) (do_v (do_v (do_v (do_v (do_v c o) ob) ol) o1) o2)) = ()

let rc_inter_right_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (get_key o2 = get_key ob /\ Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()
      
let rc_inter_left_v (l a b c:concrete_st_v) (o1 o2 ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    ((~ (commutes_with_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))
      (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v (do_v a o) ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v (do_v c o) ob) ol) o1) o2)) = ()

let rc_inter_left_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (get_key o1 = get_key ob /\ Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2)) /\ Fst_then_snd? (rc_v (get_op_v ob) (get_op_v ol))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let rc_inter_lca_v (l a b c:concrete_st_v) (o1 o2 ol oi:op_v)
  : Lemma (requires Fst_then_snd? (rc_v o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    (exists o. Fst_then_snd? (rc_v o ol)) /\ 
                    (exists o. Fst_then_snd? (rc_v o oi)) /\
                    eq_v (merge_v (do_v l oi) (do_v (do_v a oi) o1) (do_v (do_v b oi) o2)) (do_v (do_v (do_v c oi) o1) o2) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2))
    (ensures eq_v (merge_v (do_v (do_v l oi) ol) (do_v (do_v (do_v a oi) ol) o1) (do_v (do_v (do_v b oi) ol) o2)) (do_v (do_v (do_v (do_v c oi) ol) o1) o2)) = ()

let rc_inter_lca_ne (l a b c:concrete_st) (o1 o2 ol oi:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    ~ (get_key o1 = get_key o2 /\ get_key o1 = get_key oi /\ get_key o1 = get_key ol /\ Fst_then_snd? (rc_v (get_op_v o1) (get_op_v o2))) /\
                    
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) = ()

(*One op*)
///////////////
let one_op_ind_right_v (l a b:concrete_st_v) (o2 o2':op_v) 
  : Lemma (requires distinct_ops o2 o2' /\ 
                    eq_v (merge_v l a (do_v b o2)) (do_v (merge_v l a b) o2))
           (ensures eq_v (merge_v l a (do_v (do_v b o2') o2)) (do_v (merge_v l a (do_v b o2')) o2)) = ()

let one_op_ind_left_v (l a b:concrete_st_v) (o1 o1':op_v) 
  : Lemma (requires distinct_ops o1 o1' /\ 
                    eq_v (merge_v l (do_v a o1) b) (do_v (merge_v l a b) o1))
           (ensures eq_v (merge_v l (do_v (do_v a o1') o1) b) (do_v (merge_v l (do_v a o1') b) o1)) = ()
          
let one_op_ind_lca_v (l:concrete_st_v) (o2 o:op_v) 
  : Lemma (requires distinct_ops o2 o /\ 
                    eq_v (merge_v l l (do_v l o2)) (do_v l o2))
          (ensures eq_v (merge_v (do_v l o) (do_v l o) (do_v (do_v l o) o2)) (do_v (do_v l o) o2)) = () 

let one_op_base (o2:op_t)
  : Lemma (ensures eq (merge init_st init_st (do init_st o2)) (do init_st o2)) = ()

let one_op_inter_base_right_v (l a b c:concrete_st_v) (o2 ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ol) o2)) (do_v (do_v c ol) o2) /\
                    eq_v (merge_v l a (do_v b o2)) (do_v c o2) /\
                    eq_v (merge_v l (do_v a ol) (do_v b ob)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v c ob) ol) o2)) = ()

let one_op_inter_base_right_ne (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (get_key o2 = get_key ob) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) = ()

let one_op_inter_base_left_v (l a b c:concrete_st_v) (o2 ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ol) o2)) (do_v (do_v c ol) o2) /\
                    (Fst_then_snd? (rc_v ob o2) ==> eq_v (merge_v l (do_v a o2) (do_v b ob)) (do_v (merge_v l a (do_v b ob)) o2)) /\ //***EXTRA***
                    eq_v (merge_v l a (do_v b o2)) (do_v c o2) /\
                    eq_v (merge_v l (do_v a ob) (do_v b o2)) (do_v (do_v c ob) o2) /\ //EXTRA!! 
                    eq_v (merge_v l (do_v a ob) (do_v b ol)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ob) ol) o2)) = ()

let one_op_inter_base_left_ne (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops ol o2 /\
                    ~ (get_key o2 = get_key ob) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //***EXTRA***
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ //EXTRA!! 
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) = ()
          
let one_op_inter_right_v (l a b c:concrete_st_v) (o2 ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol /\
                    ((~ (commutes_with_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v c ob) ol) o2))
      (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v (do_v (do_v b o) ob) ol) o2)) (do_v (do_v (do_v (do_v c o) ob) ol) o2)) = ()

let one_op_inter_right_ne (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    ~ (get_key o2 = get_key ob) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) = ()
          
let one_op_inter_left_v (l a b c:concrete_st_v) (o2 ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol /\
                    ((~ (commutes_with_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ob) ol) o2))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a o) ob) ol) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c o) ob) ol) o2)) = ()

let one_op_inter_left_ne (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    ~ (get_key o2 = get_key ob) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) = ()

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let one_op_inter_lca_v (l a b c:concrete_st_v) (o2 ol oi:op_v)
  : Lemma (requires distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\ 
                    (exists o. Fst_then_snd? (rc_v o ol)) /\ 
                    (exists o. Fst_then_snd? (rc_v o oi)) /\
                    eq_v (merge_v (do_v l oi) (do_v a oi) (do_v (do_v b oi) o2)) (do_v (do_v c oi) o2) /\
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ol) o2)) (do_v (do_v c ol) o2))
    (ensures eq_v (merge_v (do_v (do_v l oi) ol) (do_v (do_v a oi) ol) (do_v (do_v (do_v b oi) ol) o2)) (do_v (do_v (do_v c oi) ol) o2)) = ()

let  one_op_inter_lca_ne (l a b c:concrete_st) (o2 ol oi:op_t)
  : Lemma (requires distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\ 
                    ~ (get_key o2 = get_key oi /\ get_key o2 = get_key ol) /\
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) = ()

(*Zero op *)
///////////////
// because we proved that e_i^l rcp eb is not possible.
//e_i^l vis eb is not possible
// so either eb rcp e_i^l or eb rct e_i^l is possible
let zero_op_inter_base_right_v (l a b c:concrete_st_v) (ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v b ol)) (do_v c ol) /\
                    eq_v (merge_v l a b) c /\
                    eq_v (merge_v l (do_v a ol) (do_v b ob)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ob) ol)) (do_v (do_v c ob) ol)) = () 

let zero_op_inter_base_left_v (l a b c:concrete_st_v) (ob ol:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops ob ol /\ 
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v b ol)) (do_v c ol) /\
                    eq_v (merge_v l a b) c /\
                    eq_v (merge_v l (do_v a ob) (do_v b ol)) (do_v (do_v c ob) ol)) //***EXTRA***
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v b ol)) (do_v (do_v c ob) ol)) = ()

let zero_op_inter_right_v (l a b c:concrete_st_v) (ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ob) ol)) (do_v (do_v c ob) ol))
          (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v (do_v b o) ob) ol)) (do_v (do_v (do_v c o) ob) ol)) = ()
          
let zero_op_inter_left_v (l a b c:concrete_st_v) (ob ol o:op_v)
  : Lemma (requires Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v b ol)) (do_v (do_v c ob) ol))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a o) ob) ol) (do_v b ol)) (do_v (do_v (do_v c o) ob) ol)) = ()

// In general, the event "o" below should be such that these exists o', (rc o' o)
let zero_op_inter_lca_v1_v (l a b c:concrete_st_v) (ol:op_v)
  : Lemma (requires (exists o'. Fst_then_snd? (rc_v o' ol)) /\ eq_v (merge_v l a b) c)
          (ensures eq_v (merge_v (do_v l ol) (do_v a ol) (do_v b ol)) (do_v c ol)) = ()

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let zero_op_inter_lca_v2_v (l a b c:concrete_st_v) (ol oi:op_v)
  : Lemma (requires distinct_ops ol oi /\
                    (exists o. Fst_then_snd? (rc_v o ol)) /\ 
                    (exists o. Fst_then_snd? (rc_v o oi)) /\ 
                    eq_v (merge_v (do_v l oi) (do_v a oi) (do_v b oi)) (do_v c oi)  /\
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v b ol)) (do_v c ol))
          (ensures eq_v (merge_v (do_v (do_v l oi) ol) (do_v (do_v a oi) ol) (do_v (do_v b oi) ol)) (do_v (do_v c oi) ol)) = ()

let zero_op_inter_lca_v2_ne (l a b c:concrete_st) (ol oi:op_t)
  : Lemma (requires distinct_ops ol oi /\
                    ~ (get_key ol = get_key oi) /\
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\
                    eq (merge (do l oi) (do a oi) (do b oi)) (do c oi)  /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol)) = ()
          
(* 2 op Comm  *)
///////////////////
#set-options "--z3rlimit 100 --ifuel 3" 
let comm_ind_right_v (l a b:concrete_st_v) (o1 o2' o2:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\
                    (Fst_then_snd? (rc_v o2' o1) ==> (eq_v (merge_v l (do_v a o1) (do_v b o2')) (do_v (merge_v l a (do_v b o2')) o1))) /\
                    ~ (Fst_then_snd? (rc_v o1 o2')) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v (merge_v l a b) o2) o1))
          (ensures eq_v (merge_v l (do_v a o1) (do_v (do_v b o2') o2)) (do_v (do_v (merge_v l a (do_v b o2')) o2) o1))= ()

let comm_ind_right_ne (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o2') /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) /\
                    ~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()

let comm_ind_left_v (l a b:concrete_st_v) (o1 o2 o1':op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\
                    (Fst_then_snd? (rc_v o1' o2) ==> (eq_v (merge_v l (do_v a o1') (do_v b o2)) (do_v (merge_v l (do_v a o1') b) o2))) /\
                    ~ (Fst_then_snd? (rc_v o2 o1')) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v (merge_v l a b) o2) o1))
          (ensures eq_v (merge_v l (do_v (do_v a o1') o1) (do_v b o2)) (do_v (do_v (merge_v l (do_v a o1') b) o2) o1)) = ()

let comm_ind_left_ne (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o1') /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o1' o2) ==> (eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o1')) /\
                    ~ (exists o3 b'. eq (do (do b o1') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (do (merge l (do a o1') b) o2) o1)) = ()

let comm_ind_lca_v (l:concrete_st_v) (ol o1 o2:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\
                    eq_v (merge_v l (do_v l o1) (do_v l o2)) (do_v (do_v l o2) o1))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v l ol) o1) (do_v (do_v l ol) o2)) (do_v (do_v (do_v l ol) o2) o1)) = ()

let comm_ind_lca_ne (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                    ~ (get_key ol = get_key o1 /\ get_key ol = get_key o2) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_inter_base_right_v (l a b c:concrete_st_v) (o1 o2 ob ol:op_v) 
  : Lemma (requires Either? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2) /\ 
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2) /\
                    eq_v (merge_v l (do_v a o1) (do_v (do_v b ob) o2)) (do_v (do_v (merge_v l a (do_v b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq_v (merge_v (do_v l ol) (do_v a ol) (do_v (do_v b ob) ol)) (do_v (do_v c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2)) = ()

let comm_inter_base_right_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (get_key o2 = get_key o1 /\ get_key o1 = get_key ob) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (do (merge l a (do b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_base_left_v (l a b c:concrete_st_v) (o1 o2 ob ol:op_v) 
  : Lemma (requires Either? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2) /\ 
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2) /\
                    eq_v (merge_v l (do_v (do_v a ob) o1) (do_v b o2)) (do_v (do_v (merge_v l (do_v a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ob) ol) (do_v b ol)) (do_v (do_v c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2)) = ()

let comm_inter_base_left_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (get_key o2 = get_key o1 /\ get_key o1 = get_key ob) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do (do a ob) o1) (do b o2)) (do (do (merge l (do a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_right_v (l a b c:concrete_st_v) (o1 o2 ob ol o:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v b ob) ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v (do_v (do_v b o) ob) ol) o2)) (do_v (do_v (do_v (do_v (do_v c o) ob) ol) o1) o2)) = ()
          
let comm_inter_right_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key ob) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let comm_inter_left_v (l a b c:concrete_st_v) (o1 o2 ob ol o:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\ Fst_then_snd? (rc_v ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with_v o ob)) \/ Fst_then_snd? (rc_v o ol)) /\
                    eq_v (merge_v (do_v l ol) (do_v (do_v (do_v a ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v c ob) ol) o1) o2))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v (do_v (do_v a o) ob) ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v (do_v (do_v c o) ob) ol) o1) o2)) = ()
          
let comm_inter_left_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key ob) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let comm_inter_lca_v (l a b c:concrete_st_v) (o1 o2 ol:op_v)
  : Lemma (requires Either? (rc_v o1 o2) /\ distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    (exists o'. Fst_then_snd? (rc_v o' ol)) /\
                    eq_v (merge_v l (do_v a o1) (do_v b o2)) (do_v (do_v c o1) o2))
          (ensures eq_v (merge_v (do_v l ol) (do_v (do_v a ol) o1) (do_v (do_v b ol) o2)) (do_v (do_v (do_v c ol) o1) o2)) = ()

let comm_inter_lca_ne (l a b c:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    ~ ( get_key o2 = get_key o1 /\ get_key o1 = get_key ol) /\
                    (exists o'. Fst_then_snd? (rc o' ol)) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) = ()
