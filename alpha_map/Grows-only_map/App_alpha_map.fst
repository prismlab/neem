module App_alpha_map

module S = Set_extended
module M = Map_extended

#set-options "--query_stats"

// concrete state of simpler MRDT (Grow-only set)
let concrete_st_s = S.t nat

// init state of gset
let init_st_s : concrete_st_s = S.empty

//operation type of gset
type app_op_s : eqtype =
  |Add : nat (*value*) -> app_op_s

let get_ele (_,(_,Add e)) = e

////do function of gset
let do_s (s:concrete_st_s) (o:op_s) =
  match o with
  |(_,(_,Add e)) -> S.add e s

//conflict resolution of gset
let rc_s (o1 o2:op_s) : rc_res = Either

//three-way merge of gset
let merge_s (l a b:concrete_st_s) : concrete_st_s =
  S.union l (S.union a b)

/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 100 --ifuel 3"
let rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = ()

let no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3))) = ()

let cond_comm_base (s:concrete_st) (o1 o2:op_t) (o3:op_t{distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3})
    : (b:bool{(Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3))) ==> eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)}) = true

let cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:seq op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3 /\ cond_comm_base s o1 o2 o3 /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3)) = admit() //can be done. increase rlimit??

////////////////////////////////////////////////////////////////////////////

let merge_comm (l a b:concrete_st)
  : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()
  
let merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s) = ()

////////////////////////////////////////////////////////////////////////////

let lemma_do (s:concrete_st) (o:op_t)
  : Lemma (ensures (forall k. k = get_key o ==> eq_s (sel (do s o) k) (do_s (sel s k) (get_op_s o)))) = ()

let lemma_merge (l a b:concrete_st)
  : Lemma (ensures (forall k. eq_s (sel (merge l a b) k) (merge_s (sel l k) (sel a k) (sel b k)))) = ()

////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 100 --ifuel 3"
(*Two OP RC*)
//////////////// 
let rc_ind_right_s (l a b:concrete_st_s) (o1 o2 o2':op_s)
  : Lemma (requires rc_s o1 o2 <> Either /\ distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\ 
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (merge_s l (do_s a o1) b) o2))
          (ensures eq_s (merge_s l (do_s a o1) (do_s (do_s b o2') o2)) (do_s (merge_s l (do_s a o1) (do_s b o2')) o2)) = ()

let rc_ind_right_ne (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o2') /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()
          
let rc_ind_left_s (l a b:concrete_st_s) (o1 o2 o1':op_s)
  : Lemma (requires rc_s o1 o2 <> Either /\ distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\  
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (merge_s l (do_s a o1) b) o2))
          (ensures eq_s (merge_s l (do_s (do_s a o1') o1) (do_s b o2)) (do_s (merge_s l (do_s (do_s a o1') o1) b) o2)) = ()

let rc_ind_left_ne (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\  
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o1') /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

let rc_ind_lca_s (l:concrete_st_s) (o1 o2 o:op_s)
  : Lemma (requires rc_s o1 o2 <> Either /\ distinct_ops o1 o2 /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq_s (merge_s l (do_s l o1) (do_s l o2)) (do_s (do_s l o1) o2))
          (ensures eq_s (merge_s (do_s l o) (do_s (do_s l o) o1) (do_s (do_s l o) o2)) (do_s (do_s (do_s l o) o1) o2)) = ()

let rc_ind_lca_ne (l:concrete_st) (o1 o2 o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o /\ distinct_ops o o2 /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()

let rc_base (o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()
          
let rc_inter_base_right_s (l a b c:concrete_st_s) (o1 o2 ob ol:op_s)
  : Lemma (requires rc_s o1 o2 <> Either /\ rc_s ob ol <> Either /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s c ol) o1) o2) /\
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s c o1) o2) /\
                    eq_s (merge_s l (do_s a ol) (do_s b ob)) (do_s (do_s c ob) ol)) //***EXTRA***
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s (do_s b ob) ol) o2)) (do_s (do_s (do_s (do_s c ob) ol) o1) o2)) = ()

let rc_inter_base_right_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key ob) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()
          
let rc_inter_base_left_s (l a b c:concrete_st_s) (o1 o2 ob ol:op_s)
  : Lemma (requires rc_s o1 o2 <> Either /\ rc_s ob ol <> Either /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s c ol) o1) o2) /\
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s c o1) o2) /\
                    eq_s (merge_s l (do_s a ob) (do_s b ol)) (do_s (do_s c ob) ol)) //***EXTRA***
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s (do_s a ob) ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s (do_s c ob) ol) o1) o2)) = ()

let rc_inter_base_left_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key ob) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()
          
let rc_inter_right_s (l a b c:concrete_st_s) (o1 o2 ob ol o:op_s)
  : Lemma (requires rc_s o1 o2 <> Either /\ rc_s ob ol <> Either /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\

                    eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s (do_s b ob) ol) o2)) (do_s (do_s (do_s (do_s c ob) ol) o1) o2))
      (ensures eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s (do_s (do_s b o) ob) ol) o2)) (do_s (do_s (do_s (do_s (do_s c o) ob) ol) o1) o2)) = ()

let rc_inter_right_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key ob) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()
      
let rc_inter_left_s (l a b c:concrete_st_s) (o1 o2 ob ol o:op_s)
  : Lemma (requires rc_s o1 o2 <> Either /\ rc_s ob ol <> Either /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\

                    eq_s (merge_s (do_s l ol) (do_s (do_s (do_s a ob) ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s (do_s c ob) ol) o1) o2))
      (ensures eq_s (merge_s (do_s l ol) (do_s (do_s (do_s (do_s a o) ob) ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s (do_s (do_s c o) ob) ol) o1) o2)) = ()

let rc_inter_left_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key ob) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let rc_inter_lca_s (l a b c:concrete_st_s) (o1 o2 ol oi:op_s)
  : Lemma (requires rc_s o1 o2 <> Either /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    (exists o. rc_s o ol <> Either) /\ 
                    (exists o. rc_s o oi <> Either) /\
                    eq_s (merge_s (do_s l oi) (do_s (do_s a oi) o1) (do_s (do_s b oi) o2)) (do_s (do_s (do_s c oi) o1) o2) /\
                    eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s c ol) o1) o2))
    (ensures eq_s (merge_s (do_s (do_s l oi) ol) (do_s (do_s (do_s a oi) ol) o1) (do_s (do_s (do_s b oi) ol) o2)) (do_s (do_s (do_s (do_s c oi) ol) o1) o2)) = ()

let rc_inter_lca_ne (l a b c:concrete_st) (o1 o2 ol oi:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    ~ (get_key o1 = get_key o2 /\ get_key o1 = get_key oi /\ get_key o1 = get_key ol) /\
                    
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) = ()

(*One op*)
///////////////
let one_op_ind_right_s (l a b:concrete_st_s) (o2 o2':op_s) 
  : Lemma (requires distinct_ops o2 o2' /\ 
                    eq_s (merge_s l a (do_s b o2)) (do_s (merge_s l a b) o2))
           (ensures eq_s (merge_s l a (do_s (do_s b o2') o2)) (do_s (merge_s l a (do_s b o2')) o2)) = ()

let one_op_ind_right_ne (l a b:concrete_st) (o2 o2':op_t)
  : Lemma (requires distinct_ops o2 o2' /\ 
                    ~ (get_key o2 = get_key o2') /\
                    eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2)) = ()

let one_op_ind_left_s (l a b:concrete_st_s) (o1 o1':op_s) 
  : Lemma (requires distinct_ops o1 o1' /\ 
                    eq_s (merge_s l (do_s a o1) b) (do_s (merge_s l a b) o1))
           (ensures eq_s (merge_s l (do_s (do_s a o1') o1) b) (do_s (merge_s l (do_s a o1') b) o1)) = ()

let one_op_ind_left_ne (l a b:concrete_st) (o1 o1':op_t)
   : Lemma (requires distinct_ops o1 o1' /\ 
                     ~ (get_key o1 = get_key o1') /\
                    eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) = ()
           
let one_op_ind_lca_s (l:concrete_st_s) (o2 o:op_s) 
  : Lemma (requires distinct_ops o2 o /\ 
                    eq_s (merge_s l l (do_s l o2)) (do_s l o2))
          (ensures eq_s (merge_s (do_s l o) (do_s l o) (do_s (do_s l o) o2)) (do_s (do_s l o) o2)) = () 

let one_op_ind_lca_ne (l:concrete_st) (o2 o:op_t)
   : Lemma (requires distinct_ops o2 o /\ 
                     ~ (get_key o2 = get_key o) /\
                     eq (merge l l (do l o2)) (do l o2))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o2)) (do (do l o) o2)) = ()

let one_op_base (o2:op_t)
  : Lemma (ensures eq (merge init_st init_st (do init_st o2)) (do init_st o2)) = ()

let one_op_inter_base_right_s (l a b c:concrete_st_s) (o2 ob ol:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ 
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s b ol) o2)) (do_s (do_s c ol) o2) /\
                    eq_s (merge_s l a (do_s b o2)) (do_s c o2) /\
                    eq_s (merge_s l (do_s a ol) (do_s b ob)) (do_s (do_s c ob) ol)) //***EXTRA***
          (ensures eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s (do_s b ob) ol) o2)) (do_s (do_s (do_s c ob) ol) o2)) = ()

let one_op_inter_base_right_ne (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (get_key o2 = get_key ob) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) = ()

let one_op_inter_base_left_s (l a b c:concrete_st_s) (o2 ob ol:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ 
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s b ol) o2)) (do_s (do_s c ol) o2) /\
                    eq_s (merge_s l a (do_s b o2)) (do_s c o2) /\
                    eq_s (merge_s l (do_s a ol) (do_s b ob)) (do_s (do_s c ob) ol) /\ //***EXTRA***
                    eq_s (merge_s l (do_s (do_s a ob) ol) (do_s b ol)) (do_s (do_s c ob) ol)) //***EXTRA***
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s a ob) ol) (do_s (do_s b ol) o2)) (do_s (do_s (do_s c ob) ol) o2)) = ()

let one_op_inter_base_left_ne (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (get_key o2 = get_key ob) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //***EXTRA***
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol) /\ //***EXTRA***
                    eq (merge l (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) = ()
          
let one_op_inter_right_s (l a b c:concrete_st_s) (o2 ob ol o:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ 
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol /\
                    eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s (do_s b ob) ol) o2)) (do_s (do_s (do_s c ob) ol) o2))
      (ensures eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s (do_s (do_s b o) ob) ol) o2)) (do_s (do_s (do_s (do_s c o) ob) ol) o2)) = ()

let one_op_inter_right_ne (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) = ()
          
let one_op_inter_left_s (l a b c:concrete_st_s) (o2 ob ol o:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ 
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o o2 /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol /\
                    eq_s (merge_s (do_s l ol) (do_s (do_s a ob) ol) (do_s (do_s b ol) o2)) (do_s (do_s (do_s c ob) ol) o2))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s (do_s a o) ob) ol) (do_s (do_s b ol) o2)) (do_s (do_s (do_s (do_s c o) ob) ol) o2)) = ()

let one_op_inter_left_ne (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    ~ (get_key o2 = get_key ob) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) = ()

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let one_op_inter_lca_s (l a b c:concrete_st_s) (o2 ol oi:op_s)
  : Lemma (requires distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\ 
                    (exists o. rc_s o ol <> Either) /\ 
                    (exists o. rc_s o oi <> Either) /\
                    eq_s (merge_s (do_s l oi) (do_s a oi) (do_s (do_s b oi) o2)) (do_s (do_s c oi) o2) /\
                    eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s b ol) o2)) (do_s (do_s c ol) o2))
    (ensures eq_s (merge_s (do_s (do_s l oi) ol) (do_s (do_s a oi) ol) (do_s (do_s (do_s b oi) ol) o2)) (do_s (do_s (do_s c oi) ol) o2)) = ()

let one_op_inter_lca_ne (l a b c:concrete_st) (o2 ol oi:op_t)
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
let zero_op_inter_base_right_s (l a b c:concrete_st_s) (ob ol:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ distinct_ops ob ol /\ 
                    eq_s (merge_s (do_s l ol) (do_s a ol) (do_s b ol)) (do_s c ol) /\
                    eq_s (merge_s l a b) c /\
                    eq_s (merge_s l (do_s a ol) (do_s b ob)) (do_s (do_s c ob) ol)) //***EXTRA***
          (ensures eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s b ob) ol)) (do_s (do_s c ob) ol)) = () 

let zero_op_inter_base_left_s (l a b c:concrete_st_s) (ob ol:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ distinct_ops ob ol /\ 
                    eq_s (merge_s (do_s l ol) (do_s a ol) (do_s b ol)) (do_s c ol) /\
                    eq_s (merge_s l a b) c /\
                    eq_s (merge_s l (do_s a ob) (do_s b ol)) (do_s (do_s c ob) ol)) //***EXTRA***
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s a ob) ol) (do_s b ol)) (do_s (do_s c ob) ol)) = () 

let zero_op_inter_right_s (l a b c:concrete_st_s) (ob ol o:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s b ob) ol)) (do_s (do_s c ob) ol))
          (ensures eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s (do_s b o) ob) ol)) (do_s (do_s (do_s c o) ob) ol)) = ()

let zero_op_inter_left_s (l a b c:concrete_st_s) (ob ol o:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    eq_s (merge_s (do_s l ol) (do_s (do_s a ob) ol) (do_s b ol)) (do_s (do_s c ob) ol))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s (do_s a o) ob) ol) (do_s b ol)) (do_s (do_s (do_s c o) ob) ol)) = ()

// In general, the event "o" below should be such that these exists o', (rc o' o)
let zero_op_inter_lca_v1_s (l a b c:concrete_st_s) (ol:op_s)
  : Lemma (requires (exists o'. rc_s o' ol <> Either) /\ eq_s (merge_s l a b) c)
          (ensures eq_s (merge_s (do_s l ol) (do_s a ol) (do_s b ol)) (do_s c ol)) = ()

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let zero_op_inter_lca_v2_s (l a b c:concrete_st_s) (ol oi:op_s)
  : Lemma (requires distinct_ops ol oi /\
                    (exists o. rc_s o ol <> Either) /\ 
                    (exists o. rc_s o oi <> Either) /\ 
                    eq_s (merge_s (do_s l oi) (do_s a oi) (do_s b oi)) (do_s c oi)  /\
                    eq_s (merge_s (do_s l ol) (do_s a ol) (do_s b ol)) (do_s c ol))
          (ensures eq_s (merge_s (do_s (do_s l oi) ol) (do_s (do_s a oi) ol) (do_s (do_s b oi) ol)) (do_s (do_s c oi) ol)) = ()

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
let comm_ind_right_s (l a b:concrete_st_s) (o1 o2' o2:op_s)
  : Lemma (requires eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s (merge_s l a b) o2) o1))
          (ensures eq_s (merge_s l (do_s a o1) (do_s (do_s b o2') o2)) (do_s (do_s (merge_s l a (do_s b o2')) o2) o1)) = ()

let comm_ind_right_ne (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                     ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o2') /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()

let comm_ind_left_s (l a b:concrete_st_s) (o1 o2' o2:op_s)
  : Lemma (requires eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s (merge_s l a b) o2) o1))
          (ensures eq_s (merge_s l (do_s (do_s a o2') o1) (do_s b o2)) (do_s (do_s (merge_s l (do_s a o2') b) o2) o1)) = ()

let comm_ind_left_ne (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o2') /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1))                    
          (ensures eq (merge l (do (do a o2') o1) (do b o2)) (do (do (merge l (do a o2') b) o2) o1)) = ()

let comm_ind_lca_s (l:concrete_st_s) (ol o1 o2:op_s)
  : Lemma (requires eq_s (merge_s l (do_s l o1) (do_s l o2)) (do_s (do_s l o2) o1))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s l ol) o1) (do_s (do_s l ol) o2)) (do_s (do_s (do_s l ol) o2) o1)) = ()

let comm_ind_lca_ne (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                    ~ (get_key ol = get_key o1 /\ get_key ol = get_key o2) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_inter_base_right_s (l a b c:concrete_st_s) (o1 o2 ob ol:op_s) 
  : Lemma (requires rc_s ob ol <> Either /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s c ol) o1) o2) /\ 
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s c o1) o2) /\
                    eq_s (merge_s l (do_s a o1) (do_s (do_s b ob) o2)) (do_s (do_s (merge_s l a (do_s b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq_s (merge_s (do_s l ol) (do_s a ol) (do_s (do_s b ob) ol)) (do_s (do_s c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s (do_s b ob) ol) o2)) (do_s (do_s (do_s (do_s c ob) ol) o1) o2)) = ()

let comm_inter_base_right_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (get_key o2 = get_key o1 /\ get_key o1 = get_key ob) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (do (merge l a (do b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_base_left_s (l a b c:concrete_st_s) (o1 o2 ob ol:op_s) 
  : Lemma (requires rc_s ob ol <> Either /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s c ol) o1) o2) /\ 
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s c o1) o2) /\
                    eq_s (merge_s l (do_s (do_s a ob) o1) (do_s b o2)) (do_s (do_s (merge_s l (do_s a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq_s (merge_s (do_s l ol) (do_s (do_s a ob) ol) (do_s b ol)) (do_s (do_s c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s (do_s a ob) ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s (do_s c ob) ol) o1) o2)) = ()

let comm_inter_base_left_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (get_key o2 = get_key o1 /\ get_key o1 = get_key ob) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do (do a ob) o1) (do b o2)) (do (do (merge l (do a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_right_s (l a b c:concrete_st_s) (o1 o2 ob ol o:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s (do_s b ob) ol) o2)) (do_s (do_s (do_s (do_s c ob) ol) o1) o2))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s (do_s (do_s b o) ob) ol) o2)) (do_s (do_s (do_s (do_s (do_s c o) ob) ol) o1) o2)) = ()
          
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

let comm_inter_left_s (l a b c:concrete_st_s) (o1 o2 ob ol o:op_s)
  : Lemma (requires rc_s ob ol <> Either /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    eq_s (merge_s (do_s l ol) (do_s (do_s (do_s a ob) ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s (do_s c ob) ol) o1) o2))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s (do_s (do_s a o) ob) ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s (do_s (do_s c o) ob) ol) o1) o2)) = ()
          
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

let comm_inter_lca_s (l a b c:concrete_st_s) (o1 o2 ol:op_s)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    (exists o'. rc_s o' ol <> Either) /\
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s c o1) o2))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s a ol) o1) (do_s (do_s b ol) o2)) (do_s (do_s (do_s c ol) o1) o2)) = ()

let comm_inter_lca_ne (l a b c:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    ~ ( get_key o2 = get_key o1 /\ get_key o1 = get_key ol) /\
                    (exists o'. Fst_then_snd? (rc o' ol)) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) = ()
