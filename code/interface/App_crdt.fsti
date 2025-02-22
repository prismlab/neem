module App_crdt

open FStar.Seq

// the concrete state type
val concrete_st : Type0

// init state
val init_st : concrete_st

// equivalence between 2 concrete states
val eq (a b:concrete_st) : Type0

val symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a)

val transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c)

val eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b)

// operation type
[@@ must_erase_for_extraction]
val app_op_t : eqtype 

type op_t = pos (*timestamp*) & (nat (*replica ID*) & app_op_t)

let get_rid (_,(rid,_)) = rid

let distinct_ops (op1 op2:op_t) = fst op1 =!= fst op2

type log = seq op_t

// apply an operation to a state
val do (s:concrete_st) (o:op_t) : concrete_st

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

//conflict resolution
val rc (o1 o2:op_t) : rc_res

// concrete merge operation
val merge (a b:concrete_st) : concrete_st

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
                  
/////////////////////////////////// Verification Conditions //////////////////////////////////////////

val merge_comm (a b:concrete_st)
  : Lemma (ensures (eq (merge a b) (merge b a)))
                       
val merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s) s)

(*Two OP*)
//////////////// 
val base_2op (o1 o2:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2)
          (ensures eq (merge (do init_st o1) (do init_st o2)) (do (merge init_st (do init_st o2)) o1))

val ind_lca_2op (l:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    eq (merge (do l o1) (do l o2)) (do (merge l (do l o2)) o1))
          (ensures eq (merge (do (do l ol) o1) (do (do l ol) o2)) (do (merge (do l ol) (do (do l ol) o2)) o1))

val inter_right_base_2op (a b :concrete_st) (o1 o2 ob ol:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do a o1) (do b o2)) (do (merge a (do b o2)) o1) /\ //from pre-cond of ind_right_2op
                    eq (merge (do a o1) (do (do b ob) o2)) (do (merge a (do (do b ob) o2)) o1) /\ //from ind_right_2op
                    eq (merge (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do a ol) (do (do b ol) o2)) o1))
          (ensures eq (merge (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (merge (do a ol) (do (do (do b ob) ol) o2)) o1))

val inter_left_base_2op (a b:concrete_st) (o1 o2 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc o2 o1) /\ Fst_then_snd? (rc ob ol) /\ get_rid o2 <> get_rid o1 /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do a ol) (do (do b ol) o2)) o1))
          (ensures eq (merge (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (merge (do (do a ob) ol) (do (do b ol) o2)) o1))
          
val inter_right_2op (a b:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (merge (do a ol) (do (do (do b ob) ol) o2)) o1))
          (ensures eq (merge (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (merge (do a ol) (do (do (do (do b o) ob) ol) o2)) o1))

val inter_left_2op (a b:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc o2 o1) /\ Fst_then_snd? (rc ob ol) /\ get_rid o2 <> get_rid o1 /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (merge (do (do a ob) ol) (do (do b ol) o2)) o1))
          (ensures eq (merge (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (merge (do (do (do a o) ob) ol) (do (do b ol) o2)) o1))

val inter_lca_2op (a b:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    eq (merge (do (do a ol) o1) (do b ol)) (do (merge (do a ol) (do b ol)) o1) /\ //1op
                    eq (merge (do a o1) (do b o2)) (do (merge a (do b o2)) o1))
          (ensures eq (merge (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do a ol) (do (do b ol) o2)) o1))

val ind_right_2op (a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    eq (merge (do a o1) (do b o2)) (do (merge a (do b o2)) o1))
          (ensures eq (merge (do a o1) (do (do b o2') o2)) (do (merge a (do (do b o2') o2)) o1))
          
val ind_left_2op (a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge (do a o1) (do b o2)) (do (merge a (do b o2)) o1))
          (ensures eq (merge (do (do a o1') o1) (do b o2)) (do (merge (do a o1') (do b o2)) o1))

(*One OP*)
//////////////// 
val base_1op (o1:op_t)
  : Lemma (ensures eq (merge (do init_st o1) init_st) (do (merge init_st init_st) o1))

val ind_lca_1op (l:concrete_st) (o1 ol:op_t)
  : Lemma (requires distinct_ops o1 ol /\
                    eq (merge (do l o1) l) (do (merge l l) o1))
          (ensures eq (merge (do (do l ol) o1) (do l ol)) (do (merge (do l ol) (do l ol)) o1))

val inter_right_base_1op (a b :concrete_st) (o1 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    (Fst_then_snd? (rc ob o1) ==> eq (merge (do a o1) (do b ob)) (do (merge a (do b ob)) o1)) /\ //from app.fsti
                    eq (merge (do (do a ol) o1) (do b ol)) (do (merge (do a ol) (do b ol)) o1))
          (ensures eq (merge (do (do a ol) o1) (do (do b ob) ol)) (do (merge (do a ol) (do (do b ob) ol)) o1))

val inter_left_base_1op (a b:concrete_st) (o1 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    eq (merge (do (do a ol) o1) (do b ol)) (do (merge (do a ol) (do b ol)) o1))
          (ensures eq (merge (do (do (do a ob) ol) o1) (do b ol)) (do (merge (do (do a ob) ol) (do b ol)) o1))
          
val inter_right_1op (a b:concrete_st) (o1 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do (do a ol) o1) (do (do b ob) ol)) (do (merge (do a ol) (do (do b ob) ol)) o1))
          (ensures eq (merge (do (do a ol) o1) (do (do (do b o) ob) ol)) (do (merge (do a ol) (do (do (do b o) ob) ol)) o1))

val inter_left_1op (a b:concrete_st) (o1 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do (do (do a ob) ol) o1) (do b ol)) (do (merge (do (do a ob) ol) (do b ol)) o1))
          (ensures eq (merge (do (do (do (do a o) ob) ol) o1) (do b ol)) (do (merge (do (do (do a o) ob) ol) (do b ol)) o1))

val inter_lca_1op (a b:concrete_st) (o1 ol oi:op_t)
  : Lemma (requires distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops ol oi /\
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do (do a oi) o1) (do b oi)) (do (merge (do a oi) (do b oi)) o1) /\
                    eq (merge (do (do a ol) o1) (do b ol)) (do (merge (do a ol) (do b ol)) o1))
          (ensures eq (merge (do (do (do a oi) ol) o1) (do (do b oi) ol)) 
                      (do (merge (do (do a oi) ol) (do (do b oi) ol)) o1))

val ind_left_1op (a b:concrete_st) (o1 o1' ol:op_t)
  : Lemma (requires distinct_ops o1 o1' /\ distinct_ops o1 ol /\ distinct_ops o1' ol /\
                    eq (merge (do a o1) (do b ol)) (do (merge a (do b ol)) o1))
          (ensures eq (merge (do (do a o1') o1) (do b ol)) (do (merge (do a o1') (do b ol)) o1))
          
val ind_right_1op (a b:concrete_st) (o2 o2' ol:op_t)
  : Lemma (requires distinct_ops o2 o2' /\ distinct_ops o2 ol /\ distinct_ops o2' ol /\
                    eq (merge (do a ol) (do b o2)) (do (merge (do a ol) b) o2))
          (ensures eq (merge (do a ol) (do (do b o2') o2)) (do (merge (do a ol) (do b o2')) o2))
          
(*Zero OP*)
(* All BottomUp-0-OP VCs are combined into a single VC *)
////////////////  
  
val lem_0op (a b:concrete_st) (ol:op_t)
  : Lemma (ensures eq (merge (do a ol) (do b ol)) (do (merge a b) ol))
