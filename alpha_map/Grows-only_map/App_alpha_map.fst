module App_alpha_map

module S = Set_extended
module M = Map_extended

#set-options "--query_stats"

// concrete state of simpler MRDT (Grow-only set)
let concrete_st_s = S.t nat

// init state of gset
let init_st_s : concrete_st_s = S.empty

//operation type of gset
type op_s : eqtype =
  |Add : nat (*value*) -> op_s

let get_ele (_,(_,Add e)) = e

////do function of gset
let do_s (s:concrete_st_s) (o:(nat & (nat & op_s))) =
  match o with
  |(_,(_,Add e)) -> S.add e s

//conflict resolution of gset
let rc_s (o1 o2:(nat & (nat & op_s))) : rc_res = Either

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

(*Two OP COMM*)
#set-options "--z3rlimit 100 --ifuel 3"
let comm_ind_right_s (l a b:concrete_st_s) (o1 o2' o2:(nat & (nat & op_s)))
  : Lemma (requires Either? (rc_s o1 o2) /\
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s (merge_s l a b) o2) o1))
          (ensures eq_s (merge_s l (do_s a o1) (do_s (do_s b o2') o2)) (do_s (do_s (merge_s l a (do_s b o2')) o2) o1)) = ()

let comm_ind_right_ne (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Either? (rc_s (get_op_s o1) (get_op_s o2)) /\
                     ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o2') /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()

let comm_ind_left_s (l a b:concrete_st_s) (o1 o2' o2:(nat & (nat & op_s)))
  : Lemma (requires Either? (rc_s o1 o2) /\
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s (merge_s l a b) o2) o1))
          (ensures eq_s (merge_s l (do_s (do_s a o2') o1) (do_s b o2)) (do_s (do_s (merge_s l (do_s a o2') b) o2) o1)) = ()

let comm_ind_left_ne (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Either? (rc_s (get_op_s o1) (get_op_s o2)) /\
                    ~ (get_key o1 = get_key o2 /\ get_key o2 = get_key o2') /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1))                    
          (ensures eq (merge l (do (do a o2') o1) (do b o2)) (do (do (merge l (do a o2') b) o2) o1)) = ()

let comm_ind_lca_s (l:concrete_st_s) (ol o1 o2:(nat & (nat & op_s)))
  : Lemma (requires Either? (rc_s o1 o2) /\
                    eq_s (merge_s l (do_s l o1) (do_s l o2)) (do_s (do_s l o2) o1))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s l ol) o1) (do_s (do_s l ol) o2)) (do_s (do_s (do_s l ol) o2) o1)) = ()

let comm_ind_lca_ne (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Either? (rc_s (get_op_s o1) (get_op_s o2)) /\
                    ~ (get_key ol = get_key o1 /\ get_key ol = get_key o2) /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()


