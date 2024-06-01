module Resettable_mrdt

module S = Set_extended
module M = Map_extended

#set-options "--query_stats"

let concrete_st_s = int

let init_st_s  = 0

type app_op_s : eqtype =
  |Inc

let do_s (s:concrete_st_s) (o:op_s) = s + 1

let rc_s (o1 o2:op_s) : rc_res = Either

let merge_s (l a b:concrete_st_s) : concrete_st_s =
  a + b - l

////////////////////////////////////////////////////////////////////////////
let rc_non_comm1 o1 o2 
  : Lemma (requires distinct_ops o1 o2)
          (ensures (Set? (snd (snd o1)) /\ Set? (snd (snd o2)) /\ fst o1 = fst o2) \/
                   (Set? (snd (snd o1)) /\ Reset? (snd (snd o2))) \/ (Set? (snd (snd o2)) /\ Reset? (snd (snd o1)))
                           ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))) = ()

let rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures commutes_with o1 o2 <==> Either? (rc o1 o2)) =
  rc_non_comm1 o1 o2

//////////////////////////////////////////////////////////////////////////

let merge_comm_s l a b = ()
let merge_idem_s s = ()

////////////////////////////////////////////////////////////////////////////
let rc_base o1 o2 = ()
let one_op_ind_lca l o2 o = ()
let one_op_base o2 = ()
let comm_ind_lca l ol o1 o2 = ()
let comm_base o1 o2 = ()
