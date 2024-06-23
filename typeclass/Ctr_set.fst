module Ctr_set

open Json1
module S = Set_extended
module C = Ictr
module S = Gset
module L = Library

let lem_eq_a o1 o2 = ()
let lem_eq_b o1 o2 = ()

let rc_non_comm o1 o2 = ()
let no_rc_chain o1 o2 o3 = ()
let cond_comm_base s o1 o2 o3 = ()
let cond_comm_ind s o1 o2 o3 o l = ()

let base_2op' o1 o2 t = ()

#set-options "--z3rlimit 100 --ifuel 3"
instance ictr_set : json C.st S.st C.app_op S.app_op = {
  Json1.init_st_a = C.init_st;
  Json1.init_st_b = S.init_st;
  Json1.eq_a = C.eq;
  Json1.eq_b = S.eq;
  Json1.lem_eq_a;
  Json1.lem_eq_b;
  Json1.rc_a = C.rc;
  Json1.rc_b = S.rc;
  Json1.do_a = C.do;
  Json1.do_b = S.do;
  Json1.merge_a = C.merge;
  Json1.merge_b = S.merge
}

instance ictr_set_cond : cond C.st S.st C.app_op S.app_op ictr_set = {
  Json1.rc_non_comm;
  Json1.no_rc_chain;
  Json1.cond_comm_base;
  Json1.cond_comm_ind
}

instance ictr_set_proof : vc C.st S.st C.app_op S.app_op ictr_set = {
  Json1.merge_comm_a = C.merge_comm;
  Json1.merge_comm_b = S.merge_comm;
  Json1.merge_idem_a = C.merge_idem;
  Json1.merge_idem_b = S.merge_idem;
  Json1.base_2op_a = C.base_2op;
  Json1.base_2op_b = S.base_2op;
  Json1.base_2op';
}
