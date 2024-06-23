module Ictr

open Library

type st = int
type app_op = 
  |Inc
let init_st = 0
let eq (a b:st) : Type0 = a = b
let rc o1 o2 = Either
let do s o = s + 1
let merge l a b = a + b - l

let rc_non_comm o1 o2 = ()
let no_rc_chain o1 o2 o3 = ()
let cond_comm_base s o1 o2 o3 = ()
let cond_comm_ind s o1 o2 o3 o l = ()

let merge_comm l a b = ()
let merge_idem s = ()
let base_2op o1 o2 = ()
let ind_lca_2op l o1 o2 ol = ()
let inter_right_base_2op l a b o1 o2 ob ol = ()    
let inter_left_base_2op l a b o1 o2 ob ol = ()
let inter_right_2op l a b o1 o2 ob ol o = ()
let inter_left_2op l a b o1 o2 ob ol o = ()
let ind_right_2op l a b o1 o2 o2' = ()
let ind_left_2op l a b o1 o2 o1' = ()
let base_1op o1 = ()
let ind_lca_1op l o1 ol = ()
let inter_right_base_1op l a b o1 ob ol = ()
let inter_left_base_1op l a b o1 ob ol = ()
let inter_right_1op l a b o1 ob ol o = ()
let inter_left_1op l a b o1 ob ol o = ()
let ind_left_1op l a b o1 o1' ol = ()
let ind_right_1op l a b o2 o2' ol = ()
let lem_0op l a b ol = ()

instance ictr : mrdt st app_op = {
  Library.init_st;
  Library.eq;
  Library.rc;
  Library.do;
  Library.merge
}

instance ictr_cond : cond st app_op ictr = {
  Library.rc_non_comm;
  Library.no_rc_chain;
  Library.cond_comm_base;
  Library.cond_comm_ind
}

instance ictr_proof : vc st app_op ictr = {
  Library.merge_comm;
  Library.merge_idem;
  Library.base_2op;
  Library.ind_lca_2op;
  Library.inter_right_base_2op;
  Library.inter_left_base_2op;
  Library.inter_right_2op;
  Library.inter_left_2op;
  Library.ind_right_2op;
  Library.ind_left_2op;
  Library.base_1op;
  Library.ind_lca_1op;
  Library.inter_right_base_1op;
  Library.inter_left_base_1op;
  Library.inter_right_1op;
  Library.inter_left_1op;
  Library.ind_left_1op;
  Library.ind_right_1op;
  Library.lem_0op 
}
