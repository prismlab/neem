module Ctr_orset

open Json1
module S = Set_extended
module C = Ictr
module S = Orset
module L = Library

let lem_eqa o1 o2 = ()
let lem_eqb o1 o2 = ()
    
let no_rc_chain o1 o2 o3 = ()
let cond_comm_base s o1 o2 o3 = ()
let cond_comm_ind s o1 o2 o3 o l = ()

(*let base_2op' o1 o2 t = ()
let ind_lca_2op' l o1 o2 ol = ()
let inter_right_base_2op' l a b o1 o2 ob ol = ()
let inter_left_base_2op' l a b o1 o2 ob ol = ()
let inter_right_2op' l a b o1 o2 ob ol o = ()
let inter_left_2op' l a b o1 o2 ob ol o = ()
let ind_right_2op' l a b o1 o2 o2' = ()
let ind_left_2op' l a b o1 o2 o1' = ()*)
let ind_right_1op' l a b o2 o2' ol = ()        
let ind_left_1op' l a b o1 o1' ol = ()

#set-options "--z3rlimit 200 --ifuel 3"
instance ictr_orset : json C.st S.st C.app_op S.app_op = {
  Json1.init_sta = C.init_st;
  Json1.init_stb = S.init_st;
  Json1.eqa = C.eq;
  Json1.eqb = S.eq;
  Json1.rca = C.rc;
  Json1.rcb = S.rc;
  Json1.doa = C.do;
  Json1.dob = S.do;
  Json1.mergea = C.merge;
  Json1.mergeb = S.merge;

  Json1.lem_eqa;
  Json1.lem_eqb;
}


#set-options "--query_stats"
let rc_non_comm_help1 (o1 o2:(pos & (nat & S.app_op)))
  : Lemma (requires L.distinct_ops o1 o2)
          (ensures (S.Rem? (snd (snd o1)) /\ S.Add? (snd (snd o2)) /\ S.get_ele o1 = S.get_ele o2 ) ==> 
                           ~ (S.eq (S.do (S.do S.init_st o1) o2) (S.do (S.do S.init_st o2) o1))) = ()

let rc_non_comm_help2 (o1 o2:(pos & (nat & S.app_op)))
  : Lemma (requires L.distinct_ops o1 o2)
          (ensures (S.Add? (snd (snd o1)) /\ S.Rem? (snd (snd o2)) /\ S.get_ele o1 = S.get_ele o2 ) ==> 
                           ~ (S.eq (S.do (S.do S.init_st o1) o2) (S.do (S.do S.init_st o2) o1))) = ()

let rc_non_comm #sta #stb #oa #ob #m o1 o2 =
  if get_key o1 = get_key o2 && is_beta_op o1 && is_beta_op o2 then
    (admit();rc_non_comm_help1 (get_opb o1) (get_opb o2); 
     rc_non_comm_help2 (get_opb o1) (get_opb o2))
  else ()

instance ictr_orset_cond : cond C.st S.st C.app_op S.app_op ictr_orset = {
  Json1.rc_non_comm = admit();
  Json1.no_rc_chain;
  Json1.cond_comm_base;
  Json1.cond_comm_ind
}

#set-options "--z3rlimit 500 --ifuel 5"
instance ictr_orset_proof : vc C.st S.st C.app_op S.app_op ictr_orset = {
  Json1.merge_comm_a = C.merge_comm;
  Json1.merge_comm_b = S.merge_comm;
  Json1.merge_idem_a = C.merge_idem;
  Json1.merge_idem_b = S.merge_idem;
  Json1.base_2opa = C.base_2op;
  Json1.base_2opb = S.base_2op;
  Json1.ind_lca_2opa = C.ind_lca_2op;
  Json1.ind_lca_2opb = S.ind_lca_2op;
  Json1.inter_right_base_2opa = C.inter_right_base_2op;
  Json1.inter_right_base_2opb = S.inter_right_base_2op;
  Json1.inter_left_base_2opa = C.inter_left_base_2op;
  Json1.inter_left_base_2opb = S.inter_left_base_2op;
  Json1.inter_right_2opa = C.inter_right_2op;
  Json1.inter_right_2opb = S.inter_right_2op;
  Json1.inter_left_2opa = C.inter_left_2op;
  Json1.inter_left_2opb = S.inter_left_2op;
  Json1.ind_right_2opa = C.ind_right_2op;
  Json1.ind_right_2opb = S.ind_right_2op;
  Json1.ind_left_2opa = C.ind_left_2op;
  Json1.ind_left_2opb = S.ind_left_2op;
  Json1.base_1opa = C.base_1op;
  Json1.base_1opb = S.base_1op;
  Json1.ind_lca_1opa = C.ind_lca_1op;
  Json1.ind_lca_1opb = S.ind_lca_1op;
  Json1.inter_right_base_1opa = C.inter_right_base_1op;
  Json1.inter_right_base_1opb = admit();//S.inter_right_base_1op;
  Json1.inter_left_base_1opa = C.inter_left_base_1op;
  Json1.inter_left_base_1opb = S.inter_left_base_1op;
  Json1.inter_right_1opa = C.inter_right_1op;
  Json1.inter_right_1opb = S.inter_right_1op;
  Json1.inter_left_1opa = C.inter_left_1op;
  Json1.inter_left_1opb = S.inter_left_1op;
  Json1.ind_right_1opa = C.ind_right_1op;
  Json1.ind_right_1opb = S.ind_right_1op;
  Json1.ind_left_1opa = C.ind_left_1op;
  Json1.ind_left_1opb = S.ind_left_1op;
  Json1.lem_0opa = C.lem_0op;
  Json1.lem_0opb = S.lem_0op;
  
  (*Json1.base_2op';
  Json1.ind_lca_2op';
  Json1.inter_right_base_2op';
  Json1.inter_left_base_2op';
  Json1.inter_right_2op'; 
  Json1.inter_left_2op';*)
  Json1.ind_right_1op';
  Json1.ind_left_1op'
}
 
