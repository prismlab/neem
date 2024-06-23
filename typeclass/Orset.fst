module Orset

open Library
module S = Set_extended

type st = S.t (pos & nat)

type app_op = 
  |Add : nat -> app_op
  |Rem : nat -> app_op
  
let init_st = S.empty

let eq (a b:st) : Type0 = a == b

let rc o1 o2 = 
  match snd (snd o1), snd (snd o2) with
  |Add e1, Rem e2 -> if e1 = e2 then Snd_then_fst else Either
  |Rem e1, Add e2 -> if e1 = e2 then Fst_then_snd else Either
  |_ -> Either
  
let do (s:st) (o:op) = 
  match o with
  |(ts, (rid, Add e)) -> S.add (ts, e) s 
  |(_, (rid, Rem e)) -> S.filter s (fun ele -> snd ele <> e)
  
let merge l a b = 
  let da = S.difference a l in    //a - l
  let db = S.difference b l in    //b - l
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in   // intersect l a b
  S.union i_lab (S.union da db)          // (intersect l a b) U (a - l) U (b - l)

let get_ele (o:op) : nat =
  match snd (snd o) with
  |Add e -> e
  |Rem e -> e

#push-options "--z3rlimit 50 --max_ifuel 3"
let rc_non_comm (o1 o2:op)
  : Lemma (requires distinct_ops o1 o2)
          (ensures (((Add? (snd (snd o1)) /\ Rem? (snd (snd o2))) \/ (Rem? (snd (snd o1)) /\ Add? (snd (snd o2)))) /\ get_ele o1 = get_ele o2) ==> 
                           ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))) = ()

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
