module Json3

module S = Set_extended

let concrete_st_a = int

let concrete_st_b = S.t (pos & nat)

let concrete_st_c = S.t (nat & (nat & nat)) & S.t nat

let init_st_a = 0

let init_st_b = S.empty

let init_st_c = (S.empty, S.empty)

let eq_a a b = a = b

let eq_b a b = a == b

let eq_c a b = 
  S.equal (fst a) (fst b) /\ 
  S.equal (snd a) (snd b)

let lem_eq_a a b = ()

let lem_eq_b a b = ()

let lem_eq_c a b = ()

type app_op_a : eqtype =
  |Inc

type app_op_b : eqtype =
  |Add : nat -> app_op_b
  |Rem : nat -> app_op_b

type app_op_c : eqtype =
  |Add_after : after_id:nat -> ele:nat -> app_op_c //inserts ele after after_id
  |Remove : id:pos -> app_op_c //removes the element with identifier id
  
let do_a s o = s + 1

let do_b s o = 
  match o with
  |(ts, (rid, Add e)) -> S.add (ts, e) s 
  |(_, (rid, Rem e)) -> S.filter s (fun ele -> snd ele <> e)

let do_c s o =
  match o with
  |(ts, (_, Add_after after_id ele)) -> (S.add (ts, (after_id, ele)) (fst s), snd s)
  |(_, (_, Remove id)) -> (fst s, S.add id (snd s))

let get_ele (o:op_b) =
  match snd (snd o) with
  |Add e -> e
  |Rem e -> e
  
let rc_a o1 o2 = Either

let rc_b o1 o2 = 
  match snd (snd o1), snd (snd o2) with
  |Add e1, Rem e2 -> if e1 = e2 then Snd_then_fst else Either
  |Rem e1, Add e2 -> if e1 = e2 then Fst_then_snd else Either
  |_ -> Either

let rc_c o1 o2 = Either
  
let merge_a l a b = a + b - l

let merge_b l a b = 
  let da = S.difference a l in    //a - l
  let db = S.difference b l in    //b - l
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in   // intersect l a b
  S.union i_lab (S.union da db)          // (intersect l a b) U (a - l) U (b - l)

let merge_c l a b =
   (S.union (fst l) (S.union (fst a) (fst b)),   
    S.union (snd l) (S.union (snd a) (snd b)))
  
/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 200 --ifuel 3"
let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures is_beta_op o1 /\ is_beta_op o2 ==>
                              ((Add? (snd (snd (get_op_b o1))) /\ Rem? (snd (snd (get_op_b o2))) /\ get_ele (get_op_b o1) = get_ele (get_op_b o2) /\ get_key o1 = get_key o2) ==> 
                              ~ (eq (do (do (init_st (Beta_t (get_key o1))) o1) o2) (do (do (init_st (Beta_t (get_key o1))) o2) o1)))) = ()

let rc_non_comm_help2 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures is_beta_op o1 /\ is_beta_op o2 ==>
                              ((Rem? (snd (snd (get_op_b o1))) /\ Add? (snd (snd (get_op_b o2))) /\ get_ele (get_op_b o1) = get_ele (get_op_b o2) /\ get_key o1 = get_key o2) ==> 
                              ~ (eq (do (do (init_st (Beta_t (get_key o1))) o1) o2) (do (do (init_st (Beta_t (get_key o1))) o2) o1)))) = ()

let rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = 
  rc_non_comm_help1 o1 o2;
  rc_non_comm_help2 o1 o2
  
let no_rc_chain o1 o2 o3 = ()
let cond_comm_base s o1 o2 o3 = ()
let cond_comm_ind s o1 o2 o3 o l = ()

////////////////////////////////////////////////////////////////////////////

let merge_comm_a l a b = ()
let merge_comm_b l a b = ()
let merge_comm_c l a b = ()
let merge_idem_a s = ()
let merge_idem_b s = ()
let merge_idem_c s = ()

////////////////////////////////////////////////////////////////////////////

let base_2op_a o1 o2 = ()
let base_2op_b o1 o2 = ()
let base_2op_c o1 o2 = ()
let base_2op' o1 o2 t = ()

#set-options "--z3rlimit 300 --ifuel 3"
let ind_lca_2op_a l o1 o2 ol = ()
let ind_lca_2op_b l o1 o2 ol = ()
let ind_lca_2op_c l o1 o2 ol = ()
let ind_lca_2op' l o1 o2 ol = ()

let inter_right_base_2op_a l a b o1 o2 ob ol = ()
let inter_right_base_2op_b l a b o1 o2 ob ol = ()
let inter_right_base_2op_c l a b o1 o2 ob ol = ()

let inter_right_base_2op' l a b o1 o2 ob ol = ()

let inter_left_base_2op_a l a b o1 o2 ob ol = ()
let inter_left_base_2op_b l a b o1 o2 ob ol = ()
let inter_left_base_2op_c l a b o1 o2 ob ol = ()

let inter_left_base_2op' l a b o1 o2 ob ol = ()

let inter_right_2op_a l a b o1 o2 ob ol o = ()
let inter_right_2op_b l a b o1 o2 ob ol o = ()
let inter_right_2op_c l a b o1 o2 ob ol o = ()

let inter_right_2op' l a b o1 o2 ob ol o = ()

let inter_left_2op_a l a b o1 o2 ob ol o = ()
let inter_left_2op_b l a b o1 o2 ob ol o = ()
let inter_left_2op_c l a b o1 o2 ob ol o = ()

let inter_left_2op' l a b o1 o2 ob ol o = ()

let ind_right_2op_a l a b o1 o2 o2' = ()
let ind_right_2op_b l a b o1 o2 o2' = ()
let ind_right_2op_c l a b o1 o2 o2' = ()

let ind_left_2op_a l a b o1 o2 o1' = ()
let ind_left_2op_b l a b o1 o2 o1' = ()
let ind_left_2op_c l a b o1 o2 o1' = ()

let base_1op_a o1 = ()
let base_1op_b o1 = ()
let base_1op_c o1 = ()

let ind_lca_1op_a l o1 ol = ()
let ind_lca_1op_b l o1 ol = ()
let ind_lca_1op_c l o1 ol = ()

let inter_right_base_1op_a l a b o1 ob ol = ()
let inter_right_base_1op_b l a b o1 ob ol = ()
let inter_right_base_1op_c l a b o1 ob ol = ()

let inter_left_base_1op_a l a b o1 ob ol = ()
let inter_left_base_1op_b l a b o1 ob ol = ()
let inter_left_base_1op_c l a b o1 ob ol = ()

let inter_right_1op_a l a b o1 ob ol o = ()
let inter_right_1op_b l a b o1 ob ol o = ()
let inter_right_1op_c l a b o1 ob ol o = ()

let inter_left_1op_a l a b o1 ob ol o = ()
let inter_left_1op_b l a b o1 ob ol o = ()
let inter_left_1op_c l a b o1 ob ol o = ()

let ind_right_1op_a l a b o1 o1' ol = ()
let ind_right_1op_b l a b o1 o1' ol = ()
let ind_right_1op_c l a b o1 o1' ol = ()
let ind_right_1op' l a b o1 o1' ol = ()

let ind_left_1op_a l a b o1 o1' ol = ()
let ind_left_1op_b l a b o1 o1' ol = ()
let ind_left_1op_c l a b o1 o1' ol = ()
let ind_left_1op' l a b o1 o1' ol = ()

let lem_0op_a l a b ol = ()
let lem_0op_b l a b ol = ()
let lem_0op_c l a b ol = ()
