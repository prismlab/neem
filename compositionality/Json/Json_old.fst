module Json

module S = FStar.Set //Set_extended

let concrete_st_a = int

let concrete_st_b = S.set nat

let init_st_a = 0

let init_st_b = S.empty

let eq_a a b = a = b

let eq_b a b = S.equal a b

let lem_eq_a a b = ()

let lem_eq_b a b = ()

type app_op_a : eqtype =
  |Inc

type app_op_b : eqtype =
  |Add : nat -> app_op_b

let do_a s o = s + 1

let do_b s o = let _,(_,Add e) = o in S.add e s

let get_ele (o:op_t{is_beta_op o}) =
  let (Set _ (Beta_op (Add e))) = snd (snd o) in e

let rc_a o1 o2 = Either

let rc_b o1 o2 = Either

let merge_a l a b = a + b - l

let merge_b l a b = S.union l (S.union a b)

/////////////////////////////////////////////////////////////////////////////

#set-options "--ifuel 3"
let rc_non_comm o1 o2 = ()
let no_rc_chain o1 o2 o3 = ()
let cond_comm_base s o1 o2 o3 = ()
let cond_comm_ind s o1 o2 o3 o l = ()

////////////////////////////////////////////////////////////////////////////

let merge_comm_a l a b = ()
let merge_comm_b l a b = ()
let merge_idem_a s = ()
let merge_idem_b s = ()

////////////////////////////////////////////////////////////////////////////

let base_2op_a o1 o2 = ()
let base_2op_b o1 o2 = ()
let base_2op' o1 o2 t = ()

#set-options "--z3rlimit 100 --ifuel 3"
let ind_lca_2op_a l o1 o2 ol = ()
let ind_lca_2op_b l o1 o2 ol = ()
let ind_lca_2op' l o1 o2 ol = ()

let inter_right_base_2op_a l a b o1 o2 ob ol = ()
let inter_right_base_2op_b l a b o1 o2 ob ol = ()
let inter_right_base_2op' l a b o1 o2 ob ol = ()

let inter_left_base_2op_a l a b o1 o2 ob ol = ()
let inter_left_base_2op_b l a b o1 o2 ob ol = ()
let inter_left_base_2op' l a b o1 o2 ob ol = ()

let inter_right_2op_a l a b o1 o2 ob ol o = ()
let inter_right_2op_b l a b o1 o2 ob ol o = ()
let inter_right_2op' l a b o1 o2 ob ol o = ()

let inter_left_2op_a l a b o1 o2 ob ol o = ()
let inter_left_2op_b l a b o1 o2 ob ol o = ()
let inter_left_2op' l a b o1 o2 ob ol o = ()

let ind_right_2op_a l a b o1 o2 o2' = ()
let ind_right_2op_b l a b o1 o2 o2' = ()

let ind_left_2op_a l a b o1 o2 o1' = ()
let ind_left_2op_b l a b o1 o2 o1' = ()

let base_1op_a o1 = ()
let base_1op_b o1 = ()

let ind_lca_1op_a l o1 ol = ()
let ind_lca_1op_b l o1 ol = ()

let inter_right_base_1op_a l a b o1 ob ol = ()
let inter_right_base_1op_b l a b o1 ob ol = ()

let inter_left_base_1op_a l a b o1 ob ol = ()
let inter_left_base_1op_b l a b o1 ob ol = ()

let inter_right_1op_a l a b o1 ob ol o = ()
let inter_right_1op_b l a b o1 ob ol o = ()

let inter_left_1op_a l a b o1 ob ol o = ()
let inter_left_1op_b l a b o1 ob ol o = ()

let ind_right_1op_a l a b o1 o1' ol = ()
let ind_right_1op_b l a b o1 o1' ol = ()
let ind_right_1op' l a b o1 o1' ol = ()

let ind_left_1op_a l a b o1 o1' ol = ()
let ind_left_1op_b l a b o1 o1' ol = ()
let ind_left_1op' l a b o1 o1' ol = ()

let lem_0op_a l a b ol = ()
let lem_0op_b l a b ol = ()
