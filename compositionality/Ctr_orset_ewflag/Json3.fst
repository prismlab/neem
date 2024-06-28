module Json3

module S = Set_extended
module M' = Map_extended

let concrete_st_a = int

let concrete_st_b = S.t (pos & nat)

let concrete_st_c = M'.t nat (int & bool)

let init_st_a = 0

let init_st_b = S.empty

let init_st_c = M'.const_on S.empty (0, false)

let eq_a a b = a = b

let eq_b a b = a == b

let sel_rid (s:concrete_st_c) (k:nat) = if M'.contains s k then M'.sel s k else (0, false)

let eq_c a b = M'.equal a b //(forall id. M'.contains a id = M'.contains b id /\ sel_rid a id = sel_rid b id)

let lem_eq_a a b = ()

let lem_eq_b a b = ()

let lem_eq_c' (a b:concrete_st_c) 
  : Lemma (requires eq_c a b)
          (ensures a == b)
          [SMTPat (eq_c a b)] =
  M'.lemma_equal_elim a b

let lem_eq_c a b = ()

type app_op_a : eqtype =
  |Inc

type app_op_b : eqtype =
  |Add : nat -> app_op_b
  |Rem : nat -> app_op_b

type app_op_c : eqtype =
  |Enable 
  |Disable
  
let do_a s o = s + 1

let do_b s o = 
  match o with
  |(ts, (rid, Add e)) -> S.add (ts, e) s 
  |(_, (rid, Rem e)) -> S.filter s (fun ele -> snd ele <> e)

let do_c s o =
  match o with
  |(_, (rid, Enable)) -> M'.upd s rid (fst (M'.sel s rid) + 1, true)
  |(_, (rid, Disable)) -> M'.map_val (fun (c,f) -> (c, false)) s

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

let rc_c o1 o2 =
  match snd (snd o1), snd (snd o2) with
  |Enable, Disable -> Snd_then_fst
  |Disable, Enable -> Fst_then_snd 
  |_ -> Either
  
let merge_a l a b = a + b - l

let merge_b l a b = 
  let da = S.difference a l in    //a - l
  let db = S.difference b l in    //b - l
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in   // intersect l a b
  S.union i_lab (S.union da db)          // (intersect l a b) U (a - l) U (b - l)

let merge_flag (l a b:(int & bool)) : bool =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac > lc
          else bc > lc

let merge_cf (l a b:(int & bool)) : (int & bool) =
  (fst a + fst b - fst l, merge_flag l a b)

// concrete merge operation
let merge_c l a b =
  let keys = S.union (M'.domain l) (S.union (M'.domain a) (M'.domain b)) in
  let u = M'.const_on keys (0, false) in
  M'.iter_upd (fun k v -> merge_cf (M'.sel l k) (M'.sel a k) (M'.sel b k)) u
  
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

let rc_non_comm_help3 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures is_gamma_op o1 /\ is_gamma_op o2 ==>
                              ((Enable? (snd (snd (get_op_c o1))) /\ Disable? (snd (snd (get_op_c o2))) /\ get_key o1 = get_key o2) ==> 
                              ~ (eq (do (do (init_st (Gamma_t (get_key o1))) o1) o2) (do (do (init_st (Gamma_t (get_key o1))) o2) o1)))) = admit()
         
let rc_non_comm_help4 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures is_gamma_op o1 /\ is_gamma_op o2 ==>
                              ((Disable? (snd (snd (get_op_c o1))) /\ Enable? (snd (snd (get_op_c o2))) /\ get_key o1 = get_key o2) ==> 
                              ~ (eq (do (do (init_st (Gamma_t (get_key o1))) o1) o2) (do (do (init_st (Gamma_t (get_key o1))) o2) o1)))) = admit()

let rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = 
  rc_non_comm_help1 o1 o2;
  rc_non_comm_help2 o1 o2;
  rc_non_comm_help3 o1 o2;
  rc_non_comm_help4 o1 o2
  
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

let inter_right_base_2op' l a b o1 o2 ob ol = admit()

let inter_left_base_2op_a l a b o1 o2 ob ol = ()
let inter_left_base_2op_b l a b o1 o2 ob ol = ()
let inter_left_base_2op_c l a b o1 o2 ob ol = ()

#set-options "--z3rlimit 500 --ifuel 5"
let inter_left_base_2op' l a b o1 o2 ob ol = admit()

let inter_right_2op_a l a b o1 o2 ob ol o = ()
let inter_right_2op_b l a b o1 o2 ob ol o = ()
let inter_right_2op_c l a b o1 o2 ob ol o = ()

let inter_right_2op' l a b o1 o2 ob ol o = admit()

let inter_left_2op_a l a b o1 o2 ob ol o = ()
let inter_left_2op_b l a b o1 o2 ob ol o = ()
let inter_left_2op_c l a b o1 o2 ob ol o = ()

let inter_left_2op' l a b o1 o2 ob ol o = admit()

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
