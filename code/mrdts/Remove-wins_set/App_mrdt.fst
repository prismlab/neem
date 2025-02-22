module App_mrdt

module S = Set_extended

// the concrete state type
type concrete_st = s:S.t (nat * nat){forall e. S.mem e s ==> ((snd e = 1) \/ (snd e = 2))} //(nat & nat)

// init state
let init_st : concrete_st = S.add (0,1) (S.add (0,2) S.empty)

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  forall e. S.mem e a <==> S.mem e b

let symmetric a b = ()

let transitive a b c = ()

let eq_is_equiv a b = ()

// operation type
type app_op_t:eqtype =
  |Add1
  |Rem1
  |Add2
  |Rem2

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
 match o with
  |(_, (rid, Add1)) -> S.filter s (fun e -> snd e <> 1)
  |(ts, (rid, Rem1)) -> S.add (ts, 1) s
  |(_, (rid, Add2)) -> S.filter s (fun e -> snd e <> 2)
  |(ts, (rid, Rem2)) -> S.add (ts, 2) s

//conflict resolution
let rc (o1 o2:op_t) =
  match snd (snd o1), snd (snd o2) with
  |Add1, Rem1 |Add2, Rem2 -> Fst_then_snd
  |Rem1, Add1 | Rem2, Add2 -> Snd_then_fst
  |_ -> Either

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let da = S.difference a l in
  let db = S.difference b l in
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in
  S.union i_lab (S.union da db)

/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 300 --ifuel 3"
let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Add1? (snd (snd o1)) /\ Rem1? (snd (snd o2))) \/ (Rem1? (snd (snd o1)) /\ Add1? (snd (snd o2))))
                           ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))) = ()
         
let rc_non_comm_help2 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Add2? (snd (snd o1)) /\ Rem2? (snd (snd o2))) \/ (Rem2? (snd (snd o1)) /\ Add2? (snd (snd o2))))
                           ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))) = ()
          
let rc_non_comm o1 o2 = 
  rc_non_comm_help1 o1 o2;
  rc_non_comm_help2 o1 o2

let no_rc_chain o1 o2 o3 = ()

let cond_comm_base s o1 o2 o3 = ()

let cond_comm_ind s o1 o2 o3 o l = ()
 
/////////////////////////////////// Verification Conditions //////////////////////////////////////////

let merge_comm l a b = ()

let merge_idem s = ()

let base_2op o1 o2 = ()

let ind_lca_2op l o1 o2 ol = ()

let inter_right_base_2op l a b o1 o2 ob ol = ()
     
let inter_left_base_2op l a b o1 o2 ob ol = ()

let inter_right_2op l a b o1 o2 ob ol o = ()

let inter_left_2op l a b o1 o2 ob ol o = ()

let inter_lca_2op l a b o1 o2 ol = ()

let ind_right_2op l a b o1 o2 o2' = ()

let ind_left_2op l a b o1 o2 o1' = ()

let base_1op o1 = ()

let ind_lca_1op l o1 ol = ()

let inter_right_base_1op l a b o1 ob ol = ()
     
let inter_left_base_1op l a b o1 ob ol = ()

let inter_right_1op l a b o1 ob ol o = ()

let inter_left_1op l a b o1 ob ol o = ()

let inter_lca_1op l a b o1 ol oi = ()

let ind_left_1op l a b o1 o1' ol = ()

let ind_right_1op l a b o2 o2' ol = ()

let lem_0op l a b ol = ()
