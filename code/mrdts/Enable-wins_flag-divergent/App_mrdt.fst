module App_mrdt

type concrete_st = (int * bool)

// init state
let init_st : concrete_st = (0, false)

// equivalence between 2 concrete states
let eq (a b:concrete_st) = a = b

let symmetric a b = ()

let transitive a b c = ()

let eq_is_equiv a b = ()

// operation type
type app_op_t:eqtype =
  |Enable 
  |Disable

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |(_, (rid, Enable)) -> (fst s + 1, true)
  |(_, (rid, Disable)) -> (fst s, false)

//conflict resolution
let rc (o1 o2:op_t) =
  match snd (snd o1), snd (snd o2) with
  |Enable, Disable -> Snd_then_fst
  |Disable, Enable -> Fst_then_snd 
  |_ -> Either

let merge_flag (l a b:concrete_st) =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac > lc
          else bc > lc

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  (fst a + fst b - fst l, merge_flag l a b)
  
/////////////////////////////////////////////////////////////////////////////

let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Enable? (snd (snd o1)) /\ Disable? (snd (snd o2))) ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1)))) = ()
         
let rc_non_comm_help2 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Disable? (snd (snd o1)) /\ Enable? (snd (snd o2))) ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1)))) = ()
          
let rc_non_comm o1 o2 =
  rc_non_comm_help1 o1 o2;
  rc_non_comm_help2 o1 o2
          
let no_rc_chain o1 o2 o3 = ()

let cond_comm_base s o1 o2 o3 = ()

let cond_comm_ind s o1 o2 o3 o l = ()
          
/////////////////////////////////// Verification Conditions //////////////////////////////////////////

let merge_comm l a b = ()

let merge_idem s = ()

#set-options "--z3rlimit 300 --ifuel 3"
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

//o = Enable, o1 = Disable
let inter_right_1op l a b o1 ob ol o = ()  // VC showing that buggy implementation cannot be proven in our framework

let inter_left_1op l a b o1 ob ol o = ()

let inter_lca_1op l a b o1 ol oi = ()

let ind_left_1op l a b o1 o1' ol = ()

let ind_right_1op l a b o2 o2' ol = ()

let lem_0op l a b ol = ()
