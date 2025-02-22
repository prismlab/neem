module App_mrdt

module S = Set_extended

// the concrete state type
type concrete_st = S.t nat

// init state
let init_st = S.empty

// equivalence between 2 concrete states
let eq (a b:concrete_st) = a == b

let symmetric a b = ()

let transitive a b c = ()

let eq_is_equiv a b = ()

// operation type
type app_op_t:eqtype = nat //// (the only operation is Add, so nat is fine)

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =  
  S.add (snd (snd o)) s

//conflict resolution
let rc (o1 o2:op_t) = Either

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  S.union l (S.union a b)
   
/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 100 --ifuel 3"
let rc_non_comm o1 o2 = ()
          
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
