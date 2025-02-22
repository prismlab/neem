module App_crdt

module M = Map_extended
module S = Set_extended

// the concrete state type 
type concrete_st = M.t nat (S.t nat) (* keys: nat, values: GSet *)

let sel (s:concrete_st) k = if M.contains s k then M.sel s k else S.empty

// init state
let init_st = M.const_on S.empty S.empty

// equivalence between 2 concrete states
let eq (a b:concrete_st) = 
  (forall id. (M.contains a id = M.contains b id) /\ 
  (forall id e. S.mem e (sel a id) <==> S.mem e (sel b id)))

let symmetric a b = ()

let transitive a b c = ()

let eq_is_equiv a b = ()

// operation type
type app_op_t:eqtype = 
  |Set : nat -> nat -> app_op_t

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st = 
  let (_,(_,Set k v)) = o in 
  M.upd s k (S.add v (sel s k))

//conflict resolution
let rc (o1 o2:op_t) = Either

// concrete merge operation
let merge (a b:concrete_st) : concrete_st =
  let keys = S.union (M.domain a) (M.domain b) in
  let u = M.const_on keys 0 in
  M.iter_upd (fun k v -> S.union (sel a k) (sel b k)) u
   
/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 100 --ifuel 3"
let rc_non_comm o1 o2 = ()

let no_rc_chain o1 o2 o3 = ()

let cond_comm_base s o1 o2 o3 = ()

let cond_comm_ind s o1 o2 o3 o l = ()
  
/////////////////////////////////// Verification Conditions //////////////////////////////////////////

let merge_comm a b = ()

let merge_idem s = ()

let base_2op o1 o2 = ()

let ind_lca_2op l o1 o2 ol = ()

let inter_right_base_2op a b o1 o2 ob ol = ()
     
let inter_left_base_2op a b o1 o2 ob ol = ()

let inter_right_2op a b o1 o2 ob ol o = ()

let inter_left_2op a b o1 o2 ob ol o = ()

let inter_lca_2op a b o1 o2 ol = ()

let ind_right_2op a b o1 o2 o2' = ()

let ind_left_2op a b o1 o2 o1' = ()
       
let base_1op o1 = ()

let ind_lca_1op l o1 ol = ()

let inter_right_base_1op a b o1 ob ol = ()
     
let inter_left_base_1op a b o1 ob ol = ()

let inter_right_1op a b o1 ob ol o = ()

let inter_left_1op a b o1 ob ol o = ()

let inter_lca_1op a b o1 ol oi = ()

let ind_left_1op a b o1 o1' ol = ()

let ind_right_1op a b o2 o2' ol = ()

let lem_0op a b ol = ()
