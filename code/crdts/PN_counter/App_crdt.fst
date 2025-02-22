module App_crdt

module M = Map_extended
module S = Set_extended

// the concrete state type 
type concrete_st = (M.t nat int & M.t nat int) (* keys: replicas IDs, values: int *) (* pair of positive and negative counter *)

let sel (s:M.t nat int) k = if M.contains s k then M.sel s k else 0

// init state
let init_st = (M.const_on S.empty 0, M.const_on S.empty 0)

// equivalence between 2 concrete states
let eq (a b:concrete_st) = 
  (forall id. (M.contains (fst a) id = M.contains (fst b) id) /\ (sel (fst a) id == sel (fst b) id)) /\
  (forall id. (M.contains (snd a) id = M.contains (snd b) id) /\ (sel (snd a) id == sel (snd b) id))

let symmetric a b = ()

let transitive a b c = ()

let eq_is_equiv a b = ()

// operation type
type app_op_t:eqtype =
  |Inc 
  |Dec 

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st = 
  match snd o with
  |r, Inc -> M.upd (fst s) r (sel (fst s) r + 1), snd s
  |r, Dec -> fst s, M.upd (snd s) r (sel (snd s) r + 1)

//conflict resolution
let rc (o1 o2:op_t) = Either

let max a b = if a > b then a else b

// concrete merge operation
let merge (a b:concrete_st) : concrete_st =
  let keys_f = S.union (M.domain (fst a)) (M.domain (fst b)) in
  let u_f = M.const_on keys_f 0 in
  let f = M.iter_upd (fun k v -> max (sel (fst a) k) (sel (fst b) k)) u_f in
  let keys_s = S.union (M.domain (snd a)) (M.domain (snd b)) in
  let u_s = M.const_on keys_s 0 in
  let s = M.iter_upd (fun k v -> max (sel (snd a) k) (sel (snd b) k)) u_s in
  f, s
   
/////////////////////////////////////////////////////////////////////////////

let rc_non_comm o1 o2 = ()
          
let no_rc_chain o1 o2 o3 = ()

let cond_comm_base s o1 o2 o3 = ()

#set-options "--ifuel 3"
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
