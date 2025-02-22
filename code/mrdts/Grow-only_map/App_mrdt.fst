module App_mrdt

module M = Map_extended
module S = Set_extended

// the concrete state type
type concrete_st = M.t nat (S.t nat)

// init state
let init_st = M.const S.empty

let sel (s:concrete_st) k = if M.contains s k then M.sel s k else S.empty

let eq_s (a b:S.t nat) : Type0 = a == b

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
 (forall k. (M.contains a k = M.contains b k) /\ eq_s (sel a k) (sel b k))

let symmetric a b = ()

let transitive a b c = ()

let eq_is_equiv a b = ()

// operation type
type app_op_t = nat * nat //// (the only operation is Add, so nat * nat is fine)

let key (op:op_t) = fst (snd op)

let value (op:op_t) = snd (snd op)

let do (s:concrete_st) (op:op_t) : concrete_st =
  let (ts, (_, (k,v))) = op in
  M.upd s k (S.add v (sel s k))

//conflict resolution
let rc (o1 o2:op_t) = Either

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u:concrete_st = M.const_on keys S.empty in
  M.iter_upd (fun k v -> S.union (sel l k) (S.union (sel a k) (sel b k))) u
   
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
