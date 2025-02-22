module App_mrdt

module S = Set_extended

// the concrete state type
type concrete_st = S.t (nat & (nat & nat)) & S.t nat //fst:(ts,after_id,ele), snd:tombstone set

// init state
let init_st = (S.empty, S.empty)

// equivalence between 2 concrete states
let eq (a b:concrete_st) = 
  S.equal (fst a) (fst b) /\
  S.equal (snd a) (snd b)

let symmetric a b = ()

let transitive a b c = ()

let eq_is_equiv a b = ()

// operation type
type app_op_t:eqtype = 
  |Add_after : after_id:nat -> ele:nat -> app_op_t //inserts ele after after_id
  |Remove : id:pos -> app_op_t //removes the element with identifier id

let get_ele (op:op_t{Add_after? (snd (snd op))}) : nat =
  let (_, (_, Add_after _ ele)) = op in ele

let get_after_id (op:op_t{Add_after? (snd (snd op))}) : nat =
  let (_, (_, Add_after id _)) = op in id

let get_rem_id (op:op_t{Remove? (snd (snd op))}) : pos =
  let (_, (_, Remove id)) = op in id

let id_ele (s:concrete_st) (id ele:nat) =
  exists e. S.mem e (fst s) /\ fst e = id /\ snd (snd e) = ele /\ not (S.mem id (snd s))

let mem_id_s (id:nat) (s:S.t (nat & (nat & nat))) =
  exists e. S.mem e s /\ fst e = id
  
// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |(ts, (_, Add_after after_id ele)) -> (S.add (ts, (after_id, ele)) (fst s), snd s)
  |(_, (_, Remove id)) -> (fst s, S.add id (snd s))

//conflict resolution
let rc (o1 o2:op_t) = Either

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
   (S.union (fst l) (S.union (fst a) (fst b)),   
    S.union (snd l) (S.union (snd a) (snd b)))
   
/////////////////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 100 --max_ifuel 3"
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

#pop-options