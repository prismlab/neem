module App_crdt

module M = Map_extended
module S = Set_extended

// the concrete state type 
type concrete_st = (S.t nat & S.t nat) (* add and remove set *)

// init state
let init_st = S.empty, S.empty

// equivalence between 2 concrete states
let eq (a b:concrete_st) = 
  (forall e. S.mem e (fst a) <==> S.mem e (fst b)) /\
  (forall e. S.mem e (snd a) <==> S.mem e (snd b))

let symmetric a b = ()

let transitive a b c = ()

let eq_is_equiv a b = ()

// operation type
type app_op_t:eqtype =
  |Add : nat -> app_op_t 
  |Rem : nat -> app_op_t

let get_ele (o:op_t) : nat =
  match snd (snd o) with
  |Add e -> e
  |Rem e -> e
  
// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st = 
  match o with
  |ts, (_, Add e) -> S.add e (fst s), snd s
  |ts, (_, Rem e) -> fst s, (if S.mem e (fst s) then S.add e (snd s) else snd s)

//conflict resolution
let rc (o1 o2:op_t) = 
  match snd (snd o1), snd (snd o2) with
  |Add e1, Rem e2 -> if e1 = e2 then Snd_then_fst else Either
  |Rem e1, Add e2 -> if e1 = e2 then Fst_then_snd else Either
  |_ -> Either

// concrete merge operation
let merge (a b:concrete_st) : concrete_st =
  S.union (fst a) (fst b), S.union (snd a) (snd b)
   
/////////////////////////////////////////////////////////////////////////////

let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures (((Add? (snd (snd o1)) /\ Rem? (snd (snd o2))) \/ 
                     (Rem? (snd (snd o1)) /\ Add? (snd (snd o2)))) /\ get_ele o1 = get_ele o2) ==> 
                           ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))) = ()
                           
let rc_non_comm o1 o2 =
  rc_non_comm_help1 o1 o2
          
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
