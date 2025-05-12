module App_mrdt

module S = Set_extended
module M = Map_extended

type replica_id : eqtype = nat
type element : eqtype = nat
type timestamp : eqtype = pos

// the concrete state type
type concrete_st = S.t (replica_id & timestamp & element)
  // replica_id -> element -> timestamp
  // Uses [O(n * r)] space where
  //    n = number of elements in the set
  //    r = number of replicas

// init state
let init_st : concrete_st = S.empty

// equivalence between 2 concrete states
let eq (a b:concrete_st) : Type0 =
  a == b

let symmetric a b = ()

let transitive a b c = ()

let eq_is_equiv a b = ()

// operation type
type app_op_t : eqtype =
  |Add : nat -> app_op_t
  |Rem : nat -> app_op_t

let get_ele (o:op_t) : nat =
  match snd (snd o) with
  |Add e -> e
  |Rem e -> e

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  | (ts, (rid, Add e)) ->
    let s' = S.filter s (fun (rid',_,e') -> not (rid = rid' && e = e')) in
    S.add (rid,ts,e) s'
  | (_, (rid, Rem e)) ->
    S.filter s (fun (_,_,e') -> not (e = e'))

let test () =
  let s1 = do init_st (1, (1, Add 0)) in
  let s1' = S.singleton (1,1,0) in
  assert (eq s1 s1');
  let s2 = do s1 (2, (1, Add 0)) in
  let s2' = S.singleton (1,2,0) in
  assert (eq s2 s2');
  let s3 = do s2 (3, (2, Add 0)) in
  let s3' = S.add (2,3,0) s2' in
  assert (eq s3 s3')

//conflict resolution
let rc (o1 o2:op_t) =
  match snd (snd o1), snd (snd o2) with
  |Add e1, Rem e2 -> if e1 = e2 then Snd_then_fst else Either
  |Rem e1, Add e2 -> if e1 = e2 then Fst_then_snd else Either
  |_ -> Either

let merge (l a b : concrete_st) : concrete_st =
  let da = S.difference a l in    //a - l
  let db = S.difference b l in    //b - l
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in   // intersect l a b
  S.union i_lab (S.union da db)          // (intersect l a b) U (a - l) U (b - l)

  /////////////////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 100 --max_ifuel 3"
let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures (((Add? (snd (snd o1)) /\ Rem? (snd (snd o2))) \/ (Rem? (snd (snd o1)) /\ Add? (snd (snd o2)))) /\ get_ele o1 = get_ele o2) ==>
                           ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))) = ()

let rc_non_comm o1 o2 =
  rc_non_comm_help1 o1 o2

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