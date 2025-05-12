module App_mrdt

module S = Set_extended
module M = Map_extended

type timestamp : eqtype = pos
type element : eqtype = nat

// the concrete state type
type concrete_st = M.t element (S.t timestamp)
  // Elements -> Set Timestamps

// init state
let init_st : concrete_st = M.const (S.empty)

let sel (s:concrete_st) e = if M.contains s e then M.sel s e else S.empty

let eq_s (a b : S.t timestamp) =
  forall e. S.mem e a <==> S.mem e b

// equivalence between 2 concrete states
let eq (a b:concrete_st) : Type0 =
  (forall e. (M.contains a e == M.contains b e) /\ eq_s (sel a e) (sel b e))                          

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
  | (ts, (_, Add e)) ->
     let tss = sel s e in
     M.upd s e (S.add ts tss)
  | (_, (_, Rem e)) ->
    M.iter_upd (fun ele tss -> if ele = e then S.empty else tss) s

//conflict resolution
let rc (o1 o2:op_t) =
  match snd (snd o1), snd (snd o2) with
  |Add e1, Rem e2 -> if e1 = e2 then Snd_then_fst else Either
  |Rem e1, Add e2 -> if e1 = e2 then Fst_then_snd else Either
  |_ -> Either

let merge_set (l a b : S.t timestamp) : S.t timestamp =
  let da = S.difference a l in    //a - l
  let db = S.difference b l in    //b - l
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in   // intersect l a b
  S.union i_lab (S.union da db)          // (intersect l a b) U (a - l) U (b - l)

let merge (l a b : concrete_st) : concrete_st =
  let keys : S.t element = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u : concrete_st = M.const_on keys S.empty in
  M.iter_upd (fun (ele:element) _ -> merge_set (sel l ele) (sel a ele) (sel b ele)) u

/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 200 --ifuel 5"
let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (ensures (Add? (snd (snd o1)) /\ Rem? (snd (snd o2)) /\ get_ele o1 = get_ele o2)
  ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))) = ()

let rc_non_comm_help2 (o1 o2:op_t)
  : Lemma (ensures (Rem? (snd (snd o1)) /\ Add? (snd (snd o2)) /\ get_ele o1 = get_ele o2)
  ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))) = ()

let rc_non_comm o1 o2 = 
  rc_non_comm_help1 o1 o2;
  rc_non_comm_help2 o1 o2;
  ()
  
let no_rc_chain o1 o2 o3 = ()

let cond_comm_base s o1 o2 o3 = ()

let cond_comm_ind s o1 o2 o3 o l = ()

/////////////////////////////////////////////////////////////////////////////

// Merge commutativity
let merge_comm l a b = ()

// Merge idempotence
let merge_idem s = ()

/////////////////////////////////////////////////////////////////////////////

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
