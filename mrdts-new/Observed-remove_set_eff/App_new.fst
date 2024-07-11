module App_new

module S = Set_extended
module M = Map_extended

#set-options "--query_stats"

let cf = (int * bool)

// the concrete state type
type concrete_st = M.t nat (M.t nat cf) // element ->
                                       //    replica ID -> 
                                       //       (ctr, flag) //elements & replica ids are unique

// init state
let init_st : concrete_st = M.const (M.const (0, false))

let sel_id (s:M.t nat cf) id = if M.contains s id then M.sel s id else (0, false)

let sel (s:concrete_st) e = if M.contains s e then M.sel s e else (M.const (0, false))

// equivalence relation of ew flag
let eq_e (a b:M.t nat cf) =
  (forall id. M.contains a id = M.contains b id /\ sel_id a id = sel_id b id)
  
// equivalence between 2 concrete states
let eq (a b:concrete_st) =
 (forall e. M.contains a e = M.contains b e /\ eq_e (sel a e) (sel b e))
 //(forall k. (M.contains a k = M.contains b k) /\ eq_e (sel a k) (sel b k)) 

let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b) = ()

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
  |(_, (rid, Add e)) -> M.upd s e (M.upd (sel s e) rid (fst (sel_id (sel s e) rid) + 1, true))
  |(_, (rid, Rem e)) -> M.iter_upd (fun k v -> if k = e then ((M.map_val (fun (c,f) -> (c, false))) v) else v) s
 
//conflict resolution
let rc (o1 o2:op_t) =  
  match snd (snd o1), snd (snd o2) with
  |Add e1, Rem e2 -> if e1 = e2 then Snd_then_fst else Either
  |Rem e1, Add e2 -> if e1 = e2 then Fst_then_snd else Either
  |_ -> Either

let merge_flag (l a b:cf) : bool =
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
let merge_cf (l a b:cf) : cf =
  (fst a + fst b - fst l, merge_flag l a b)
  
// concrete merge operation
let merge_ew (l a b:(M.t nat cf)) : (M.t nat cf) =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun k v -> merge_cf (sel_id l k) (sel_id a k) (sel_id b k)) u
  
// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let eles = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on eles init_st in
  M.iter_upd (fun k v -> merge_ew (sel l k) (sel a k) (sel b k)) u

/////////////////////////////////////////////////////////////////////////////

let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (ensures (((Add? (snd (snd o1)) /\ Rem? (snd (snd o2))) \/ (Rem? (snd (snd o1)) /\ Add? (snd (snd o2)))) /\ get_ele o1 = get_ele o2)
  ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))) = ()

let rc_non_comm (o1 o2:op_t)
  : Lemma (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = 
  rc_non_comm_help1 o1 o2
  
let no_rc_chain (o1 o2 o3:op_t)
  : Lemma (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3))) = ()

let cond_comm_base (s:concrete_st) (o1 o2 o3:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

#set-options "--z3rlimit 500 --ifuel 5"
let cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:seq op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)) /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3)) = ()

/////////////////////////////////////////////////////////////////////////////
// Merge commutativity
let merge_comm (l a b:concrete_st)
   : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

// Merge idempotence
let merge_idem (s:concrete_st)
   : Lemma (ensures eq (merge s s s) s) = ()

///////////////////////////////////////////////////////////////////////////

let base_2op o1 o2 = ()

let ind_lca_2op l o1 o2 ol = ()

let inter_right_base_2op_fts (l a b :concrete_st) (o1 o2 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc o2 o1) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (merge l a (do (do b ob) o2)) o1) /\ //from ind_right_2op
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do a ol) (do (do b ol) o2)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) o1)) = ()

let inter_right_base_2op_comm (l a b :concrete_st) (o1 o2 ob ol:op_t)
  : Lemma (requires Either? (rc o2 o1) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) /\ //from pre-cond of ind_right_2op
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (merge l a (do (do b ob) o2)) o1) /\ //from ind_right_2op
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do a ol) (do (do b ol) o2)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) o1)) = ()
          
let inter_right_base_2op l a b o1 o2 ob ol = 
  if Fst_then_snd? (rc o2 o1) then inter_right_base_2op_fts l a b o1 o2 ob ol
  else inter_right_base_2op_comm l a b o1 o2 ob ol
     
let inter_left_base_2op l a b o1 o2 ob ol = ()

let inter_right_2op_fts (l a b:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc o2 o1) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) o1)) = ()

let inter_right_2op_comm (l a b:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Either? (rc o2 o1) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    get_rid o <> get_rid ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) o1)) = ()

let inter_right_2op l a b o1 o2 ob ol o = 
  if Fst_then_snd? (rc o2 o1) then inter_right_2op_fts l a b o1 o2 ob ol o
  else inter_right_2op_comm l a b o1 o2 ob ol o

let inter_left_2op l a b o1 o2 ob ol o = ()

let inter_lca_2op l a b o1 o2 ol = ()
    
let ind_right_2op l a b o1 o2 o2' = ()

let ind_left_2op l a b o1 o2 o1' = ()

let base_1op o1 = ()

let ind_lca_1op l o1 ol = ()

let inter_right_base_1op l a b o1 ob ol = ()
     
let inter_left_base_1op l a b o1 ob ol = ()

let inter_right_1op l a b o1 ob ol o = ()

let inter_left_1op (l a b:concrete_st) (o1 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do a ob) ol) (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) o1)) = ()

let inter_lca_1op (l a b:concrete_st) (o1 ol oi:op_t)
  : Lemma (requires distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops ol oi /\
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do b oi)) (do (merge (do l oi) (do a oi) (do b oi)) o1) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1))
          (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do b oi) ol)) 
                      (do (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) o1)) = ()
                      
let ind_left_1op l a b o1 o1' ol = ()

let ind_right_1op l a b o2 o2' ol = ()

let lem_0op l a b ol = ()
