module App

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
  (forall id. M.contains a id = M.contains b id /\ sel_id a id == sel_id b id)
  
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

#push-options "--z3rlimit 100 --max_ifuel 3"
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

(*Two OP RC*)
//////////////// 
let rc_ind_right (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let rc_ind_left (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

let rc_ind_lca (l:concrete_st) (o1 o2 o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()

let rc_base (o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

#push-options "--z3rlimit 300 --max_ifuel 4"
let rc_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let rc_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

//does not pass automatically. Passes with asserts in rc_inter_right'
let rc_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = admit()

let rc_inter_right' (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = 
  let lhs = merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2) in
  let rhs = do (do (do (do (do c o) ob) ol) o1) o2 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o1)) rid) = fst (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ob)) rid) = fst (sel_id (sel rhs (get_ele ob)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o)) rid) = fst (sel_id (sel rhs (get_ele o)) rid));
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele ob /\ ele <> get_ele ol /\ ele <> get_ele o) ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid)); 
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()

//does not pass automatically. Passes with asserts in rc_inter_left'
let rc_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = admit()
      
let rc_inter_left' (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = 
  let lhs = merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2) in
  let rhs = do (do (do (do (do c o) ob) ol) o1) o2 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o1)) rid) = fst (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ob)) rid) = fst (sel_id (sel rhs (get_ele ob)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o)) rid) = fst (sel_id (sel rhs (get_ele o)) rid));
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele ob /\ ele <> get_ele ol /\ ele <> get_ele o) ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()

let rc_inter_lca (l a b c:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) = admit()

let rc_inter_lca' (l a b c:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) = 
  let lhs = merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2) in
  let rhs = do (do (do (do c oi) ol) o1) o2 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o1)) rid) = fst (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele oi)) rid) = fst (sel_id (sel rhs (get_ele oi)) rid));
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele ol /\ ele <> get_ele oi) ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele o1)) rid) == snd (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele o2)) rid) == snd (sel_id (sel rhs (get_ele o2)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele ol)) rid) == snd (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele oi)) rid) == snd (sel_id (sel rhs (get_ele oi)) rid));
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele ol /\ ele <> get_ele oi) ==>
                     snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()

(*One op*)
///////////////
let one_op_ind_right (l a b c:concrete_st) (o2 o2':op_t)
   : Lemma (requires eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2)) = ()

let one_op_ind_left (l a b c:concrete_st) (o1 o1':op_t)
   : Lemma (requires eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) = ()
           
let one_op_ind_lca (l:concrete_st) (o2 o:op_t)
  : Lemma (requires eq (merge l l (do l o2)) (do l o2))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o2)) (do (do l o) o2)) = () 

let one_op_base (o2:op_t)
  : Lemma (ensures eq (merge init_st init_st (do init_st o2)) (do init_st o2)) = ()

let one_op_inter_base_right (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) = ()

let one_op_inter_base_left (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ //EXTRA!! 
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) = ()

let one_op_inter_right (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) = admit()

let one_op_inter_right' (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) = 
  let lhs = merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2) in
  let rhs = do (do (do (do c o) ob) ol) o2 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ob)) rid) = fst (sel_id (sel rhs (get_ele ob)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o)) rid) = fst (sel_id (sel rhs (get_ele o)) rid));
  assume (forall ele rid. (ele <> get_ele o2 /\ ele <> get_ele ob /\ ele <> get_ele ol /\ ele <> get_ele o) ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()
          
let one_op_inter_left (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) = admit()

let one_op_inter_left' (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) =
  let lhs = merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2) in
  let rhs = do (do (do (do c o) ob) ol) o2 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid)); 
  assume (forall rid. fst (sel_id (sel lhs (get_ele ob)) rid) = fst (sel_id (sel rhs (get_ele ob)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o)) rid) = fst (sel_id (sel rhs (get_ele o)) rid));
  assume (forall ele rid. (ele <> get_ele o2 /\ ele <> get_ele ob /\ ele <> get_ele ol /\ ele <> get_ele o) ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()
          
let one_op_inter_lca (l a b c:concrete_st) (o2 ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) = 
  let lhs = merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2) in
  let rhs = do (do (do c oi) ol) o2 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid)); 
  assume (forall rid. fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid)); 
  assume (forall rid. fst (sel_id (sel lhs (get_ele oi)) rid) = fst (sel_id (sel rhs (get_ele oi)) rid));
  assume (forall ele rid. (ele <> get_ele o2 /\ ele <> get_ele ol /\ ele <> get_ele oi) ==>
                     fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele o2)) rid) == snd (sel_id (sel rhs (get_ele o2)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele ol)) rid) == snd (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele oi)) rid) == snd (sel_id (sel rhs (get_ele oi)) rid));
  assume (forall ele rid. (ele <> get_ele o2 /\ ele <> get_ele ol /\ ele <> get_ele oi) ==>
                     snd (sel_id (sel lhs (get_ele ol)) rid) == snd (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()

(*Zero op *)
///////////////
let zero_op_inter_base_right (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) = () 

let zero_op_inter_base_left (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do b ol) ) (do (do c ob) ol)) = () 

let zero_op_inter_right (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol)) = ()

let zero_op_inter_left (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol)) = ()

let zero_op_inter_lca_v1 (l a b c:concrete_st) (ol:op_t)
  : Lemma (requires (exists o'. Fst_then_snd? (rc o' ol)) /\ eq (merge l a b) c)
          (ensures eq (merge (do l ol) (do a ol) (do b ol)) (do c ol)) = ()

let zero_op_inter_lca_v2 (l a b c:concrete_st) (ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\
                    eq (merge (do l oi) (do a oi) (do b oi)) (do c oi)  /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol)) = ()

(* 2 op Comm  *)
///////////////////

let comm_ind_right (l a b c:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) )
                    //~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = 
  let lhs = merge l (do a o1) (do (do b o2') o2) in
  let rhs = do (do (merge l a (do b o2')) o2) o1 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o1)) rid) = fst (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2')) rid) = fst (sel_id (sel rhs (get_ele o2')) rid)); 
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele o2') ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele o1)) rid) == snd (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele o2)) rid) == snd (sel_id (sel rhs (get_ele o2)) rid)); 
  assume (forall rid. snd (sel_id (sel lhs (get_ele o2')) rid) == snd (sel_id (sel rhs (get_ele o2')) rid)); 
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele o2') ==>
                     snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()

let comm_ind_left (l a b c:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o1' o2) ==> (eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o1')) )
                    //~ (exists o3 b'. eq (do (do b o1') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (do (merge l (do a o1') b) o2) o1)) = 
  let lhs = merge l (do (do a o1') o1) (do b o2) in
  let rhs = do (do (merge l (do a o1') b) o2) o1 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o1)) rid) = fst (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o1')) rid) = fst (sel_id (sel rhs (get_ele o1')) rid)); 
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele o1') ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele o1)) rid) == snd (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele o2)) rid) == snd (sel_id (sel rhs (get_ele o2)) rid)); 
  assume (forall rid. snd (sel_id (sel lhs (get_ele o1')) rid) == snd (sel_id (sel rhs (get_ele o1')) rid)); 
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele o1') ==>
                     snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()

let comm_ind_lca (l:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (do (merge l a (do b ob)) o1) o2) /\ 
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = 
  let lhs = merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2) in
  let rhs = do (do (do (do c ob) ol) o1) o2 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o1)) rid) = fst (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid)); 
  assume (forall rid. fst (sel_id (sel lhs (get_ele ob)) rid) = fst (sel_id (sel rhs (get_ele ob)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele ob /\ ele <> get_ele ol) ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele o1)) rid) == snd (sel_id (sel rhs (get_ele o1)) rid)); 
  assume (forall rid. snd (sel_id (sel lhs (get_ele o2)) rid) == snd (sel_id (sel rhs (get_ele o2)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele ob)) rid) == snd (sel_id (sel rhs (get_ele ob)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele ol)) rid) == snd (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele ob /\ ele <> get_ele ol) ==>
                     snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()

let comm_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do (do a ob) o1) (do b o2)) (do (do (merge l (do a ob) b) o1) o2) /\ 
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = 
  let lhs = merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2) in
  let rhs = do (do (do (do c ob) ol) o1) o2 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid);
  assume (forall rid. fst (sel_id (sel lhs (get_ele o1)) rid) = fst (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid)); 
  assume (forall rid. fst (sel_id (sel lhs (get_ele ob)) rid) = fst (sel_id (sel rhs (get_ele ob)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele ob /\ ele <> get_ele ol) ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid)); 
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid)); 
  assume (forall rid. snd (sel_id (sel lhs (get_ele o1)) rid) == snd (sel_id (sel rhs (get_ele o1)) rid)); 
  assume (forall rid. snd (sel_id (sel lhs (get_ele o2)) rid) == snd (sel_id (sel rhs (get_ele o2)) rid)); 
  assume (forall rid. snd (sel_id (sel lhs (get_ele ob)) rid) == snd (sel_id (sel rhs (get_ele ob)) rid));
  assume (forall rid. snd (sel_id (sel lhs (get_ele ol)) rid) == snd (sel_id (sel rhs (get_ele ol)) rid)); 
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele ob /\ ele <> get_ele ol) ==>
                     snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  assume (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()

let comm_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = admit()

#push-options "--z3rlimit 500 --max_ifuel 5"
let comm_inter_right' (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do (do (do l o) ob) ol) o2)) (do (do (do (do (do l o) ob) ol) o1) o2)) = 
  let e = get_ele o in
  if e = get_ele o1 && get_ele o1 = get_ele o2 then admit() //done
  else if e = get_ele o1 && get_ele o1 <> get_ele o2 then admit() //done
  else if e <> get_ele o1 && get_ele o1 = get_ele o2 then admit() //done
  else if get_ele o1 = get_ele ol then admit() //done
  else admit() //done
          
let comm_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = admit()

let comm_inter_left' (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                            //get_rid o1 <> get_rid o2 /\ get_rid ob <> get_rid ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                      //Either? (rc o ol) /\ 
                    (~(Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) =
  let e = get_ele o in
  if e = get_ele o1 && get_ele o1 = get_ele o2 then admit() //done
  else if e = get_ele o1 && get_ele o1 <> get_ele o2 then admit() //done
  else if e <> get_ele o1 && get_ele o1 = get_ele o2 then admit() //done
  else if get_ele o1 = get_ele ol then admit() //done
  else admit() //done


let merge_pre l a b =
  (forall ele. M.contains l ele <==> (M.contains a ele /\ M.contains b ele)) /\
  (forall ele id. M.contains l ele ==> (M.contains (sel l ele) id <==> (M.contains (sel a ele) id /\ M.contains (sel b ele) id))) /\
  (forall ele id. M.contains l ele /\ M.contains (sel l ele) id ==>
             fst (sel_id (sel l ele) id) <= fst (sel_id (sel a ele) id) /\
             fst (sel_id (sel l ele) id) <= fst (sel_id (sel b ele) id))

//todo
let comm_inter_lca' (l a b c:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ get_rid o1 <> get_rid o2 /\
                    //Rem? (snd (snd o1)) /\ Rem? (snd (snd o2)) /\ get_ele o1 = get_ele o2 /\ //done
                    //Rem? (snd (snd o1)) /\ Rem? (snd (snd o2)) /\ get_ele o1 <> get_ele o2 /\ get_ele o1 = get_ele ol /\ //not done
                    //Add? (snd (snd o1)) /\ Add? (snd (snd o2)) /\ get_ele o1 <> get_ele o2 /\
                    Add? (snd (snd ol)) /\ 
                    //(exists o'. Fst_then_snd? (rc o' ol)) /\
                    //l == init_st /\ a == init_st /\
                    ~ (Fst_then_snd? (rc o1 ol)) /\  ~ (Fst_then_snd? (rc o2 ol)) /\
                    //merge_pre l (do a o1) (do b o2) /\
                    //merge_pre (do l ol) (do (do a ol) o1) (do (do b ol) o2) /\
                    //eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) = 
  let lhs = merge (do l ol) (do (do a ol) o1) (do (do b ol) o2) in
  let rhs = do (do (do c ol) o1) o2 in
  assume (forall k. M.contains lhs k = M.contains rhs k);
  assume (forall ele rid. M.contains lhs ele ==> (M.contains (sel lhs ele) rid = M.contains (sel rhs ele) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o1)) rid) = fst (sel_id (sel rhs (get_ele o1)) rid));
  assume (forall rid. fst (sel_id (sel lhs (get_ele o2)) rid) = fst (sel_id (sel rhs (get_ele o2)) rid)); 
  assume (forall rid. fst (sel_id (sel lhs (get_ele ol)) rid) = fst (sel_id (sel rhs (get_ele ol)) rid));
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\ ele <> get_ele ol) ==>
                     fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid)); 
  assume (forall ele rid. fst (sel_id (sel lhs ele) rid) = fst (sel_id (sel rhs ele) rid)); 
  assume (forall rid. snd (sel_id (sel lhs (get_ele o1)) rid) == snd (sel_id (sel rhs (get_ele o1)) rid));  //works  with fts pre
  assume (forall rid. snd (sel_id (sel lhs (get_ele o2)) rid) == snd (sel_id (sel rhs (get_ele o2)) rid)); 
  assume (forall rid. snd (sel_id (sel lhs (get_ele ol)) rid) == snd (sel_id (sel rhs (get_ele ol)) rid)); 
  assume (forall ele rid. (ele <> get_ele o1 /\ ele <> get_ele o2 /\  ele <> get_ele ol) ==>
                     snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  assert (forall ele rid. snd (sel_id (sel lhs ele) rid) == snd (sel_id (sel rhs ele) rid));
  ()
////////////////////////////////////////////////////////////////

