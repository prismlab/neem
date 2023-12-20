module App

module S = FStar.Set
module M = Map_extended
module S' = Set_extended

#set-options "--query_stats"

let cf = (int * bool)

// the concrete state type
type concrete_st = M.t nat (M.t nat cf) // element ->
                                       //    replica ID -> 
                                       //       (ctr, flag) //elements & replica ids are unique

// init state
let init_st : concrete_st = M.const (M.const (0, false))

let sel_e (s:concrete_st) e = if M.contains s e then M.sel s e else (M.const (0, false))

let sel_id (s:M.t nat cf) id = if M.contains s id then M.sel s id else (0, false)

let ele_id (s:concrete_st) (e id:nat) =
  M.contains s e /\ M.contains (sel_e s e) id

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  (forall e. M.contains a e = M.contains b e) /\
  (forall e. M.contains a e ==> (forall id. M.contains (sel_e a e) id = M.contains (sel_e b e) id /\ 
                                  sel_id (sel_e a e) id == sel_id (sel_e b e) id))

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

let get_rid (_,(rid,_)) = rid

let get_ele (o:op_t) : nat =
  match snd (snd o) with
  |Add e -> e
  |Rem e -> e
  
// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
 match o with
  |(_, (rid, Add e)) -> M.upd s e (M.upd (sel_e s e) rid (fst (sel_id (sel_e s e) rid) + 1, true))
  |(_, (rid, Rem e)) -> M.iter_upd (fun k v -> if k = e then ((M.map_val (fun (c,f) -> (c, false))) v) else v) s

//conflict resolution
let rc (o1:op_t) (o2:op_t{distinct_ops o1 o2}) =
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
  M.iter_upd (fun k v -> merge_ew (sel_e l k) (sel_e a k) (sel_e b k)) u

/////////////////////////////////////////////////////////////////////////////

let no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3))) = ()

let relaxed_comm (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

let non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) =
  assert (((Add? (snd (snd o1)) /\ Rem? (snd (snd o2)) /\ get_ele o1 = get_ele o2) \/ 
           (Rem? (snd (snd o1)) /\ Add? (snd (snd o2)) /\ get_ele o1 = get_ele o2)) ==>
           ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))); ()
         
let cond_comm (o1:op_t) (o2:op_t{distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2))}) (o3:op_t) =
  if Rem? (snd (snd o3)) && get_ele o1 = get_ele o3 then true else false

let cond_comm_base (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ cond_comm o1 o2 o3)
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

#push-options "--z3rlimit 50 --ifuel 3 --split_queries on_failure"
let cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:log)
  : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ cond_comm o1 o2 o3 /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3)) = ()
          
/////////////////////////////////////////////////////////////////////////////

let merge_comm (l a b:concrete_st)
  : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

let merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s) = ()

let fast_fwd_base (a:concrete_st) (op:op_t)
  : Lemma (ensures eq (do a op) (merge a a (do a op))) = ()

let rec fast_fwd_ind_help (a b:concrete_st) (l:log)
  : Lemma (requires b == apply_log a l)
          (ensures (forall ele rid. fst (sel_id (sel_e b ele) rid) >= fst (sel_id (sel_e a ele) rid)))
          (decreases length l) =
  if length l = 0 then ()
  else (lem_apply_log a l;
        fast_fwd_ind_help a (apply_log a (fst (un_snoc l))) (fst (un_snoc l)))
          
let fast_fwd_ind (a b:concrete_st) (o2 o2':op_t) (l:log)
  : Lemma (requires do b o2 == apply_log a l /\
                    eq (do b o2) (merge a a (do b o2)))
          (ensures eq (do (do b o2') o2) (merge a a (do (do b o2') o2))) =
  fast_fwd_ind_help a (do b o2) l

let rc_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let rc_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

let comm_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o2' o1 /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures ((eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) ==>
                     eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) \/
                    (eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) ==>
                     eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l a (do (do b o2') o2)) o1)))) = 
  assert (eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) ==>
          eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2));
  ()

let comm_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o1' o2 /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                             
          (ensures ((eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2) ==>
                     eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) \/
                    (eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) ==>
                     eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do a o1') (do b o2)) o1)))) =
  assert (eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) ==>
          eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do a o1') (do b o2)) o1));
  ()

let rc_base (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()
  
let comm_base1 (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2)
          (ensures (eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) ==>
                    eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2))) = ()

let comm_base2 (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2)
          (ensures (eq (merge l (do l o1) (do l o2)) (do (do l o2) o1) ==>
                    eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o2) o1))) = ()

let comm_base (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ distinct_ops o o1 /\ distinct_ops o o2)
          (ensures (eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) ==>
                    eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) /\
                   (eq (merge l (do l o1) (do l o2)) (do (do l o2) o1) ==>
                    eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o2) o1))) =
  comm_base1 l o o1 o2;
  comm_base2 l o o1 o2

let rc_intermediate1 (l:concrete_st) (o1 o2 o o':op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\ distinct_ops o' o2)
          (ensures eq (merge (do l o') (do (do l o') o1) (do (do (do l o) o') o2)) (do (do (do (do l o) o') o1) o2)) = ()

let rc_intermediate2 (l l' a b:concrete_st) (o1 o2 o o':op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\ distinct_ops o' o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do l' o1) o2) /\ 
                    eq (merge l (do a o') (do b o)) (do (do l' o) o'))
          (ensures eq (merge (do l o') (do (do a o') o1) (do (do (do b o) o') o2)) (do (do (do (do l' o) o') o1) o2)) = admit()

let rc_intermediate2' (l l' a b:concrete_st) (o1 o2 o o':op_t)
 : Lemma (requires distinct_ops o1 o2 /\ Rem? (snd (snd o1)) /\ Add? (snd (snd o2)) /\ get_ele o1 = get_ele o2 /\ //Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o o' /\ Rem? (snd (snd o)) /\ Add? (snd (snd o')) /\ get_ele o = get_ele o' /\ //Fst_then_snd? (rc o o') /\
                    get_rid o' = get_rid o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do l' o1) o2) /\ 
                    eq (merge l (do a o') (do b o)) (do (do l' o) o'))
          (ensures eq (merge (do l o') (do (do a o') o1) (do (do (do b o) o') o2)) (do (do (do (do l' o) o') o1) o2)) = 
  if get_ele o' = get_ele o2 then () else ()
  
let rc_intermediate2'' (l l' a b:concrete_st) (o1 o2 o o':op_t)
 : Lemma (requires distinct_ops o1 o2 /\ Rem? (snd (snd o1)) /\ Add? (snd (snd o2)) /\ get_ele o1 = get_ele o2 /\ //Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o o' /\ Rem? (snd (snd o)) /\ Add? (snd (snd o')) /\ get_ele o = get_ele o' /\ //Fst_then_snd? (rc o o') /\
                    eq (merge l (do a o1) (do b o2)) (do (do l' o1) o2) /\
                    eq (merge l (do a o') (do b o)) (do (do l' o) o') /\
                    eq (merge (do l o') (do (do a o') o1) (do (do b o') o2)) (do (do (do l' o') o1) o2))
          (ensures eq (merge (do l o') (do (do a o') o1) (do (do (do b o) o') o2)) (do (do (do (do l' o) o') o1) o2)) = 
 if get_ele o' = get_ele o2 then () else ()
          
let comm_intermediate1 (l:concrete_st) (o1 o2 o o' o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\
                    distinct_ops o' o1 /\ distinct_ops o' o2 /\ distinct_ops o3 o1 /\ 
                    eq (do (do l o2) o1) (do (do l o1) o2) /\
                    ~ (exists o3 a'. eq (do l o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do l o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))
          (ensures ((eq (merge l (do l o1) (do l o2)) (do (do l o1) o2) /\
                     eq (merge (do l o') (do (do l o') o1) (do (do (do l o) o') o2)) (do (do (do (do l o) o') o1) o2)) ==>
      eq (merge (do (do l o3) o') (do (do (do l o3) o') o1) (do (do (do (do l o3) o) o') o2)) (do (do (do (do (do l o3) o) o') o1) o2)) /\
                   ((eq (merge l (do l o1) (do l o2)) (do (do l o2) o1) /\
                     eq (merge (do l o') (do (do l o') o1) (do (do (do l o) o') o2)) (do (do (do (do l o) o') o2) o1)) ==>
      eq (merge (do (do l o3) o') (do (do (do l o3) o') o1) (do (do (do (do l o3) o) o') o2)) (do (do (do (do (do l o3) o) o') o2) o1))) = ()

let comm_intermediate2 (l l' a b:concrete_st) (o1 o2 o o':op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ 
                    distinct_ops o o' /\ Fst_then_snd? (rc o o') /\
                    distinct_ops o' o2 /\ distinct_ops o' o1 /\
                    eq (do (do l o2) o1) (do (do l o1) o2) /\ 
                    eq (merge l (do a o') (do b o)) (do (do l' o) o') /\
                    eq (merge l (do a o) (do b o')) (do (do l' o) o') /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    eq (merge (do l o') (do (do l o') o1) (do (do l o) o')) (do (do (do l o) o') o1))
          (ensures (eq (merge l (do a o1) (do b o2)) (do (do l' o1) o2) ==>
                    eq (merge (do l o') (do (do a o') o1) (do (do (do b o) o') o2)) (do (do (do (do l' o) o') o1) o2)) /\
                   (eq (merge l (do a o1) (do b o2)) (do (do l' o2) o1) ==>
                    eq (merge (do l o') (do (do a o') o1) (do (do (do b o) o') o2)) (do (do (do (do l' o) o') o2) o1))) = admit()

////////////////////////////////////////////////////////////////

let inter_merge1 (l:concrete_st) (o o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o3 /\ Fst_then_snd? (rc o3 o1) /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2))
          (ensures eq (merge (do (do l o) o1) (do (do (do l o) o1) o2) (do (do (do l o) o3) o1)) (do (do (do (do l o) o3) o1) o2)) = ()

let inter_merge2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o3 /\ Fst_then_snd? (rc o3 o1) /\ 
                    //distinct_ops o2 o3 /\ Fst_then_snd? (rc o3 o2) /\
                    eq (merge l s (do l o3)) s' /\
                    eq (merge s (do s o2) s') (do s' o2))
          (ensures eq (merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

let inter_merge3 (l a b c:concrete_st) (op op':op_t) 
  : Lemma (requires eq (merge l a b) c /\
                    (forall (o:op_t). eq (merge l a (do b o)) (do c o)))
          (ensures eq (merge l a (do (do b op) op')) (do (do c op) op')) = ()

let inter_merge4 (l s:concrete_st) (o1 o2 o3 o4:op_t)
  : Lemma (requires distinct_ops o1 o3 /\ Fst_then_snd? (rc o3 o1) /\ 
                    distinct_ops o2 o3 /\ Fst_then_snd? (rc o3 o2) /\
                    distinct_ops o1 o4 /\ Fst_then_snd? (rc o4 o1) /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1)) (do (do (do (do s o4) o3) o1) o2)) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
let concrete_st_s = S'.t nat

// init state 
let init_st_s = S'.empty

// apply an operation to a state 
let do_s (st_s:concrete_st_s) (o:op_t) : concrete_st_s =
  match o with
  |(ts, (rid, Add e)) -> S'.add e st_s
  |(_, (rid, Rem e)) -> S'.filter st_s (fun ele -> ele <> e)

// equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  (forall e. S'.mem e st_s <==> (M.contains st e /\ (exists id. snd (sel_id (sel_e st e) id) = true)))

// initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()
  
// equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = 
  if Add? (snd (snd op)) then 
    (if S'.mem (get_ele op) st_s then () else ()) 
  else ()

////////////////////////////////////////////////////////////////

