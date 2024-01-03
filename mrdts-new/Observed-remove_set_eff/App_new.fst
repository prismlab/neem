module App_new

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

type op_t = pos (*timestamp*) & (nat (*replica ID*) & app_op_t)

//let distinct_ops (op1 op2:op_t) = fst op1 =!= fst op2

let get_rid (_,(rid,_)) = rid

type rc_res =
  |Fst_then_snd //o1 -> o2
  |Snd_then_fst //o2 -> o1
  |Either

let get_ele (o:op_t) : nat =
  match snd (snd o) with
  |Add e -> e
  |Rem e -> e
  
// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
 match o with
  |(_, (rid, Add e)) -> M.upd s e (M.upd (sel_e s e) rid (fst (sel_id (sel_e s e) rid) + 1, true))
  |(_, (rid, Rem e)) -> M.iter_upd (fun k v -> if k = e then ((M.map_val (fun (c,f) -> (c, false))) v) else v) s

let commutes_with (o1 o2:op_t) =
  forall s. eq (do (do s o1) o2) (do (do s o2) o1)
  
//conflict resolution
let rc (o1:op_t) (o2:op_t(*{distinct_ops o1 o2}*)) =
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
  : Lemma (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3))) = ()

let relaxed_comm (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

let non_comm (o1 o2:op_t)
  : Lemma (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) =
  assert (((Add? (snd (snd o1)) /\ Rem? (snd (snd o2)) /\ get_ele o1 = get_ele o2) \/ 
           (Rem? (snd (snd o1)) /\ Add? (snd (snd o2)) /\ get_ele o1 = get_ele o2)) ==>
           ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1))); ()
         
let cond_comm (o1:op_t) (o2:op_t{~ (Either? (rc o1 o2))}) (o3:op_t) =
  if Rem? (snd (snd o3)) && get_ele o1 = get_ele o3 then true else false

#push-options "--z3rlimit 100 --max_ifuel 3 --split_queries on_failure"
//#push-options "--z3rlimit 50 --max_ifuel 3"

// let cond_comm_base (s:concrete_st) (o1 o2 o3:op_t)
//   : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ cond_comm o1 o2 o3)
//           (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

// let cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:log)
//   : Lemma (requires distinct_ops o1 o2 /\ ~ (Either? (rc o1 o2)) /\ cond_comm o1 o2 o3 /\
//                     eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
//           (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3)) = ()
          
/////////////////////////////////////////////////////////////////////////////

// Merge commutativity
 let merge_comm (l a b:concrete_st)
   : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

// Merge idempotence
 let merge_idem (s:concrete_st)
   : Lemma (ensures eq (merge s s s) s) = ()

(*Two OP RC*)
//////////////// 
let rc_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
   : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                     eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
           (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let rc_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

//Special case of rc_intermediate_v1
let rc_base (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()

let rc_base_base (o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let rc_intermediate_base_right (l s1 s2 s3:concrete_st) (o o' o1 o2:op_t) 
  : Lemma (requires Fst_then_snd? (rc o o') /\ Fst_then_snd? (rc o1 o2)
                    /\ eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2)
                    /\ eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) 
                    /\ eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2) //***EXTRA*** (from rc_base)
                    /\ eq (merge l (do s1 o') (do s2 o)) (do (do s3 o) o')) //***EXTRA*** 
          (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2)) =
  if get_ele o2 = get_ele o' && get_rid o2 = get_rid o' then () //done
  else if get_ele o2 = get_ele o' && get_rid o2 <> get_rid o' then () //done
  else if get_ele o2 <> get_ele o' && get_rid o2 = get_rid o' then () //done
  else () //done

let rc_intermediate_base_left_right (l s1 s2 s3:concrete_st) (o o' o1' o1 o2:op_t) 
  : Lemma (requires Fst_then_snd? (rc o o') /\ Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o1' o')
                    /\ Either? (rc o o1') //***EXTRA*** 
                    /\ eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2)
                    /\ eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2)) 
        (ensures eq (merge (do l o') (do (do (do s1 o1') o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do (do s3 o1') o) o') o1) o2)) = 
  if get_ele o2 = get_ele o' && get_rid o2 = get_rid o' then () //done
  else if get_ele o2 = get_ele o' && get_rid o2 <> get_rid o' then () //done
  else if get_ele o2 <> get_ele o' && get_rid o2 = get_rid o' then () //done
  else () //done

let rc_intermediate_2_right (l s1 s2 s3:concrete_st) (o1 o2:op_t) (o o':op_t) (o_n:op_t{~ (commutes_with o_n o)})
: Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o o') /\
                  //get_rid o <> get_rid o' (*o,o' must be concurrent *) /\
                  get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                  eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2))
      (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) (do (do (do (do (do s3 o_n) o) o') o1) o2)) = 
  assert (Add? (snd (snd o_n)) /\ get_ele o_n = get_ele o');
  if get_ele o2 = get_ele o' && get_rid o2 = get_rid o' then () //done
  else if get_ele o2 = get_ele o' && get_rid o2 <> get_rid o' then () //done
  else if get_ele o2 <> get_ele o' && get_rid o2 = get_rid o' then () //done
  else () //done

let rc_intermediate_2_left (l s1 s2 s3:concrete_st) (o1 o2:op_t) (o o':op_t) (o_n:op_t{~ (commutes_with o_n o)})
: Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o o') /\
                  //get_rid o <> get_rid o' (*o,o' must be concurrent *) /\
                  get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                  eq (merge (do l o') (do (do (do s1 o) o') o1) (do (do s2 o') o2)) (do (do (do (do s3 o) o') o1) o2))
      (ensures eq (merge (do l o') (do (do (do (do s1 o_n) o) o') o1) (do (do s2 o') o2)) (do (do (do (do (do s3 o_n) o) o') o1) o2)) =
  assert (Add? (snd (snd o_n)) /\ get_ele o_n = get_ele o');
  if get_ele o2 = get_ele o' && get_rid o2 = get_rid o' then () //done
  else if get_ele o2 = get_ele o' && get_rid o2 <> get_rid o' then () //done
  else if get_ele o2 <> get_ele o' && get_rid o2 = get_rid o' then () //done
  else () //done

let rc_intermediate_1_v2 (l s1 s2 s3:concrete_st) (o1 o2:op_t) (o':op_t{Add? (snd (snd o'))}) (o_n:op_t{Add? (snd (snd o_n))})
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    //get_rid o1 <> get_rid o2 /\
                    eq (merge (do l o_n) (do (do s1 o_n) o1) (do (do s2 o_n) o2)) (do (do (do s3 o_n) o1) o2) /\
                    eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2))
    (ensures eq (merge (do (do l o_n) o') (do (do (do s1 o_n) o') o1) (do (do (do s2 o_n) o') o2)) (do (do (do (do s3 o_n) o') o1) o2)) =
  if get_ele o2 = get_ele o' && get_rid o2 = get_rid o' then admit() //not done
  else if get_ele o2 = get_ele o' && get_rid o2 <> get_rid o' then admit() //not done
  else if get_ele o2 <> get_ele o' && get_rid o2 = get_rid o' then admit() //not done
  else admit() //not done

(*One op*)
///////////////
let ind_right_one_op (l a b c:concrete_st) (o1 o1':op_t)
   : Lemma (requires eq (merge l a (do b o1)) (do (merge l a b) o1))
           (ensures eq (merge l a (do (do b o1') o1)) (do (merge l a (do b o1')) o1)) = ()
           
let base_one_op (l:concrete_st) (o o1:op_t)
  : Lemma (requires eq (merge l l (do l o1)) (do l o1))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o1)) (do (do l o) o1) ) = ()

let base_base_one_op (o1:op_t)
  : Lemma (ensures eq (merge init_st init_st (do init_st o1)) (do init_st o1)) = ()

let intermediate_base_right_one_op_right (l s1 s2 s3:concrete_st) (o o' o1:op_t) 
  : Lemma (requires Fst_then_snd? (rc o o') 
                    /\ eq (merge (do l o') (do s1 o') (do (do s2 o') o1)) (do (do s3 o') o1)
                    /\ eq (merge l s1 (do s2 o1)) (do s3 o1)
                    /\ eq (merge l (do s1 o') (do s2 o)) (do (do s3 o) o')) //***EXTRA***
          (ensures eq (merge (do l o') (do s1 o') (do (do (do s2 o) o') o1)) (do (do (do s3 o) o') o1)) = ()

let intermediate_base_right_one_op_left (l s1 s2 s3:concrete_st) (o o' o1:op_t) 
  : Lemma (requires Fst_then_snd? (rc o o') 
                    /\ eq (merge (do l o1) (do (do l o1) o) (do (do l o1) o')) (do (do (do l o1) o) o') //***EXTRA*** (from rc_base)
                    /\ eq (merge (do l o') (do (do s1 o') o1) (do s2 o')) (do (do s3 o') o1)
                    /\ eq (merge l (do s1 o1) s2) (do s3 o1)
                    /\ eq (merge (do l o') (do (do l o') o1) (do (do l o) o')) (do (do (do l o) o') o1) //**EXTRA***
                    /\ eq (merge l (do s1 o') (do s2 o)) (do (do s3 o) o') //***EXTRA***
                    /\ eq (merge l (do s1 o) (do s2 o')) (do (do s3 o) o')) //***EXTRA***
          (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o) o')) (do (do (do s3 o) o') o1)) = 
  let lhs = (merge (do l o') (do (do s1 o') o1) (do (do s2 o) o')) in
  let rhs = (do (do (do s3 o) o') o1) in
  
  if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 = get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 <> get_rid o' then 
    (assume (fst (sel_id (sel_e (do s1 o') (get_ele o1)) (get_rid o1)) >= fst (sel_id (sel_e l (get_ele o1)) (get_rid o1))); //todo
     assert (snd (sel_id (sel_e lhs (get_ele o1)) (get_rid o1)) = snd (sel_id (sel_e rhs (get_ele o1)) (get_rid o1)));
     ())
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 = get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 <> get_rid o' then () //done
  else if Rem? (snd (snd o1)) && get_ele o1 = get_ele o' then ()
  else ()

let intermediate_base_left_one_op (l s1 s2 s3:concrete_st) (o o' o1:op_t) 
  : Lemma (requires Fst_then_snd? (rc o o')  
                    /\ eq (merge (do l o') (do s1 o') (do (do s2 o') o1)) (do (do s3 o') o1)
                    /\ eq (merge l s1 (do s2 o1)) (do s3 o1) 
                    /\ eq (merge l (do s1 o') (do s2 o)) (do (do s3 o) o') //***EXTRA***
                    /\ eq (merge l (do (do s1 o) o') (do s2 o')) (do (do s3 o) o')) //***EXTRA***
          (ensures eq (merge (do l o') (do (do s1 o) o') (do (do s2 o') o1)) (do (do (do s3 o) o') o1)) = 
  if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 = get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 <> get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 = get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 <> get_rid o' then () //done
  else if Rem? (snd (snd o1)) && get_ele o1 = get_ele o' then () //done
  else () //done

let intermediate_base_left_right_one_op (l s1 s2 s3:concrete_st) (o o' o1' o1:op_t) 
  : Lemma (requires Fst_then_snd? (rc o o') /\ Fst_then_snd? (rc o1' o')
                    ///\ get_rid o <> get_rid o' /\ get_rid o1' <> get_rid o' 
                    /\ eq (merge (do l o1) (do (do l o1) o) (do (do l o1) o')) (do (do (do l o1) o) o') //***EXTRA*** (from rc_base)
                    /\ eq (merge (do l o') (do s1 o') (do (do s2 o') o1)) (do (do s3 o') o1)
                    /\ eq (merge (do l o') (do (do s1 o1') o') (do (do s2 o') o1)) (do (do (do s3 o1') o') o1) //EXTRA

                    /\ eq (merge l s1 (do s2 o1)) (do s3 o1) 
                    /\ eq (merge (do l o') (do (do l o') o1) (do (do l o) o')) (do (do (do l o) o') o1) //***EXTRA***
                    /\ eq (merge (do l o') (do l o')  (do (do (do l o) o') o1)) (do (do (do l o) o') o1))
          (ensures eq (merge (do l o') (do (do s1 o1') o') (do (do (do s2 o) o') o1)) (do (do (do (do s3 o1') o) o') o1)) = 
  assert (Either? (rc o o1'));
  let lhs = (merge (do l o') (do (do s1 o1') o') (do (do (do s2 o) o') o1)) in
  let rhs = (do (do (do (do s3 o1') o) o') o1) in
  if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 = get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 <> get_rid o' then 
    (assert (forall ele rid. fst (sel_id (sel_e lhs ele) rid) = fst (sel_id (sel_e rhs ele) rid)); //done
     assert (forall ele rid. snd (sel_id (sel_e lhs ele) rid) = snd (sel_id (sel_e rhs ele) rid)); //done
     ())
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 = get_rid o' then () // done
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 <> get_rid o' then () // done
  else if Rem? (snd (snd o1)) && get_ele o1 = get_ele o' then () // done
  else () // done


(*let intermediate_base_left_right_one_op_right (l s1 s2 s3:concrete_st) (o o' o1' o1:op_t) 
  : Lemma (requires Fst_then_snd? (rc o o') /\ Fst_then_snd? (rc o1' o')
                    /\ eq (merge (do l o') (do s1 o') (do (do s2 o') o1)) (do (do s3 o') o1)
                    /\ eq (merge l s1 (do s2 o1)) (do s3 o1)
                    /\ eq (merge (do l o') (do (do l o') o1) (do (do l o) o')) (do (do (do l o) o') o1)) //***EXTRA***
          (ensures eq (merge (do l o') (do (do s1 o1') o') (do (do (do s2 o) o') o1)) (do (do (do (do s3 o1') o) o') o1)) = admit()

let intermediate_base_left_right_one_op_left (l s1 s2 s3:concrete_st) (o o' o1' o1:op_t) 
  : Lemma (requires Fst_then_snd? (rc o o') /\ Fst_then_snd? (rc o1' o')
                    /\ eq (merge (do l o') (do (do s1 o') o1) (do s2 o')) (do (do s3 o') o1)
                    /\ eq (merge l (do s1 o1) s2) (do s3 o1)
                    /\ eq (merge (do l o') (do (do l o') o1) (do (do l o) o')) (do (do (do l o) o') o1)) //***EXTRA***
          (ensures eq (merge (do l o') (do (do (do s1 o1') o') o1) (do (do s2 o) o')) (do (do (do (do s3 o1') o) o') o1)) = admit()*)

let intermediate_2_right_one_op (l s1 s2 s3:concrete_st) (o1: op_t) (o o':op_t) (o_n:op_t{~ (commutes_with o_n o)})
: Lemma (requires Fst_then_snd? (rc o o') /\
                  //get_rid o <> get_rid o' (*o,o' must be concurrent *) /\
                  get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                  eq (merge (do l o') (do s1 o') (do (do (do s2 o) o') o1)) (do (do (do s3 o) o') o1))
      (ensures eq (merge (do l o') (do s1 o') (do (do (do (do s2 o_n) o) o') o1)) (do (do (do (do s3 o_n) o) o') o1)) = 
  assert (Add? (snd (snd o_n)) && get_ele o_n = get_ele o');
  if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 = get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 <> get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 = get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 <> get_rid o' then () //done
  else if Rem? (snd (snd o1)) && get_ele o1 = get_ele o' then () //done
  else () //done

let intermediate_2_left_one_op (l s1 s2 s3:concrete_st) (o1:op_t) (o o':op_t) (o_n:op_t{~ (commutes_with o_n o)})
: Lemma (requires Fst_then_snd? (rc o o') /\
                  //get_rid o <> get_rid o' (*o,o' must be concurrent *) /\
                  get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                  eq (merge (do l o') (do (do s1 o) o') (do (do s2 o') o1)) (do (do (do s3 o) o') o1))
      (ensures eq (merge (do l o') (do (do (do s1 o_n) o) o') (do (do s2 o') o1)) (do (do (do (do s3 o_n) o) o') o1)) = 
  assert (Add? (snd (snd o_n)) && get_ele o_n = get_ele o');
  if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 = get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 = get_ele o' && get_rid o1 <> get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 = get_rid o' then () //done
  else if Add? (snd (snd o1)) && get_ele o1 <> get_ele o' && get_rid o1 <> get_rid o' then () //done
  else if Rem? (snd (snd o1)) && get_ele o1 = get_ele o' then () //done
  else () //done

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let intermediate_1_v2_one_op (l s1 s2 s3:concrete_st) (o1:op_t) (o':op_t{Add? (snd (snd o'))}) (o_n:op_t{Add? (snd (snd o_n))})
  : Lemma (requires eq (merge (do l o_n) (do s1 o_n) (do (do s2 o_n) o1)) (do (do s3 o_n) o1) /\
                    eq (merge (do l o') (do s1 o') (do (do s2 o') o1)) (do (do s3 o') o1))
          (ensures eq (merge (do (do l o_n) o') (do (do s1 o_n) o') (do (do (do s2 o_n) o') o1)) (do (do (do s3 o_n) o') o1)) = admit()

(*Zero op *)
///////////////
let intermediate_base_right_zero_op (l s1 s2 s3:concrete_st) (o o':op_t) 
  : Lemma (requires Fst_then_snd? (rc o o')  
                    /\ eq (merge (do l o') (do s1 o') (do s2 o')) (do s3 o')
                    /\ eq (merge l s1 s2) s3
                    /\ eq (merge l (do s1 o') (do s2 o)) (do (do s3 o) o')) //***EXTRA***
          (ensures eq (merge (do l o') (do s1 o') (do (do s2 o) o')) (do (do s3 o) o')) = ()

let intermediate_base_left_right_zero_op (l s1 s2 s3:concrete_st) (o o' o1':op_t) 
  : Lemma (requires Fst_then_snd? (rc o o') /\ Fst_then_snd? (rc o1' o')
                    /\ eq (merge (do l o') (do s1 o') (do s2 o')) (do s3 o')
                    /\ eq (merge l s1 s2) s3 ) 
          (ensures eq (merge (do l o') (do (do s1 o1') o') (do (do s2 o) o')) (do (do (do s3 o1') o) o')) = ()

let intermediate_2_right_zero_op (l s1 s2 s3:concrete_st) (o o':op_t) (o_n:op_t{~ (commutes_with o_n o)})
: Lemma (requires Fst_then_snd? (rc o o') /\
                  //get_rid o <> get_rid o' (*o,o' must be concurrent *) /\
                  get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                  eq (merge (do l o') (do s1 o') (do (do s2 o) o')) (do (do s3 o) o'))
      (ensures eq (merge (do l o') (do s1 o') (do (do (do s2 o_n) o) o')) (do (do (do s3 o_n) o) o')) = 
  assert (Fst_then_snd? (rc o o_n) && get_ele o = get_ele o_n);
  assert (Either? (rc o' o_n));
  if get_ele o_n = get_ele o' then () //done
  else ()

let intermediate_2_left_zero_op (l s1 s2 s3:concrete_st) (o o':op_t) (o_n:op_t{~ (commutes_with o_n o)})
: Lemma (requires Fst_then_snd? (rc o o') /\
                  //get_rid o <> get_rid o' (*o,o' must be concurrent *) /\
                  get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                  eq (merge (do l o') (do (do s1 o) o') (do s2 o')) (do (do s3 o) o'))
      (ensures eq (merge (do l o') (do (do (do s1 o_n) o) o') (do s2 o')) (do (do (do s3 o_n) o) o')) = 
  assert (Fst_then_snd? (rc o o_n) && get_ele o = get_ele o_n);
  assert (Either? (rc o' o_n));
  if get_ele o_n = get_ele o' then () //done
  else ()

// In general, the event "o" below should be such that these exists o', (rc o' o)
let intermediate_1_v1_zero_op (l s1 s2 s3:concrete_st) (o:op_t{Add? (snd (snd o))})
  : Lemma (requires eq (merge l s1 s2) s3)
          (ensures eq (merge (do l o) (do s1 o) (do s2 o)) (do s3 o) ) = ()

// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let intermediate_1_v2_zero_op (l s1 s2 s3:concrete_st) (o':op_t{Add? (snd (snd o'))}) (o_n:op_t{Add? (snd (snd o_n))})
  : Lemma (requires eq (merge (do l o_n) (do s1 o_n) (do s2 o_n)) (do s3 o_n)  /\
                    eq (merge (do l o') (do s1 o') (do s2 o')) (do s3 o'))
          (ensures eq (merge (do (do l o_n) o') (do (do s1 o_n) o') (do (do s2 o_n) o')) (do (do s3 o_n) o')) = ()

(* 2 op Comm  *)
///////////////////

let comm_ind_right (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                    //commutes_with o1 o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) )
                    //~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = 
  if Add? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o1 = get_ele o2 then () //done
  else if Add? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o1 <> get_ele o2 && Add? (snd (snd o2')) then () //done
  else if Add? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o1 <> get_ele o2 && Rem? (snd (snd o2')) then () //done
  else if Add? (snd (snd o1)) && Rem? (snd (snd o2)) then () //done
  else if Rem? (snd (snd o1)) && Add? (snd (snd o2)) then () //done
  else ()

let comm_ind_left (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                    //commutes_with o1 o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o2) ==> (eq (merge l (do a o2') (do b o2)) (do (merge l (do a o2') b) o2))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o2')) )
                    //~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o2') o1) (do b o2)) (do (do (merge l (do a o2') b) o2) o1)) = 
  if Add? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o1 = get_ele o2 then () //done
  else if Add? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o1 <> get_ele o2 && Add? (snd (snd o2')) then () //done
  else if Add? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o1 <> get_ele o2 && Rem? (snd (snd o2')) then () //done
  else if Add? (snd (snd o1)) && Rem? (snd (snd o2)) then () //done
  else if Rem? (snd (snd o1)) && Add? (snd (snd o2)) then () //done
  else ()

let comm_base (l:concrete_st) (o o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\
                    //commutes_with o1 o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o2) o1)) = ()

let comm_base_base (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_intermediate_base_right (l s1 s2 s3:concrete_st) (o o' o1 o2:op_t) 
  : Lemma (requires //Fst_then_snd? (rc o o') /\ Either? (rc o1 o2)
                    Rem? (snd (snd o)) /\ Add? (snd (snd o')) /\ get_ele o = get_ele o' /\
                    Add? (snd (snd o1)) /\ Add? (snd (snd o2))
                    /\ eq (merge l (do s1 o1) (do (do s2 o) o2)) (do (do (merge l s1 (do s2 o)) o1) o2) //comes from comm_ind_right
                    /\ eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2) 
                    /\ eq (merge (do l o') (do s1 o') (do (do s2 o) o')) (do (do s3 o) o') //comes from intermediate_base_zero_op
                    /\ eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2)) 
          (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2)) = 
  if Rem? (snd (snd o1)) && Rem? (snd (snd o2)) then admit() //done
  else if Add? (snd (snd o1)) && Rem? (snd (snd o2)) && get_ele o1 = get_ele o' then admit() //done
  else if Add? (snd (snd o1)) && Rem? (snd (snd o2)) && get_ele o1 <> get_ele o' then admit() //done
  else if Rem? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o2 = get_ele o' then admit() //done
  else if Rem? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o2 <> get_ele o' then admit() //done
  
  else if get_ele o1 = get_ele o' && get_ele o2 = get_ele o' && get_rid o1 = get_rid o' && get_rid o2 = get_rid o' then admit() // done
  else if get_ele o1 = get_ele o' && get_ele o2 = get_ele o' && get_rid o1 = get_rid o' && get_rid o2 <> get_rid o' then admit() // done
  else if get_ele o1 = get_ele o' && get_ele o2 = get_ele o' && get_rid o1 <> get_rid o' && get_rid o2 = get_rid o' then admit() // done
  else if get_ele o1 = get_ele o' && get_ele o2 = get_ele o' && get_rid o1 <> get_rid o' && get_rid o2 <> get_rid o' then admit() // not done

  else if get_ele o1 = get_ele o' && get_ele o2 <> get_ele o' && get_rid o1 = get_rid o' && get_rid o2 = get_rid o' then admit() // done
  else if get_ele o1 = get_ele o' && get_ele o2 <> get_ele o' && get_rid o1 = get_rid o' && get_rid o2 <> get_rid o' then admit() // done
  else if get_ele o1 = get_ele o' && get_ele o2 <> get_ele o' && get_rid o1 <> get_rid o' && get_rid o2 = get_rid o' then admit() // done
  else if get_ele o1 = get_ele o' && get_ele o2 <> get_ele o' && get_rid o1 <> get_rid o' && get_rid o2 <> get_rid o' then admit() // not done
  
  else admit() //not done

let comm_intermediate_base_left_right (l s1 s2 s3:concrete_st) (o o' o1' o1 o2:op_t) 
  : Lemma (requires Fst_then_snd? (rc o o') /\ Either? (rc o1 o2) /\ Fst_then_snd? (rc o1' o')
                    /\ eq (merge (do l o') (do (do s1 o') o1) (do (do s2 o') o2)) (do (do (do s3 o') o1) o2)
                    /\ eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2)  
                    /\ eq (merge l (do (do s1 o1') o1) (do (do s2 o) o2)) (do (do (merge l (do s1 o1') (do s2 o)) o1) o2) //comes from comm_ind_right
                    /\ eq (merge (do l o') (do s1 o') (do (do s2 o) o')) (do (do s3 o) o')) //comes from intermediate_base_zero_op

        (ensures eq (merge (do l o') (do (do (do s1 o1') o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do (do s3 o1') o) o') o1) o2)) = admit()

let comm_intermediate_2_right (l s1 s2 s3:concrete_st) (o1 o2:op_t) (o o':op_t) (o_n:op_t)//{~ (commutes_with o_n o)})
: Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc o o') /\
                  //get_rid o <> get_rid o' (*o,o' must be concurrent *) /\
                  get_rid o_n <> get_rid o' (*o_n,o' must be concurrent*) /\
                 // Either? (rc o_n o') /\ 
                  eq (merge (do l o') (do (do s1 o') o1) (do (do (do s2 o) o') o2)) (do (do (do (do s3 o) o') o1) o2))
      (ensures eq (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) (do (do (do (do (do s3 o_n) o) o') o1) o2)) = 
  assume (Either? (rc o_n o') /\ Fst_then_snd? (rc o o') /\ get_ele o = get_ele o');
  let lhs = (merge (do l o') (do (do s1 o') o1) (do (do (do (do s2 o_n) o) o') o2)) in
  let rhs = (do (do (do (do (do s3 o_n) o) o') o1) o2) in
  assume (forall ele. M.contains lhs ele = M.contains rhs ele);
  assume (forall ele. M.contains lhs ele ==> (forall rid. M.contains (sel_e lhs ele) rid = M.contains (sel_e rhs ele) rid));
  admit()

#push-options "--z3rlimit 100 --max_ifuel 5 --split_queries always"
let comm_intermediate_1_v1 (l s1 s2 s3:concrete_st) (o1 o2:op_t) (o:op_t{Add? (snd (snd o))})
  : Lemma (requires Either? (rc o1 o2) /\
                    eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o2) o1) /\ //***EXTRA***
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2))
          (ensures eq (merge (do l o) (do (do s1 o) o1) (do (do s2 o) o2)) (do (do (do s3 o) o1) o2)) = 
  let lhs = (merge (do l o) (do (do s1 o) o1) (do (do s2 o) o2)) in
  let rhs = (do (do (do s3 o) o1) o2) in
  assume (forall ele. M.contains lhs ele = M.contains rhs ele);
  assume (forall ele. M.contains lhs ele ==> (forall rid. M.contains (sel_e lhs ele) rid = M.contains (sel_e rhs ele) rid));
  assume (forall ele rid. (ele <> get_ele o /\ rid <> get_rid o) ==> ( (sel_id (sel_e lhs ele) rid) =  (sel_id (sel_e rhs ele) rid)));
  assume (forall ele rid. (ele <> get_ele o /\ rid = get_rid o) ==> (fst (sel_id (sel_e lhs ele) rid) = fst (sel_id (sel_e rhs ele) rid)));
  assert (forall ele rid. (ele = get_ele o /\ rid <> get_rid o) ==> (fst (sel_id (sel_e lhs ele) rid) = fst (sel_id (sel_e rhs ele) rid)));
  admit()
