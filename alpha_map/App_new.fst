module App_new

//module S = Set_extended
module M = Map_extended

#set-options "--query_stats"

// concrete state of ew flag
let concrete_st_s = M.t nat (int * bool) //map of rid, (counter, flag)

// init state of ew flag
let init_st_s = M.const (0, false)

let sel (s:concrete_st_s) k = if M.contains s k then M.sel s k else (0, false)

// equivalence relation of ew flag
let eq_s (a b:concrete_st_s) =
  (forall id. (M.contains a id = M.contains b id) /\ (sel a id == sel b id))

let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b) = ()
          
type op_s:eqtype = 
  |Enable 
  |Disable

let do_s (s:concrete_st_s) (o:(nat & (nat & op_s))) : concrete_st_s =
    //{(Enable? (snd (snd o)) ==> (forall rid. rid <> fst (snd o) <==> (sel s rid == sel r rid)))}) =
  match o with
  |_, (rid, Enable) -> M.upd s rid (fst (sel s rid) + 1, true)
  |_, (rid, Disable) -> M.map_val (fun (c,f) -> (c, false)) s

//conflict resolution
let rc (o1:op_t) (o2:op_t(*{distinct_ops o1 o2}*)) =
  match snd (snd o1), snd (snd o2) with
  |Add k1 _, Rem k2 _ -> if k1 = k2 then Snd_then_fst else Either
  |Rem k1 _, Add k2 _ -> if k1 = k2 then Fst_then_snd else Either
  |_ -> Either

let merge_flag (l a b:(int & bool)) : bool =
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
let merge_cf (l a b:(int * bool)) : (int * bool) =
  (fst a + fst b - fst l, merge_flag l a b)
  
// concrete merge operation
let merge_s (l a b:concrete_st_s) : concrete_st_s =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun k v -> merge_cf (sel l k) (sel a k) (sel b k)) u

let pre_op o =
  match o with
  |(_, (rid, Add k Enable)) -> True
  |(_, (rid, Rem k Enable)) -> False
  |(_, (rid, Add k Disable)) -> False
  |(_, (rid, Rem k Disable)) -> True

let distinct_ops_s (op1 op2:(nat & (nat & op_s))) = fst op1 =!= fst op2

let commutes_with_s (o1 o2:(nat & (nat & op_s))) =
  forall s. eq_s (do_s (do_s s o1) o2) (do_s (do_s s o2) o1)

let merge_comm (l a b:concrete_st)
  : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

let merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s) = ()

#push-options "--z3rlimit 50 --max_ifuel 2"
let lemma_do_base (s:concrete_st) (o:op_t)
  : Lemma (requires pre_op o /\ s == init_st)
          (ensures (forall k. k = get_ele o ==> eq_s (sel_k (do s o) k) (do_s (sel_k s k) (get_op_s o)))) = ()

let lemma_do (s:concrete_st) (o1:op_t)
  : Lemma (requires pre_op o1)
          (ensures (forall k. k = get_ele o1 ==> eq_s (sel_k (do s o1) k) (do_s (sel_k s k) (get_op_s o1)))) = ()

let lemma_do1 (s:concrete_st) (o1 o2:op_t)
  : Lemma (requires pre_op o1 /\ pre_op o2)
          (ensures (forall k. k = get_ele o1 /\ get_ele o1 = get_ele o2 ==> 
                         eq_s (sel_k (do (do s o1) o2) k) (do_s (do_s (sel_k s k) (get_op_s o1)) (get_op_s o2)))) = ()
          
(*Two OP RC*)
//////////////// 
#push-options "--z3rlimit 200 --max_ifuel 4"
let rc_ind_right (l a b:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    pre_op o1 /\ pre_op o2' /\ pre_op o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()
          
let rc_ind_left (l a b:concrete_st) (o1 o1' o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    pre_op o1 /\ pre_op o1' /\ pre_op o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

let rc_ind_lca (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    pre_op ol /\ pre_op o1 /\ pre_op o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o1) o2)) = ()

let rc_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ pre_op o1 /\ pre_op o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let rc_inter_base_right (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    pre_op ob /\ pre_op ol /\ pre_op o1 /\ pre_op o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\                 
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let rc_inter_base_left (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\
                    pre_op ob /\ pre_op ol /\ pre_op o1 /\ pre_op o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\
                    eq (merge l (do s1 ob) (do s2 ol)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = ()

let rc_inter_right_s (l s1 s2 s3:concrete_st_s) (o1 o2 ob ol o:(nat & (nat & op_s)))
  : Lemma (requires Disable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\ 
                    Disable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with_s o ob)) \/ (Disable? (snd (snd o)) /\ Enable? (snd (snd ol)))) /\                 
                    eq_s (merge_s (do_s l ol) (do_s (do_s s1 ol) o1) (do_s (do_s (do_s s2 ob) ol) o2)) 
                         (do_s (do_s (do_s (do_s s3 ob) ol) o1) o2))
  (ensures eq_s (merge_s (do_s l ol) (do_s (do_s s1 ol) o1) (do_s (do_s (do_s (do_s s2 o) ob) ol) o2)) 
                (do_s (do_s (do_s (do_s (do_s s3 o) ob) ol) o1) o2)) = ()

#push-options "--z3rlimit 300 --max_ifuel 4"
let rc_inter_right (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ //distinct_ops o1 o2 /\ 
                    Fst_then_snd? (rc ob ol) /\ //distinct_ops ob ol /\ 
                    pre_op o1 /\ pre_op o2 /\ pre_op ob /\ pre_op ol /\ pre_op o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
  (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = 
  
  let e = get_ele o in
  if get_ele o = get_ele o1 then
    (assert (eq_s (sel_k (do (do (do (do s3 ob) ol) o1) o2) e) 
                 (do_s (do_s (do_s (do_s (sel_k s3 e) (get_op_s ob)) (get_op_s ol)) (get_op_s o1)) (get_op_s o2))); 
    rc_inter_right_s (sel_k l e) (sel_k s1 e) (sel_k s2 e) (sel_k s3 e) (get_op_s o1) (get_op_s o2) (get_op_s ob) (get_op_s ol) (get_op_s o))
  else 
    (if get_ele o2 = get_ele ol && get_rid o2 = get_rid ol then () //done
     else if get_ele o2 = get_ele ol && get_rid o2 <> get_rid ol then () //done
     else if get_ele o2 <> get_ele ol && get_rid o2 = get_rid o then () //done
     else ()) //done

let rc_inter_left_s (l s1 s2 s3:concrete_st_s) (o1 o2 ob ol o:(nat & (nat & op_s)))
  : Lemma (requires Disable? (snd (snd o1)) /\ Enable? (snd (snd o2)) /\ 
                    Disable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with_s o ob)) \/ (Disable? (snd (snd o)) /\ Enable? (snd (snd ol)))) /\                 
                    eq_s (merge_s (do_s l ol) (do_s (do_s (do_s s1 ob) ol) o1) (do_s (do_s s2 ol) o2)) 
                         (do_s (do_s (do_s (do_s s3 ob) ol) o1) o2))
  (ensures eq_s (merge_s (do_s l ol) (do_s (do_s (do_s (do_s s1 o) ob) ol) o1) (do_s (do_s s2 ol) o2)) 
                (do_s (do_s (do_s (do_s (do_s s3 o) ob) ol) o1) o2)) = ()
                
let rc_inter_left (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ //distinct_ops o1 o2 /\ 
                    Fst_then_snd? (rc ob ol) /\ //distinct_ops ob ol /\ 
                    pre_op o1 /\ pre_op o2 /\ pre_op ob /\ pre_op ol /\ pre_op o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) =
  let e = get_ele o in
  if get_ele o = get_ele o1 then
  (assert (eq_s (sel_k (do (do (do (do s3 ob) ol) o1) o2) e) 
                (do_s (do_s (do_s (do_s (sel_k s3 e) (get_op_s ob)) (get_op_s ol)) (get_op_s o1)) (get_op_s o2)));
   rc_inter_left_s (sel_k l e) (sel_k s1 e) (sel_k s2 e) (sel_k s3 e) (get_op_s o1) (get_op_s o2) (get_op_s ob) (get_op_s ol) (get_op_s o))
  else 
    (if get_ele o2 = get_ele ol && get_rid o2 = get_rid ol then () //done
     else if get_ele o2 = get_ele ol && get_rid o2 <> get_rid ol then () //done
     else if get_ele o2 <> get_ele ol && get_rid o2 = get_rid o then () //done
     else ()) //done
     
let rc_inter_lca (l s1 s2 s3:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    pre_op o1 /\ pre_op o2 /\ pre_op ol /\ pre_op oi /\ 
                    eq (merge (do l oi) (do (do s1 oi) o1) (do (do s2 oi) o2)) (do (do (do s3 oi) o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do s1 oi) ol) o1) (do (do (do s2 oi) ol) o2)) (do (do (do (do s3 oi) ol) o1) o2)) = ()

(*One op*)
///////////////
let one_op_ind_right (l a b c:concrete_st) (o2 o2':op_t)
   : Lemma (requires pre_op o2 /\ pre_op o2' /\ eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2)) = ()

let one_op_ind_left (l a b c:concrete_st) (o1 o1':op_t)
   : Lemma (requires pre_op o1 /\ pre_op o1' /\ eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) = () 

let one_op_ind_lca (l:concrete_st) (ol o1:op_t)
  : Lemma (requires pre_op ol /\ pre_op o1 /\ eq (merge l (do l o1) l) (do l o1) /\ fst ol < fst o1)
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do l ol)) (do (do l ol) o1)) = ()

let one_op_base (o1:op_t)
  : Lemma (requires pre_op o1)
          (ensures eq (merge init_st (do init_st o1) init_st) (do init_st o1)) = ()

let one_op_inter_base_right (l s1 s2 s3:concrete_st) (ob ol o1:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\
                    pre_op ob /\ pre_op ol /\ pre_op o1 /\
                    eq (merge l s1 (do s2 o1)) (do s3 o1) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ol) o1)) (do (do s3 ol) o1) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do s1 ol) (do (do (do s2 ob) ol) o1)) (do (do (do s3 ob) ol) o1)) = ()

let one_op_inter_base_left (l s1 s2 s3:concrete_st) (ob ol o1:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    pre_op ob /\ pre_op ol /\ pre_op o1 /\
                    eq (merge l s1 (do s2 o1)) (do s3 o1) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ol) o1)) (do (do s3 ol) o1) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol) /\ //***EXTRA***
                    eq (merge l (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol) /\ //***EXTRA***
                    (Fst_then_snd? (rc ob o1) ==> eq (merge l (do s1 o1) (do s2 ob)) (do (merge l s1 (do s2 ob)) o1))) //***EXTRA*** 
          (ensures eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1)) = ()

let one_op_inter_right (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    pre_op o1 /\ pre_op ob /\ pre_op ol /\ pre_op o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ob) ol) ) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 o) ob) ol) ) (do (do (do (do s3 o) ob) ol) o1)) = ()

let one_op_inter_left (l s1 s2 s3:concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    pre_op o1 /\ pre_op ob /\ pre_op ol /\ pre_op o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do (do s2 ol) o1)) (do (do (do s3 ob) ol) o1))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do (do s2 ol) o1)) (do (do (do (do s3 o) ob) ol) o1)) = ()

let one_op_inter_lca (l s1 s2 s3:concrete_st) (o1 ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    pre_op o1 /\ pre_op ol /\ pre_op oi /\
                    eq (merge (do l oi) (do s1 oi) (do (do s2 oi) o1)) (do (do s3 oi) o1) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ol) o1)) (do (do s3 ol) o1))
          (ensures eq (merge (do (do l oi) ol) (do (do s1 oi) ol) (do (do (do s2 oi) ol) o1)) (do (do (do s3 oi) ol) o1)) = admit()

(*Zero op *)
///////////////

let zero_op_inter_base_right (l s1 s2 s3:concrete_st) (ob ol:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    pre_op ob /\ pre_op ol /\
                    eq (merge l s1 s2) s3 /\
                    eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol) /\
                    eq (merge l (do s1 ol) (do s2 ob)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol)) = ()

let zero_op_inter_base_left (l s1 s2 s3:concrete_st) (ob ol:op_t) 
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    pre_op ob /\ pre_op ol /\
                    eq (merge l s1 s2) s3 /\
                    eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol) /\
                    eq (merge l (do s1 ob) (do s2 ol)) (do (do s3 ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol)) = ()

let zero_op_inter_right (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    pre_op ob /\ pre_op ol /\ pre_op o /\
                    //get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do s1 ol) (do (do (do s2 o) ob) ol)) (do (do (do s3 o) ob) ol)) = ()

let zero_op_inter_left (l s1 s2 s3:concrete_st) (ob ol o:op_t)
  : Lemma (requires distinct_ops ob ol /\ Fst_then_snd? (rc ob ol) /\ 
                    pre_op ob /\ pre_op ol /\ pre_op o /\
                    //get_rid o <> get_rid ol (*o_n,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol))
          (ensures eq (merge (do l ol) (do (do (do s1 o) ob) ol) (do s2 ol)) (do (do (do s3 o) ob) ol)) = ()

let zero_op_inter_lca_v1 (l s1 s2 s3:concrete_st) (ol:op_t)
  : Lemma (requires pre_op ol /\ (exists o'. Fst_then_snd? (rc o' ol)) /\ eq (merge l s1 s2) s3)
          (ensures eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol)) = ()

let zero_op_inter_lca_v2 (l s1 s2 s3:concrete_st) (ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\
                    pre_op ol /\ pre_op oi /\ 
                    eq (merge (do l oi) (do s1 oi) (do s2 oi)) (do s3 oi)  /\
                    eq (merge (do l ol) (do s1 ol) (do s2 ol)) (do s3 ol))
          (ensures eq (merge (do (do l oi) ol) (do (do s1 oi) ol) (do (do s2 oi) ol)) (do (do s3 oi) ol)) = ()

(* 2 op Comm  *)
///////////////////

#push-options "--z3rlimit 400 --max_ifuel 4"
let comm_ind_right_s (l a b c:concrete_st_s) (o1 o2' o2:(nat & (nat & op_s)))
  : Lemma (requires ((Disable? (snd (snd o1)) /\ Disable? (snd (snd o2))) \/ (Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)))) /\
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s (merge_s l a b) o2) o1) /\
                    ((Disable? (snd (snd o2')) /\ Enable? (snd (snd o1))) ==>
                      eq_s (merge_s l (do_s a o1) (do_s b o2')) (do_s (merge_s l a (do_s b o2')) o1)) /\
                    //~ (exists o3 a'. eq_s (do_s a o1) (do_s a' o3) /\ Disable? (snd (snd o2)) /\ Enable? (snd (snd o3))) /\
                    ~ (Disable? (snd (snd o1)) /\ Enable? (snd (snd o2'))) )
                    //~ (exists o3 b'. eq_s (do_s (do_s b o2') o2) (do_s b' o3) /\ Disable? (snd (snd o1)) /\ Enable? (snd (snd o3))) /\
                    //~ (exists o3 b'. eq_s (do_s b o2) (do_s b' o3) /\ Disable? (snd (snd o1)) /\ Enable? (snd (snd o3))))
          (ensures eq_s (merge_s l (do_s a o1) (do_s (do_s b o2') o2)) (do_s (do_s (merge_s l a (do_s b o2')) o2) o1)) = ()
          
let comm_ind_right (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ //distinct_ops o1 o2 /\ distinct_ops o2' o1 /\
                    pre_op o1 /\ pre_op o2' /\ pre_op o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) /\
                    ~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    ~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = 
  let e = get_ele o2' in
  if e = get_ele o1 && get_ele o1 = get_ele o2 then 
    (assert (eq_s (sel_k (do (do (merge l a b) o2) o1) e) 
                 (do_s (do_s (sel_k (merge l a b) e) (get_op_s o2)) (get_op_s o1))); 
    if ((Disable? (snd (snd (get_op_s o1))) && Disable? (snd (snd (get_op_s o2)))) ||
       (Enable? (snd (snd (get_op_s o1))) && Enable? (snd (snd (get_op_s o2))))) &&
       not (Disable? (snd (snd (get_op_s o1))) && Enable? (snd (snd (get_op_s o2')))) then
    comm_ind_right_s (sel_k l e) (sel_k a e) (sel_k b e) (sel_k c e) (get_op_s o1) (get_op_s o2') (get_op_s o2) //done
    else if Rem? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o1 <> get_ele o2 then () //done
    else if Add? (snd (snd o1)) && Rem? (snd (snd o2)) && get_ele o1 <> get_ele o2 then () //done
    else ())
  else if e = get_ele o1 && get_ele o1 <> get_ele o2 then () //done
  else if e <> get_ele o1 && get_ele o1 = get_ele o2 then () //done
  else () //done
  
let comm_ind_left_s (l a b c:concrete_st_s) (o1 o2' o2:(nat & (nat & op_s)))
  : Lemma (requires ((Disable? (snd (snd o1)) /\ Disable? (snd (snd o2))) \/ (Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)))) /\
                    eq_s (merge_s l (do_s a o1) (do_s b o2)) (do_s (do_s (merge_s l a b) o2) o1) /\
                    ((Disable? (snd (snd o2')) /\ Enable? (snd (snd o2))) ==>
                      eq_s (merge_s l (do_s a o2') (do_s b o2)) (do_s (merge_s l (do_s a o2') b) o2)) /\
                    //~ (exists o3 a'. eq_s (do_s a o1) (do_s a' o3) /\ Disable? (snd (snd o2)) /\ Enable? (snd (snd o3))) /\
                    ~ (Disable? (snd (snd o2)) /\ Enable? (snd (snd o2'))) )
                    //~ (exists o3 b'. eq_s (do_s (do_s b o2') o2) (do_s b' o3) /\ Disable? (snd (snd o1)) /\ Enable? (snd (snd o3))) /\
                    //~ (exists o3 b'. eq_s (do_s b o2) (do_s b' o3) /\ Disable? (snd (snd o1)) /\ Enable? (snd (snd o3))))
          (ensures eq_s (merge_s l (do_s (do_s a o2') o1) (do_s b o2)) (do_s (do_s (merge_s l (do_s a o2') b) o2) o1)) = ()

let comm_ind_left (l a b c:concrete_st) (o1 o2' o2:op_t)
  : Lemma (requires (*distinct_ops o1 o2 /\*) Either? (rc o1 o2) /\ //distinct_ops o2' o2 /\
                    pre_op o1 /\ pre_op o2' /\ pre_op o2 /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o2) ==> (eq (merge l (do a o2') (do b o2)) (do (merge l (do a o2') b) o2))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o2')) )
                    //~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o2') o1) (do b o2)) (do (do (merge l (do a o2') b) o2) o1)) = 
  let e = get_ele o2' in
  if e = get_ele o1 && get_ele o1 = get_ele o2 then 
    (assert (eq_s (sel_k (do (do (merge l a b) o2) o1) e) 
                 (do_s (do_s (sel_k (merge l a b) e) (get_op_s o2)) (get_op_s o1))); 
    if ((Disable? (snd (snd (get_op_s o1))) && Disable? (snd (snd (get_op_s o2)))) ||
       (Enable? (snd (snd (get_op_s o1))) && Enable? (snd (snd (get_op_s o2))))) &&
       not (Disable? (snd (snd (get_op_s o2))) && Enable? (snd (snd (get_op_s o2')))) then
    comm_ind_left_s (sel_k l e) (sel_k a e) (sel_k b e) (sel_k c e) (get_op_s o1) (get_op_s o2') (get_op_s o2) //done
    else if Rem? (snd (snd o1)) && Add? (snd (snd o2)) && get_ele o1 <> get_ele o2 then () //done
    else if Add? (snd (snd o1)) && Rem? (snd (snd o2)) && get_ele o1 <> get_ele o2 then () //done
    else ())
  else if e = get_ele o1 && get_ele o1 <> get_ele o2 then () //done
  else if e <> get_ele o1 && get_ele o1 = get_ele o2 then () //done
  else () //done

let comm_ind_lca (l:concrete_st) (ol o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ distinct_ops ol o1 /\ distinct_ops ol o2 /\ distinct_ops o1 o2 /\ 
                    pre_op ol /\ pre_op o1 /\ pre_op o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Either? (rc o1 o2) /\ pre_op o1 /\ pre_op o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_inter_base_right_s (l s1 s2 s3:concrete_st_s) (ob ol o1 o2:(nat & (nat & op_s)))
  : Lemma (requires Disable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\
                    ((Disable? (snd (snd o1)) /\ Disable? (snd (snd o2))) \/ (Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)))) /\
                    eq_s (merge_s l (do_s s1 o1) (do_s s2 o2)) (do_s (do_s s3 o1) o2) /\
                    eq_s (merge_s (do_s l ol) (do_s (do_s s1 ol) o1) (do_s (do_s s2 ol) o2)) (do_s (do_s (do_s s3 ol) o1) o2) /\ 
                    eq_s (merge_s l (do_s s1 o1) (do_s (do_s s2 ob) o2)) (do_s (do_s (merge_s l s1 (do_s s2 ob)) o1) o2) /\ 
                    eq_s (merge_s (do_s l ol) (do_s s1 ol) (do_s (do_s s2 ob) ol)) (do_s (do_s s3 ob) ol))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s s1 ol) o1) (do_s (do_s (do_s s2 ob) ol) o2)) 
                        (do_s (do_s (do_s (do_s s3 ob) ol) o1) o2)) = ()
          
let comm_inter_base_right (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ //distinct_ops ob ol /\ 
                    Either? (rc o1 o2) /\ //distinct_ops o1 o2 /\ 
                    //distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    pre_op ob /\ pre_op ol /\ pre_op o1 /\ pre_op o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\ 
                    eq (merge l (do s1 o1) (do (do s2 ob) o2)) (do (do (merge l s1 (do s2 ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do s1 ol) (do (do s2 ob) ol)) (do (do s3 ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = //ob
  let e = get_ele ob in
  if e = get_ele o1 && get_ele o1 = get_ele o2 then
    (assert (eq_s (sel_k (do (do (do s3 ol) o1) o2) e) 
                 (do_s (do_s (do_s (sel_k s3 e) (get_op_s ol)) (get_op_s o1)) (get_op_s o2))); 
    if ((Disable? (snd (snd (get_op_s o1))) && Disable? (snd (snd (get_op_s o2)))) ||
       (Enable? (snd (snd (get_op_s o1))) && Enable? (snd (snd (get_op_s o2))))) &&
         Disable? (snd (snd (get_op_s ob))) && Enable? (snd (snd (get_op_s ol))) then
       comm_inter_base_right_s (sel_k l e) (sel_k s1 e) (sel_k s2 e) (sel_k s3 e) (get_op_s ob) (get_op_s ol) (get_op_s o1) (get_op_s o2)
    else ())
  else if e = get_ele o1 && get_ele o1 <> get_ele o2 then () //done
  else if e <> get_ele o1 && get_ele o1 = get_ele o2 then () //done
  else () //done
  
let comm_inter_base_left_s (l s1 s2 s3:concrete_st_s) (ob ol o1 o2:(nat & (nat & op_s)))
  : Lemma (requires Disable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\
                    ((Disable? (snd (snd o1)) /\ Disable? (snd (snd o2))) \/ (Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)))) /\
                    eq_s (merge_s l (do_s s1 o1) (do_s s2 o2)) (do_s (do_s s3 o1) o2) /\
                    eq_s (merge_s (do_s l ol) (do_s (do_s s1 ol) o1) (do_s (do_s s2 ol) o2)) (do_s (do_s (do_s s3 ol) o1) o2) /\ 
                    eq_s (merge_s l (do_s (do_s s1 ob) o1) (do_s s2 o2)) (do_s (do_s (merge_s l (do_s s1 ob) s2) o1) o2) /\ 
                    eq_s (merge_s (do_s l ol) (do_s (do_s s1 ob) ol) (do_s s2 ol)) (do_s (do_s s3 ob) ol))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s (do_s s1 ob) ol) o1) (do_s (do_s s2 ol) o2)) 
                        (do_s (do_s (do_s (do_s s3 ob) ol) o1) o2)) = ()
                        
let comm_inter_base_left (l s1 s2 s3:concrete_st) (ob ol o1 o2:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ //distinct_ops ob ol /\ 
                    Either? (rc o1 o2) /\ //distinct_ops o1 o2 /\ 
                    //distinct_ops ol o1 /\ distinct_ops ol o2 /\
                    pre_op ob /\ pre_op ol /\ pre_op o1 /\ pre_op o2 /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2) /\ 
                    eq (merge l (do (do s1 ob) o1) (do s2 o2)) (do (do (merge l (do s1 ob) s2) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do s1 ob) ol) (do s2 ol)) (do (do s3 ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2)) = 
  let e = get_ele ob in
  if e = get_ele o1 && get_ele o1 = get_ele o2 then
    (assert (eq_s (sel_k (do (do (do s3 ol) o1) o2) e) 
                 (do_s (do_s (do_s (sel_k s3 e) (get_op_s ol)) (get_op_s o1)) (get_op_s o2))); 
    if ((Disable? (snd (snd (get_op_s o1))) && Disable? (snd (snd (get_op_s o2)))) ||
       (Enable? (snd (snd (get_op_s o1))) && Enable? (snd (snd (get_op_s o2))))) &&
         Disable? (snd (snd (get_op_s ob))) && Enable? (snd (snd (get_op_s ol))) then
       comm_inter_base_left_s (sel_k l e) (sel_k s1 e) (sel_k s2 e) (sel_k s3 e) (get_op_s ob) (get_op_s ol) (get_op_s o1) (get_op_s o2)
    else ())
  else if e = get_ele o1 && get_ele o1 <> get_ele o2 then () //done
  else if e <> get_ele o1 && get_ele o1 = get_ele o2 then () //done
  else () //done

let comm_inter_right_s (l s1 s2 s3:concrete_st_s) (o1 o2 ob ol o:(nat & (nat & op_s)))
  : Lemma (requires Disable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\
                    ((Disable? (snd (snd o1)) /\ Disable? (snd (snd o2))) \/ (Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((Disable? (snd (snd o)) /\ Disable? (snd (snd ol))) \/ (Enable? (snd (snd o)) /\ Enable? (snd (snd ol)))) /\
                    ((~ (commutes_with_s o ob)) \/ (Disable? (snd (snd o)) /\ Enable? (snd (snd ol)))) /\  
                    eq_s (merge_s (do_s l ol) (do_s (do_s s1 ol) o1) (do_s (do_s (do_s s2 ob) ol) o2)) 
                         (do_s (do_s (do_s (do_s s3 ob) ol) o1) o2))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s s1 ol) o1) (do_s (do_s (do_s (do_s s2 o) ob) ol) o2)) 
                        (do_s (do_s (do_s (do_s (do_s s3 o) ob) ol) o1) o2)) = () 

#push-options "--z3rlimit 400 --max_ifuel 5"
let comm_inter_right (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ //distinct_ops o1 o2 /\ 
                    Fst_then_snd? (rc ob ol) /\ //distinct_ops ob ol /\ 
                    pre_op o1 /\ pre_op o2 /\ pre_op ob /\ pre_op ol /\ pre_op o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    distinct_ops o ol /\ Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do s2 ob) ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do (do (do s2 o) ob) ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) = 
  let e = get_ele o in
  if e = get_ele o1 && get_ele o1 = get_ele o2 then 
    (assert (eq_s (sel_k (do (do (do (do s3 ob) ol) o1) o2) e) 
                 (do_s (do_s (do_s (do_s (sel_k s3 e) (get_op_s ob)) (get_op_s ol)) (get_op_s o1)) (get_op_s o2))); 
    if ((Disable? (snd (snd (get_op_s o1))) && Disable? (snd (snd (get_op_s o2)))) ||
       (Enable? (snd (snd (get_op_s o1))) && Enable? (snd (snd (get_op_s o2))))) &&
         Disable? (snd (snd (get_op_s ob))) && Enable? (snd (snd (get_op_s ol))) then
       comm_inter_right_s (sel_k l e) (sel_k s1 e) (sel_k s2 e) (sel_k s3 e) (get_op_s o1) (get_op_s o2) (get_op_s ob) (get_op_s ol) (get_op_s o)
    else ())
  else if e = get_ele o1 && get_ele o1 <> get_ele o2 then () //done
  else if e <> get_ele o1 && get_ele o1 = get_ele o2 then () //done
  else if get_ele o1 = get_ele ol then ()
  else ()

let comm_inter_left_s (l s1 s2 s3:concrete_st_s) (o1 o2 ob ol o:(nat & (nat & op_s)))
  : Lemma (requires Disable? (snd (snd ob)) /\ Enable? (snd (snd ol)) /\
                    ((Disable? (snd (snd o1)) /\ Disable? (snd (snd o2))) \/ (Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((Disable? (snd (snd o)) /\ Disable? (snd (snd ol))) \/ (Enable? (snd (snd o)) /\ Enable? (snd (snd ol)))) /\
                    ((~ (commutes_with_s o ob)) \/ (Disable? (snd (snd o)) /\ Enable? (snd (snd ol)))) /\  
                    eq_s (merge_s (do_s l ol) (do_s (do_s (do_s s1 ob) ol) o1) (do_s (do_s s2 ol) o2)) 
                         (do_s (do_s (do_s (do_s s3 ob) ol) o1) o2))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s (do_s (do_s s1 o) ob) ol) o1) (do_s (do_s s2 ol) o2)) 
                        (do_s (do_s (do_s (do_s (do_s s3 o) ob) ol) o1) o2)) = () 

let comm_inter_left (l s1 s2 s3:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\  //distinct_ops o1 o2 /\ 
                     Fst_then_snd? (rc ob ol) /\ //distinct_ops ob ol /\
                    pre_op o1 /\ pre_op o2 /\ pre_op ob /\ pre_op ol /\ pre_op o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    distinct_ops o ol /\ Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do s1 ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do s3 ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do s1 o) ob) ol) o1) (do (do s2 ol) o2)) (do (do (do (do (do s3 o) ob) ol) o1) o2)) =
  admit()

let comm_inter_lca_s (l s1 s2 s3:concrete_st_s) (o1 o2 ol o':(nat & (nat & op_s)))
  : Lemma (requires ((Disable? (snd (snd o1)) /\ Disable? (snd (snd o2))) \/ (Enable? (snd (snd o1)) /\ Enable? (snd (snd o2)))) /\
                    Disable? (snd (snd o')) /\ Enable? (snd (snd ol)) /\
                    eq_s (merge_s l (do_s s1 o1) (do_s s2 o2)) (do_s (do_s s3 o1) o2))
          (ensures eq_s (merge_s (do_s l ol) (do_s (do_s s1 ol) o1) (do_s (do_s s2 ol) o2)) (do_s (do_s (do_s s3 ol) o1) o2)) =()
          
let comm_inter_lca' (l s1 s2 s3:concrete_st) (o1 o2 ol o':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ //distinct_ops ol o1 /\ distinct_ops ol o2 /\ distinct_ops o1 o2 /\ 
                    (exists o'. Fst_then_snd? (rc o' ol)) /\
                    pre_op o1 /\ pre_op o2 /\ pre_op ol /\
                    eq (merge l (do s1 o1) (do s2 o2)) (do (do s3 o1) o2))
          (ensures eq (merge (do l ol) (do (do s1 ol) o1) (do (do s2 ol) o2)) (do (do (do s3 ol) o1) o2)) = 
  admit()

