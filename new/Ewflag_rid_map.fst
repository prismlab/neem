module Ewflag_rid_map

module M = Map_extended
module S = FStar.Set

#set-options "--query_stats"
let cf = (int * bool)

// the concrete state type
type concrete_st = M.t nat cf // (replica_id, ctr, flag) //replica ids are unique
 
let init_st : concrete_st = M.const (0, false)

let sel (s:concrete_st) k = if M.contains s k then M.sel s k else (0, false)

let eq (a b:concrete_st) =
  (forall id. M.contains a id = M.contains b id /\
         sel a id == sel b id)

// few properties of equivalence relation
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
  |Enable 
  |Disable

type timestamp_t = pos 

type op_t = timestamp_t & (nat (*replica_id*) & app_op_t)

let get_rid (_,(rid,_)) = rid

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |(_, (rid, Enable)) -> M.upd s rid (fst (sel s rid) + 1, true) 
  |(_, (rid, Disable)) -> M.map_val (fun (c,f) -> (c, false)) s 

type resolve_conflict_res =
  | First_then_second // op2.op1 
  | Second_then_first // op1.op2

let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if Enable? (snd (snd x)) && Disable? (snd (snd y)) then First_then_second else Second_then_first
  
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
let merge_cf (lca s1 s2:cf) : cf =
  (fst s1 + fst s2 - fst lca, merge_flag lca s1 s2)

let concrete_merge (lca s1 s2:concrete_st) : concrete_st =  
  let keys = S.union (M.domain lca) (S.union (M.domain s1) (M.domain s2)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun k v -> merge_cf (sel lca k) (sel s1 k) (sel s2 k)) u

////////////////////////////////////////////////////////////////
//// Linearization properties - intermediate merge //////

let prop1 (l:concrete_st) (o1 o2 o3:op_t) 
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second)
                    //get_rid o1 = get_rid o2 /\ get_rid o3 <> get_rid o1*)
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()
          
let prop2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o2 <> fst o3 /\ fst o1 <> fst o3 /\
                    eq (concrete_merge l s (do l o3)) s' /\ 
                    not (resolve_conflict o2 o3 = Second_then_first) /\
                    not (resolve_conflict o1 o3 = Second_then_first) /\
                    eq (concrete_merge s (do s o2) s') (do s' o2))
          (ensures eq (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

//prop3 requires either case analysis preconditions (or)
//                      comment out the case analysis pre-cond and do case analysis 
//                      on the proof like "if Disable? (snd (snd op)) then () else ()"
let prop3 (l a b c:concrete_st) (op op':op_t)
  : Lemma (requires eq (concrete_merge l a b) c /\ 
              (*(Enable? (snd (snd op)) /\ Enable? (snd (snd op'))) \/
               (Enable? (snd (snd op)) /\ Disable? (snd (snd op'))) \/
               (Disable? (snd (snd op)) /\ Enable? (snd (snd op'))) \/
               (Disable? (snd (snd op)) /\ Disable? (snd (snd op')))) /\*)
              (forall (o:op_t). eq (concrete_merge l a (do b o)) (do c o)))
              //fst op <> fst op' /\ get_rid op = get_rid op' /\
          (ensures eq (concrete_merge l a (do (do b op) op')) (do (do c op) op')) = 
  if Disable? (snd (snd op)) then () else ()

let prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o3' /\ fst o2 <> fst o3 /\ fst o2 <> fst o3' /\
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second /\
                    resolve_conflict o1 o3' = First_then_second /\
                    eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
                    //get_rid o1 = get_rid o2 /\ get_rid o3 = get_rid o3' /\
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                      (do (do (do (do s o3') o3) o1) o2)) = ()

////////////////////////////////////////////////////////////////
//// Recursive merge condition //////

let merge_pre l a b =
  (forall id. M.contains (concrete_merge l a b) id ==>
         fst (sel a id) >= fst (sel l id) /\
         fst (sel b id) >= fst (sel l id))
         
let rec_merge (s si si' sn sn':concrete_st)
  : Lemma (requires //merge_pre s sn sn' /\ merge_pre s sn si' /\ merge_pre s si sn' /\ merge_pre s si' sn /\
                    //merge_pre s si si' /\ merge_pre s si' si /\ 
                    merge_pre si sn (concrete_merge s si si') /\ merge_pre si' sn' (concrete_merge s si' si) /\
                    //merge_pre (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn) /\
                    //merge_pre si sn (concrete_merge s si sn') /\ merge_pre si' sn' (concrete_merge s sn si') /\
                    
                    eq (concrete_merge s sn sn') (concrete_merge si sn (concrete_merge s si sn')) /\
                    eq (concrete_merge s sn sn') (concrete_merge si' sn' (concrete_merge s sn si')) /\
                    //eq (concrete_merge s sn si') (concrete_merge si sn (concrete_merge s si si')) /\
                    eq (concrete_merge s si sn') (concrete_merge si' sn' (concrete_merge s si' si)))         
          (ensures (eq (concrete_merge s sn sn')
                       (concrete_merge (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn)))) = ()
          
////////////////////////////////////////////////////////////////
