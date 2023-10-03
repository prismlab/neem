module Orset_rid_map

module M = Map_extended
module S = FStar.Set
module E = Ewflag_rid_map

#set-options "--query_stats"
// the concrete state type
type concrete_st = M.t nat E.concrete_st // element ->
                                       //    replica ID -> 
                                       //       (ctr, flag) //elements & replica ids are unique

let init_st : concrete_st = M.const E.init_st

let sel (s:concrete_st) k = if M.contains s k then M.sel s k else E.init_st

let ele_id (s:concrete_st) (e id:nat) =
  M.contains s e /\ M.contains (sel s e) id
  
let eq (a b:concrete_st) =
  (forall e. M.contains a e = M.contains b e) /\
  (forall e. M.contains a e ==> E.eq (sel a e) (sel b e)) ///\
  //(forall e id. ele_id a e id <==> ele_id b e id)

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
  |Add : nat -> app_op_t 
  |Rem : nat -> app_op_t

type timestamp_t = pos 

type op_t = timestamp_t & (nat (*replica_id*) & app_op_t)

let get_ele (o:op_t) =
  match o with
  |(_,(_,Add ele)) -> ele
  |(_,(_,Rem ele)) -> ele

let get_rid (_,(rid,_)) = rid

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |(_, (rid, Add e)) -> M.upd s e (M.upd (sel s e) rid (fst (E.sel (sel s e) rid) + 1, true))
  |(_, (rid, Rem e)) -> M.iter_upd (fun k v -> if k = get_ele o then ((M.map_val (fun (c,f) -> (c, false))) v) else v) s

type resolve_conflict_res =
  | First_then_second // op2.op1 
  | Second_then_first // op1.op2

let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if get_ele x = get_ele y && Add? (snd (snd x)) && Rem? (snd (snd y)) then First_then_second 
  else Second_then_first

let concrete_merge (lca s1 s2:concrete_st) : concrete_st =  
  let eles = S.union (M.domain lca) (S.union (M.domain s1) (M.domain s2)) in
  let u = M.const_on eles init_st in
  M.iter_upd (fun k v -> E.concrete_merge (sel lca k) (sel s1 k) (sel s2 k)) u

////////////////////////////////////////////////////////////////
//// Linearization properties - intermediate merge //////

let prop1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second)
                    //get_rid o1 = get_rid o2 /\ get_rid o3 <> get_rid o1*))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

#push-options "--z3rlimit 50"
let prop2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o2 <> fst o3 /\ fst o1 <> fst o3 /\
                    eq (concrete_merge l s (do l o3)) s' /\
                    not (resolve_conflict o2 o3 = Second_then_first) /\ 
                    not (resolve_conflict o1 o3 = Second_then_first) /\
                    eq (concrete_merge s (do s o2) s') (do s' o2))
          (ensures eq (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

//prop3 requires case analysis pre-conditions
let prop3 (l a b c:concrete_st) (op op':op_t) 
  : Lemma (requires eq (concrete_merge l a b) c /\ 
              ((Add? (snd (snd op)) /\ Add? (snd (snd op'))) \/
               (Add? (snd (snd op)) /\ Rem? (snd (snd op'))) \/
               (Rem? (snd (snd op)) /\ Add? (snd (snd op'))) \/
               (Rem? (snd (snd op)) /\ Rem? (snd (snd op')))) /\
              (forall (o:op_t). eq (concrete_merge l a (do b o)) (do c o)))
              //fst op <> fst op' /\ get_rid op = get_rid op' /\
          (ensures eq (concrete_merge l a (do (do b op) op')) (do (do c op) op')) = ()

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
  (forall e. M.contains (concrete_merge l a b) e ==>
        (forall id. M.contains (sel (concrete_merge l a b) e) id ==>
               fst (E.sel (sel a e) id) >= fst (E.sel (sel l e) id) /\
               fst (E.sel (sel b e) id) >= fst (E.sel (sel l e) id)))

#push-options "--z3rlimit 100"
let rec_merge (s si si' sn sn':concrete_st)
  : Lemma (requires //merge_pre s sn sn' /\ merge_pre s sn si' /\ merge_pre s si sn' /\ merge_pre s si' sn /\
                    //merge_pre s si si' /\ merge_pre s si' si /\ 
                    merge_pre si sn (concrete_merge s si si') /\ merge_pre si' sn' (concrete_merge s si' si) /\
                    //merge_pre (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn) /\
                    //merge_pre si sn (concrete_merge s si sn') /\ merge_pre si' sn' (concrete_merge s sn si') /\
                    
                    eq (concrete_merge s sn sn') (concrete_merge si sn (concrete_merge s si sn')) /\
                    eq (concrete_merge s sn sn') (concrete_merge si' sn' (concrete_merge s sn si')) /\
                    eq (concrete_merge s sn si') (concrete_merge si sn (concrete_merge s si si')) /\
                    eq (concrete_merge s si sn') (concrete_merge si' sn' (concrete_merge s si' si)))         
          (ensures (eq (concrete_merge s sn sn')
                       (concrete_merge (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn)))) = ()

////////////////////////////////////////////////////////////////
