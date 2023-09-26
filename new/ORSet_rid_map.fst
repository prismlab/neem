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

let prop1 (l:concrete_st) (o1 o2 o3:op_t) // cond1
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second (*/\
                    get_rid o1 = get_rid o2 /\ get_rid o3 <> get_rid o1*))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

#push-options "--z3rlimit 50"
let prop2 (s s':concrete_st) (o1 o2 o3:op_t) //cond2
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second /\
                    eq (concrete_merge s (do s o2) s') (do s' o2)
                    (*get_rid o1 = get_rid o2 /\ get_rid o1 <> get_rid o3*))
          (ensures eq (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

let prop3 (l a b c:concrete_st) (op op':op_t) //cond3
  : Lemma 
    (requires eq (concrete_merge l a b) c /\ 
              ((Add? (snd (snd op)) /\ Add? (snd (snd op'))) \/
               (Add? (snd (snd op)) /\ Rem? (snd (snd op'))) \/
               (Rem? (snd (snd op)) /\ Add? (snd (snd op'))) \/
               (Rem? (snd (snd op)) /\ Rem? (snd (snd op')))) /\
              (forall (o:op_t). eq (concrete_merge l a (do b o)) (do c o)))
              //fst op <> fst op' /\ get_rid op = get_rid op' /\
    (ensures eq (concrete_merge l a (do (do b op) op')) (do (do c op) op')) = ()

let prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t) //automatic //cond5
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o3' /\ fst o2 <> fst o3 /\ fst o2 <> fst o3' /\
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second /\
                    not (resolve_conflict o2 o3' = Second_then_first) /\ //extra ----- check
                    //get_rid o1 = get_rid o2 /\ get_rid o3 = get_rid o3' /\ get_rid o1 <> get_rid o3 /\
                    eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                      (do (do (do (do s o3') o3) o1) o2)) = ()

let merge_pre l a b =
  (forall e. M.contains (concrete_merge l a b) e ==>
        (forall id. M.contains (sel (concrete_merge l a b) e) id ==>
               fst (E.sel (sel a e) id) >= fst (E.sel (sel l e) id) /\
               fst (E.sel (sel b e) id) >= fst (E.sel (sel l e) id)))
               
#push-options "--z3rlimit 200"
let merge_pre' l a b =
  (forall e. M.contains (concrete_merge l a b) e ==>
        (forall id. M.contains (sel (concrete_merge l a b) e) id ==>
               fst (E.sel (sel a e) id) >= fst (E.sel (sel l e) id) /\
               fst (E.sel (sel b e) id) >= fst (E.sel (sel l e) id))) /\
  (forall e id. (E.sel (sel a e) id = E.sel (sel b e) id /\ fst (E.sel (sel l e) id) = fst (E.sel (sel a e) id) /\ 
           snd (E.sel (sel a e) id) = true) ==> snd (E.sel (sel l e) id) = true)

let rec_merge (s si si' sn sn':concrete_st)
  : Lemma (requires //merge_pre' s sn sn' /\ merge_pre' si sn sn' /\ merge_pre' si' sn sn' /\ 
                    //merge_pre' s sn si' /\ merge_pre' s si sn' /\
                    //merge_pre' s si si' /\ merge_pre' s si' si /\ 
                    merge_pre si sn (concrete_merge s si si') /\ merge_pre si' sn' (concrete_merge s si' si) /\
                    //merge_pre' (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn) /\
                    //merge_pre' si sn (concrete_merge s si sn') /\ merge_pre' si' (concrete_merge s sn si') sn' /\
                    
                    eq (concrete_merge s sn sn') (concrete_merge si sn (concrete_merge s si sn')) /\
                    eq (concrete_merge s sn sn') (concrete_merge si' (concrete_merge s sn si') sn') /\
                    eq (concrete_merge s sn si') (concrete_merge si sn (concrete_merge s si si')) /\
                    eq (concrete_merge s si sn') (concrete_merge si' sn' (concrete_merge s si' si)))
         
          (ensures (eq (concrete_merge s sn sn')
                       (concrete_merge (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn)))) = ()
                      
let rec_merge1 (s si si' sn sn':concrete_st)
  : Lemma (requires merge_pre' s sn sn' /\ merge_pre' si sn sn' /\ merge_pre' si' sn sn' /\ 
                    merge_pre' s sn si' /\ merge_pre' s si sn' /\
                    merge_pre' s si si' /\ merge_pre' s si' si /\ 
                    merge_pre' si sn (concrete_merge s si si') /\ merge_pre' si' sn' (concrete_merge s si' si) /\
                    merge_pre' (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn) /\
                    eq (concrete_merge s sn sn') (concrete_merge si sn sn') /\
                    eq (concrete_merge s sn sn') (concrete_merge si' sn sn') /\
                    eq (concrete_merge s sn si') (concrete_merge si sn (concrete_merge s si si')) /\
                    eq (concrete_merge s si sn') (concrete_merge si' sn' (concrete_merge s si' si)))
          (ensures (eq (concrete_merge s sn sn')
                       (concrete_merge (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn)))) = ()
                       
(*#push-options "--z3rlimit 100"
let prop1 (l:concrete_st) (o1 o2 o3:op_t) // cond1
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    not (resolve_conflict o3 o1 = First_then_second) /\
                    not (resolve_conflict o3 o2 = First_then_second) /\
                    get_rid o1 = get_rid o2 (*/\ get_rid o3 <> get_rid o1*))
                    //resolve_conflict o1 o3 = First_then_second) //o3.o1
                    //not (resolve_conflict o2 o3 = Second_then_first) //not(o2.o3)
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

let prop2 (l s s':concrete_st) (o1 o2 o3:op_t) //cond2
  : Lemma (requires eq (concrete_merge s (do s o2) s') (do s' o2) /\
                    fst o1 <> fst o3 /\ fst o2 <> fst o3 /\
                    not (resolve_conflict o3 o1 = First_then_second) /\
                    not (resolve_conflict o3 o2 = First_then_second) /\
                    eq (concrete_merge l s (do l o3)) s'
                    (*get_rid o1 = get_rid o2 /\ get_rid o1 <> get_rid o3*))
          (ensures eq (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()
          
let prop3 (s s':concrete_st) (o2 o2':op_t) 
  : Lemma (requires eq (concrete_merge s s s') s' /\
                    ((Add? (snd (snd o2)) /\ Add? (snd (snd o2'))) \/
                     (Add? (snd (snd o2)) /\ Rem? (snd (snd o2'))) \/
                     (Rem? (snd (snd o2)) /\ Add? (snd (snd o2'))) \/
                     (Rem? (snd (snd o2)) /\ Rem? (snd (snd o2')))) /\
                    (forall o. eq (concrete_merge s (do s o) s') (do s' o)) /\
                    fst o2 <> fst o2' /\ get_rid o2 = get_rid o2')
          (ensures eq (concrete_merge s (do (do s o2') o2) s') (do (do s' o2') o2)) = ()

let lem_merge3 (l a b c:concrete_st) (op op':op_t) //cond3
  : Lemma 
    (requires eq (concrete_merge l a b) c /\ 
              ((Add? (snd (snd op)) /\ Add? (snd (snd op'))) \/
               (Add? (snd (snd op)) /\ Rem? (snd (snd op'))) \/
               (Rem? (snd (snd op)) /\ Add? (snd (snd op'))) \/
               (Rem? (snd (snd op)) /\ Rem? (snd (snd op')))) /\
              //fst op <> fst op' /\ get_rid op = get_rid op' /\
              (forall (o:op_t). eq (concrete_merge l a (do b o)) (do c o)))
    (ensures eq (concrete_merge l a (do (do b op) op')) (do (do c op) op')) = ()

let merge_pre l a b =
  (forall e. M.contains (concrete_merge l a b) e ==>
        (forall id. M.contains (sel (concrete_merge l a b) e) id ==>
               fst (E.sel (sel a e) id) >= fst (E.sel (sel l e) id) /\
               fst (E.sel (sel b e) id) >= fst (E.sel (sel l e) id)))

let prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t)  //cond5
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o3' /\ fst o2 <> fst o3 /\ fst o2 <> fst o3' /\
                    //merge_pre (do l o1) (do (do l o1) o2) (do (do s o3) o1) /\
                    //merge_pre (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1) /\
                    //not (resolve_conflict o3 o1 = First_then_second) /\
                     (resolve_conflict o2 o3 = First_then_second) /\
                     //not (resolve_conflict o3' o1 = First_then_second) /\
                    resolve_conflict o3' o2 = First_then_second /\
                    get_rid o1 = get_rid o2 /\ get_rid o3 = get_rid o3' /\
                    //o3.o1, o3'.o1, o3.o2, o3'.o2
                    eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                      (do (do (do (do s o3') o3) o1) o2)) = ()

let lem_merge4 (s s':concrete_st) (op op':op_t) //cond4
  : Lemma (requires get_rid op = get_rid op' /\
                    merge_pre (do s op) (do s' op) (do s op) /\ //extra pre-cond
                    ((Add? (snd (snd op)) /\ Add? (snd (snd op'))) \/ 
                    (Add? (snd (snd op)) /\ Rem? (snd (snd op'))) \/ 
                    (Rem? (snd (snd op)) /\ Add? (snd (snd op'))) \/ 
                    (Rem? (snd (snd op)) /\ Rem? (snd (snd op')))) /\ 
                    eq (concrete_merge (do s op) (do s' op) (do s op)) (do s' op))
          (ensures eq (concrete_merge (do s op) (do (do s' op') op) (do s op)) (do (do s' op') op)) = ()

let idempotence (s:concrete_st) 
  : Lemma (eq (concrete_merge s s s) s) = ()

let prop5' (l s s':concrete_st) (o o3:op_t)
  : Lemma (requires eq (concrete_merge s s s') s' /\
                    merge_pre s s s' /\
                    //eq (concrete_merge l s (do l o3)) s' /\
                    ((Add? (snd (snd o)) /\ Add? (snd (snd o3))) \/
                    (Add? (snd (snd o)) /\ Rem? (snd (snd o3))) \/
                    (Rem? (snd (snd o)) /\ Add? (snd (snd o3))) \/
                    (Rem? (snd (snd o)) /\ Rem? (snd (snd o3)))) /\
                    get_rid o <> get_rid o3)
          (ensures eq (concrete_merge s s (do s' o)) (do s' o)) = ()*)
