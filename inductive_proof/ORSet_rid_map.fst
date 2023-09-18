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

let one_ele (k:nat) v : concrete_st = M.const_on (Set.singleton k) v

let upd_cf (e:E.concrete_st) (rid:nat{M.contains e rid}) (v:E.cf) : E.concrete_st =
  M.upd e rid v

let upd_cf_all (e:E.concrete_st) (v:E.cf) : E.concrete_st =
  M.map_val (fun _ -> v) e

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |(_, (rid, Add e)) -> if M.contains s e && M.contains (sel s e) rid then 
                          M.upd s e (M.upd (sel s e) rid (fst (E.sel (sel s e) rid) + 1, true))
                       else if not (M.contains (sel s e) rid) then
                          M.upd s e (M.concat (E.one_ele rid (1, true)) (sel s e))
                       else M.concat (one_ele e (E.one_ele rid (1, true))) s
  |(_, (rid, Rem e)) -> M.iter_upd (fun k v -> if k = get_ele o then ((M.map_val (fun (c,f) -> (c, false))) v) else v) s
                       //M.upd s e (M.map_val (fun (c,f) -> (c, false)) (sel s e))

let lem_do_add (s:concrete_st) (o:op_t)
  : Lemma (requires Add? (snd (snd o)))
          (ensures (E.sel (sel (do s o) (get_ele o)) (get_rid o) = (fst (E.sel (sel s (get_ele o)) (get_rid o)) + 1, true)) /\
                   (forall e id. ele_id (do s o) e id <==> ele_id s e id \/ (e = get_ele o /\ id = get_rid o)) /\
                   (forall e. M.contains (do s o) e <==> M.contains s e \/ e = get_ele o) (*/\
    (forall e. M.contains s e ==> (forall id. M.contains (sel (do s o) e) id <==> M.contains (sel s e) id \/ id = get_rid o)*))
          [SMTPat (do s o)] = ()

let lem_do_rem (s:concrete_st) (o:op_t)
  : Lemma (requires Rem? (snd (snd o)))
          (ensures (forall e id. ele_id s e id <==> ele_id (do s o) e id) /\
                   (forall e. M.contains s e ==> (forall id. M.contains (sel (do s o) e) id <==> M.contains (sel s e) id)))
          [SMTPat (do s o)] = ()

let concrete_merge (lca s1 s2:concrete_st) : concrete_st =  
  let eles = S.union (M.domain lca) (S.union (M.domain s1) (M.domain s2)) in
  let u = M.const_on eles init_st in
  M.iter_upd (fun k v -> E.concrete_merge (sel lca k) (sel s1 k) (sel s2 k)) u

let lem_merge (lca s1 s2:concrete_st)
  : Lemma (ensures (forall e. M.contains (concrete_merge lca s1 s2) e <==> 
                         M.contains lca e \/ M.contains s1 e \/ M.contains s2 e) /\
                   (forall e id. M.contains (concrete_merge lca s1 s2) e ==>
                         (M.contains (sel (concrete_merge lca s1 s2) e) id <==>
                          M.contains (sel lca e) id \/ M.contains (sel s1 e) id \/ M.contains (sel s2 e) id)))
                   [SMTPat (concrete_merge lca s1 s2)] = ()


#push-options "--z3rlimit 200"
let prop1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o2 /\ fst o2 <> fst o3 /\
                    ((Add? (snd (snd o1)) /\ Add? (snd (snd o3)) /\ Add? (snd (snd o2)))) /\ // \/
                     //(Add? (snd (snd o1)) /\ Rem? (snd (snd o3))) /\
                     //(Rem? (snd (snd o3)))) /\
                    get_rid o1 = get_rid o2 /\ get_rid o3 <> get_rid o1)
                    //resolve_conflict o1 o3 = First_then_second) //o3.o1
                    //not (resolve_conflict o2 o3 = Second_then_first) //not(o2.o3)
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = 
  let lhs = (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) in
  let rhs = (do (do (do l o3) o1) o2) in
  let e1 = get_ele o1 in let e2 = get_ele o2 in let e3 = get_ele o3 in
  let r2 = get_rid o2 in let r1 = get_rid o1 in let r3 = get_rid o3 in
  assert (forall e. M.contains lhs e <==> M.contains rhs e);
  assert (forall e id. ele_id (do l o1) e id <==> ele_id l e id \/ (e = e1 /\ id = r1));
  assert (forall e id. ele_id (do l o3) e id <==> ele_id l e id \/ (e = e3 /\ id = r3));
  assert (forall e id. ele_id (do (do l o1) o2) e id <==> ele_id (do l o1) e id \/ (e = e2 /\ id = r2));
  assert (forall e id. ele_id (do (do l o3) o1) e id <==> ele_id (do l o3) e id \/ (e = e1 /\ id = r1));
  assert (forall e id. ele_id (do (do (do l o3) o1) o2) e id <==> ele_id (do (do l o3) o1) e id \/ (e = e2 /\ id = r2));
  assert (forall e id. ele_id (do (do (do l o3) o1) o2) e id <==> 
                  ele_id l e id \/ (e = e1 /\ id = r1) \/ (e = e2 /\ id = r2) \/ (e = e3 /\ id = r3));
  //assert (forall e id. ele_id (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) e id <==> 
    //              ele_id l e id \/ (e = e1 /\ id = r1) \/ (e = e2 /\ id = r2) \/ (e = e3 /\ id = r3));
  //assert (forall e id. ele_id lhs e id <==> ele_id rhs e id);
  assert (forall e. M.contains lhs e ==> (forall id. M.contains (sel lhs e) id <==> M.contains (sel rhs e) id));
  admit()
  


let idempotence (s:concrete_st) //automatic
  : Lemma (eq (concrete_merge s s s) s) = ()

let prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t) //automatic
  : Lemma (requires //fst o2 <> fst o3 /\ 
                    ((Add? (snd (snd o1)) /\ Add? (snd (snd o3))) \/
                     (Rem? (snd (snd o3)))) /\
                    ((Add? (snd (snd o2)) /\ Add? (snd (snd o3))) \/
                     (Rem? (snd (snd o3)))) /\
                    ((Add? (snd (snd o1)) /\ Add? (snd (snd o3'))) \/
                     (Rem? (snd (snd o3')))) /\
                    ((Add? (snd (snd o2)) /\ Add? (snd (snd o3'))) \/
                     (Rem? (snd (snd o3')))) /\
                    get_rid o1 = get_rid o2 /\ get_rid o3 = get_rid o3' /\
                    //o3.o1, o3'.o1, o3.o2, o3'.o2
                    eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                      (do (do (do (do s o3') o3) o1) o2)) = admit()
                      
let lem_merge4 (s s':concrete_st) (op op':op_t)
  : Lemma (requires get_rid op = get_rid op' /\ 
                    eq (concrete_merge (do s op) (do s' op) (do s op)) (do s' op))
          (ensures eq (concrete_merge (do s op) (do (do s' op') op) (do s op)) (do (do s' op') op)) = admit()

let prop5' (l s s':concrete_st) (o o3:op_t)
  : Lemma (requires eq (concrete_merge s s s') s' /\
                    eq (concrete_merge l s (do l o3)) s' /\
                    get_rid o <> get_rid o3)
          (ensures eq (concrete_merge s s (do s' o)) (do s' o)) = admit() 

let prop3 (s s':concrete_st) (o2 o2':op_t) //done
  : Lemma (requires eq (concrete_merge s s s') s' /\
                    (forall o. eq (concrete_merge s (do s o) s') (do s' o)) /\
                    fst o2 <> fst o2' /\ get_rid o2 = get_rid o2')
          (ensures eq (concrete_merge s (do (do s o2') o2) s') (do (do s' o2') o2)) = ()

let lem_merge3 (l a b c:concrete_st) (op op':op_t) //done
  : Lemma 
    (requires eq (concrete_merge l a b) c /\ 
              //fst op <> fst op' /\ get_rid op = get_rid op' /\
              (forall (o:op_t). eq (concrete_merge l a (do b o)) (do c o)))
    (ensures eq (concrete_merge l a (do (do b op) op')) (do (do c op) op')) = ()
