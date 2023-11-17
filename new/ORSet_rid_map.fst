module Orset_rid_map

module M = Map_extended
module S = FStar.Set
open SeqUtils
open FStar.Seq
open FStar.Ghost
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

let get_rid (_,(rid,_)) = rid

type log = seq op_t

let mem_rid (rid:nat) (l:log) =
  exists e. mem e l /\ fst (snd e) = rid

unfold
let ( ++ ) (l1 l2:log) = Seq.append l1 l2

unfold
let mem_id (id:timestamp_t) (l:log) : bool =
  mem_assoc_fst id l
  
unfold
let distinct_ops (l:log) = distinct_assoc_fst l

type st0 = concrete_st & erased log
  
let v_of (s:st0) : concrete_st = fst s
let ops_of (s:st0) : GTot log = snd s

let get_ele (o:op_t) =
  match o with
  |(_,(_,Add ele)) -> ele
  |(_,(_,Rem ele)) -> ele

// apply an operation to a state
let do (s:concrete_st) (o:op_t) 
  : (r:concrete_st{(forall rid e. e <> get_ele o ==> E.sel (sel r e) rid = E.sel (sel s e) rid) /\
                   (Add? (snd (snd o)) ==> (forall e. M.contains r e <==> M.contains s e \/ e = get_ele o) /\
                                   (forall e. e = get_ele o ==> E.sel (sel r e) (get_rid o) = (fst (E.sel (sel s e) (get_rid o)) + 1, true))) /\
                   (Rem? (snd (snd o)) ==> (forall e. M.contains r e <==> M.contains s e) /\
                                   (forall e rid. e = get_ele o ==> E.sel (sel r e) rid = (fst (E.sel (sel s e) rid), false)))}) =
  match o with
  |(_, (rid, Add e)) -> M.upd s e (M.upd (sel s e) rid (fst (E.sel (sel s e) rid) + 1, true))
  |(_, (rid, Rem e)) -> M.iter_upd (fun k v -> if k = get_ele o then ((M.map_val (fun (c,f) -> (c, false))) v) else v) s

#push-options "--ifuel 3"
let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()
#pop-options

// applying a log of operations to a concrete state
let rec apply_log (x:concrete_st) (l:log) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |_ -> apply_log (do x (head l)) (tail l)                   

// property of apply_log
let rec lem_apply_log (x:concrete_st) (l:log)
  : Lemma (ensures (length l > 0 ==> apply_log x l == do (apply_log x (fst (un_snoc l))) (last l)))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_apply_log (do x (head l)) (tail l)

#push-options "--z3rlimit 50 --ifuel 3"
let rec lem_apply (x:concrete_st) (l:log)
  : Lemma (ensures (let r = apply_log x l in
                        //(forall rid. M.contains r rid ==> M.contains x rid \/ mem_rid rid l) /\
                        (forall ele. M.contains x ele ==> M.contains r ele) /\
                        (forall ele. M.contains x ele ==> (forall rid. M.contains (sel x ele) rid ==> M.contains (sel r ele) rid)) /\ 
                        (forall ele rid. M.contains x ele /\ M.contains (sel x ele) rid ==> fst (E.sel (sel r ele) rid) >= fst (E.sel (sel x ele) rid))))
                        //(forall rid. fst (sel r rid) >= fst (sel x rid))))
          (decreases length l) =
          //[SMTPat (apply_log x l)] =
  match length l with
  |0 -> ()
  |_ -> lem_apply (do x (head l)) (tail l)
#pop-options

type st1 = s:st0{(v_of s == apply_log init_st (ops_of s))}

let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  (v_of s == apply_log init_st (ops_of s))

type st = s:st0{valid_st s}

type resolve_conflict_res =
  | First_then_second // op2.op1 
  | Second_then_first // op1.op2

let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if get_ele x = get_ele y && Add? (snd (snd x)) && Rem? (snd (snd y)) then First_then_second 
  else Second_then_first

let concrete_merge (lca s1 s2:concrete_st) 
  : (r:concrete_st{(forall e. M.contains r e <==> M.contains lca e \/ M.contains s1 e \/ M.contains s2 e) /\
                   (forall e rid. E.sel (sel r e) rid = E.sel (E.concrete_merge (sel lca e) (sel s1 e) (sel s2 e)) rid)}) =  
  let eles = S.union (M.domain lca) (S.union (M.domain s1) (M.domain s2)) in
  let u = M.const_on eles init_st in
  M.iter_upd (fun k v -> E.concrete_merge (sel lca k) (sel s1 k) (sel s2 k)) u

//operations x and y are commutative
let commutative (x y:op_t) =
  not (((Add? (snd (snd x)) && Rem? (snd (snd y)) && get_ele x = get_ele y) ||
        (Add? (snd (snd y)) && Rem? (snd (snd x)) && get_ele x = get_ele y))) 

let comm_symmetric (x y:op_t) 
  : Lemma (requires commutative x y)
          (ensures commutative y x) = ()
          
// if x and y are commutative ops, applying them in any order should give equivalent results
let commutative_prop (x y:op_t) 
  : Lemma (requires commutative x y)
          (ensures (forall s. eq (apply_log s (cons x (cons y empty))) (apply_log s (cons y (cons x empty))))) = ()

//commutativity for a sequence of operation
let commutative_seq (x:op_t) (l:log) : bool =
  forallb (fun e -> commutative x e) l

let comm_empty_log (x:op_t) (l:log)
  : Lemma (ensures length l = 0 ==> commutative_seq x l) = ()
  
let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{(v_of s == do (v_of i) (last (ops_of s))) /\
               (ops_of i = fst (un_snoc (ops_of s))) /\
               (ops_of s = snoc (ops_of i) (last (ops_of s))) /\
               is_prefix (ops_of i) (ops_of s) /\
               (forall id. mem_id id (ops_of i) <==> mem_id id (ops_of s) /\ id <> fst (last (ops_of s)))}) =
  let p,_ = un_snoc (ops_of s) in
  let r = apply_log init_st p in
  lem_apply_log init_st (ops_of s);
  let p, l = un_snoc (ops_of s) in
  let r = apply_log init_st p in
  lemma_split (ops_of s) (length (ops_of s) - 1); 
  lemma_append_count_assoc_fst p (snd (split (ops_of s) (length (ops_of s) - 1))); 
  distinct_invert_append p (snd (split (ops_of s) (length (ops_of s) - 1)));
  (r, hide p)

//currently present in App.fsti as Log MRDT needs it
let rec inverse_helper (s:concrete_st) (l':log) (op:op_t)
  : Lemma (ensures (let l = Seq.snoc l' op in 
                   (apply_log s l == do (apply_log s l') op))) 
          (decreases length l')
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |_ -> inverse_helper (do s (head l')) (tail l') op
  
//currently present in App.fsti as Log MRDT needs it
let rec split_prefix (s:concrete_st) (l:log) (a:log)
  : Lemma (requires is_prefix l a)
          (ensures (apply_log s a == apply_log (apply_log s l) (diff a l)) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) == (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |_ -> split_prefix (do s (head l)) (tail l) (tail a)

let consistent_branches (lca s1 s2:st1) =
  distinct_ops (ops_of lca) /\ distinct_ops (ops_of s1) /\ distinct_ops (ops_of s2) /\
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  (forall id id1. mem_id id (ops_of lca) ==> not (mem_id id1 (diff (ops_of s1) (ops_of lca)))) /\
  (forall id id1. mem_id id (ops_of lca) ==> not (mem_id id1 (diff (ops_of s2) (ops_of lca)))) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
  (forall rid. mem_rid rid (diff (ops_of s1) (ops_of lca)) ==> ~ (mem_rid rid (diff (ops_of s2) (ops_of lca))))

let consistent_branches_s1_gt0 (lca s1 s2:st1) =
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca)

let consistent_branches_s2_gt0 (lca s1 s2:st1) =
  consistent_branches lca s1 s2 /\
  length (ops_of s2) > length (ops_of lca)

let consistent_branches_s1s2_gt0 (lca s1 s2:st1) =
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca) /\
  length (ops_of s2) > length (ops_of lca)

let do_st (s:st1) (o:op_t) : st1 =
  split_prefix init_st (ops_of s) (snoc (ops_of s) o); 
  (do (v_of s) o, hide (snoc (ops_of s) o))

#push-options "--z3rlimit 50 --ifuel 3"
let merge_is_comm (lca s1 s2:st)
  : Lemma (requires true) //consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = ()
                       
let lem_trans_merge_s1' (lca s1 s2 s1':concrete_st)
  : Lemma (requires eq s1 s1')
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1' s2)) = ()

let lem_trans_merge_s2' (lca s1 s2 s2':concrete_st)
  : Lemma (requires eq s2 s2')
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1 s2')) = ()

#push-options "--z3rlimit 100 --ifuel 5 --split_queries always"
let lin_rc_ind_s1'_pre (lca s1 s2:st) (last1 last2:op_t) =
  length (ops_of s1) > length (ops_of lca) /\ //get_rid last1 <> get_rid last2 /\
  Rem? (snd (snd last1)) /\ Add? (snd (snd last2)) /\ get_ele last1 = get_ele last2 /\
  (let s1' = inverse_st s1 in
  eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
     (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)))
                       
let lin_rc_ind_s1'_req (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires lin_rc_ind_s1'_pre lca s1 s2 last1 last2 /\ 
                    (let _, last1' = un_snoc (ops_of s1) in
                     Rem? (snd (snd last1')) /\ get_ele last1' = get_ele last1))                         
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_rc_ind_s1'_rneq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires lin_rc_ind_s1'_pre lca s1 s2 last1 last2 /\ 
                    (let _, last1' = un_snoc (ops_of s1) in
                     Rem? (snd (snd last1')) /\ get_ele last1' <> get_ele last1))                         
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_rc_ind_s1'_aeq (lca s1 s2:st) (last1 last2:op_t) //takes time
  : Lemma (requires lin_rc_ind_s1'_pre lca s1 s2 last1 last2 /\ 
                    (let _, last1' = un_snoc (ops_of s1) in
                     Add? (snd (snd last1')) /\ get_ele last1' = get_ele last1))                         
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_rc_ind_s1'_aneq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires lin_rc_ind_s1'_pre lca s1 s2 last1 last2 /\ 
                    (let _, last1' = un_snoc (ops_of s1) in
                     Add? (snd (snd last1')) /\ get_ele last1' <> get_ele last1))                         
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()
                           
let lin_rc_ind_s1' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires lin_rc_ind_s1'_pre lca s1 s2 last1 last2)                        
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let _, last1' = un_snoc (ops_of s1) in
  if Rem? (snd (snd last1')) && get_ele last1' = get_ele last1 then lin_rc_ind_s1'_req lca s1 s2 last1 last2
  else if Rem? (snd (snd last1')) && get_ele last1' <> get_ele last1 then lin_rc_ind_s1'_rneq lca s1 s2 last1 last2
  else if Add? (snd (snd last1')) && get_ele last1' = get_ele last1 then lin_rc_ind_s1'_aeq lca s1 s2 last1 last2
  else lin_rc_ind_s1'_aneq lca s1 s2 last1 last2

let lin_rc_ind_s2'_pre (lca s1 s2:st) (last1 last2:op_t) =
  length (ops_of s2) > length (ops_of lca) /\ //get_rid last1 <> get_rid last2 /\
  Rem? (snd (snd last1)) /\ Add? (snd (snd last2)) /\ get_ele last1 = get_ele last2 /\
  (let s2' = inverse_st s2 in
  eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
     (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)))

let lin_rc_ind_s2'_req (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires lin_rc_ind_s2'_pre lca s1 s2 last1 last2 /\ 
                    (let _, last2' = un_snoc (ops_of s2) in
                     Rem? (snd (snd last2')) /\ get_ele last2' = get_ele last2))                         
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_rc_ind_s2'_rneq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires lin_rc_ind_s2'_pre lca s1 s2 last1 last2 /\ 
                    (let _, last2' = un_snoc (ops_of s2) in
                     Rem? (snd (snd last2')) /\ get_ele last2' <> get_ele last2))                         
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_rc_ind_s2'_aeq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires lin_rc_ind_s2'_pre lca s1 s2 last1 last2 /\ 
                    (let _, last2' = un_snoc (ops_of s2) in
                     Add? (snd (snd last2')) /\ get_ele last2' = get_ele last2))                         
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_rc_ind_s2'_aneq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires lin_rc_ind_s2'_pre lca s1 s2 last1 last2 /\ 
                    (let _, last2' = un_snoc (ops_of s2) in
                     Add? (snd (snd last2')) /\ get_ele last2' <> get_ele last2))                         
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()
                           
let lin_rc_ind_s2' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires lin_rc_ind_s2'_pre lca s1 s2 last1 last2)                           
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let _, last2' = un_snoc (ops_of s2) in
  if Rem? (snd (snd last2')) && get_ele last2' = get_ele last2 then lin_rc_ind_s2'_req lca s1 s2 last1 last2
  else if Rem? (snd (snd last2')) && get_ele last2' <> get_ele last2 then lin_rc_ind_s2'_rneq lca s1 s2 last1 last2
  else if Add? (snd (snd last2')) && get_ele last2' = get_ele last2 then lin_rc_ind_s2'_aeq lca s1 s2 last1 last2
  else lin_rc_ind_s2'_aneq lca s1 s2 last1 last2
                      
let rec lin_rc (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\ 
                    //fst last1 <> fst last2 /\
                    //get_rid last1 <> get_rid last2 /\
                    Rem? (snd (snd last1)) /\ Add? (snd (snd last2)) /\ get_ele last1 = get_ele last2) //rc last1 last2 
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1); length (ops_of s2)]) =
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then () //done
  else if ops_of s1 = ops_of lca then 
    (let s2' = inverse_st s2 in
     assume (consistent_branches lca s1 s2'); //can be done
     lin_rc lca s1 s2' last1 last2;
     lin_rc_ind_s2' lca s1 s2 last1 last2) //done
  else 
    (let s1' = inverse_st s1 in
     assume (consistent_branches lca s1' s2); //can be done
     lin_rc lca s1' s2 last1 last2;
     lin_rc_ind_s1' lca s1 s2 last1 last2) //done
#pop-options

let reorder (last_op:op_t) (l:log)
  : (b:bool{b = true <==> (exists op. mem op l /\ fst last_op <> fst op /\
                         (let pre,suf = pre_suf l op in
                          not (commutative last_op op) /\
                          First_then_second? (resolve_conflict op last_op) /\
                          //Second_then_first? (resolve_conflict last_op op) /\
                          commutative_seq op suf))}) =
  existsb (fun (op:op_t) -> mem op l &&  fst last_op <> fst op &&
                         (let pre,suf = pre_suf l op in
                          not (commutative last_op op) &&
                          First_then_second? (resolve_conflict op last_op) &&
                          //Second_then_first? (resolve_conflict last_op op) &&
                          commutative_seq op suf)) l

#push-options "--z3rlimit 50 --ifuel 3"
let lin_comm_ind_r1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    Rem? (snd (snd last2)) /\ Rem? (snd (snd last1)) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let lin_comm_ind_r2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    Rem? (snd (snd last2)) /\ Add? (snd (snd last1)) /\ get_ele last1 <> get_ele last2 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let lin_comm_ind_r (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    Rem? (snd (snd last2)) /\ 
                    (Rem? (snd (snd last1)) \/ (Add? (snd (snd last1)) /\ get_ele last1 <> get_ele last2)) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  if Rem? (snd (snd last1)) then lin_comm_ind_r1 lca s1 s2 last1 last2
  else lin_comm_ind_r2 lca s1 s2 last1 last2

#push-options "--z3rlimit 50 --ifuel 3"
let rec lin_comm_r (lca s1 s2:st) (last1 last2:op_t)
    : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                      consistent_branches lca s1 s2 /\
                      get_rid last1 <> get_rid last2 /\
                      Rem? (snd (snd last2)) /\
                      ((Rem? (snd (snd last1))) \/ (Add? (snd (snd last1)) /\ get_ele last1 <> get_ele last2)) /\
                      not (reorder last2 (diff (snoc (ops_of s1) last1) (ops_of lca))))
            (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
            (decreases length (ops_of s1)) =
    if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then () //done
    else if ops_of s1 = ops_of lca then () //done
    else 
      (let _, last1' = un_snoc (ops_of s1) in
       let s1' = inverse_st s1 in
       assume (v_of s1 == do (v_of s1') last1');
       assume (get_rid last1' <> get_rid last2);
       assume (consistent_branches lca s1' s2); //can be done
       assume (consistent_branches lca s1 (do_st s2 last2)); //can be done
       assume ((Rem? (snd (snd last1'))) \/ (Add? (snd (snd last1')) /\ get_ele last1' <> get_ele last2));
       assume (not (reorder last2 (diff (ops_of s1) (ops_of lca)))); //can be done
       lin_comm_r lca s1' s2 last1' last2;         
       lin_comm_ind_r lca s1 s2 last1 last2)

let lin_comm_ind_a1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    Add? (snd (snd last2)) /\ Add? (snd (snd last1)) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let lin_comm_ind_a2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    Add? (snd (snd last2)) /\ Rem? (snd (snd last1)) /\ get_ele last1 <> get_ele last2 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let lin_comm_ind_a (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    Add? (snd (snd last2)) /\ 
                    ((Add? (snd (snd last1))) \/ (Rem? (snd (snd last1)) /\ get_ele last1 <> get_ele last2)) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  if Add? (snd (snd last1)) then lin_comm_ind_a1 lca s1 s2 last1 last2
  else lin_comm_ind_a2 lca s1 s2 last1 last2

#push-options "--z3rlimit 100 --ifuel 5 --split_queries always"
(*let lin_comm_ind_a3_aeq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Add? (snd (snd last1)) /\ 
                    //get_ele last1 = get_ele last2 /\ //done
                    //get_ele last1 <> get_ele last2 /\ //NOT DONE
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     get_rid last1 <> get_rid last2' /\
                     Add? (snd (snd last2')) /\ get_ele last2' = get_ele last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  assume (forall e. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e = 
               M.contains (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e);
  assume ((forall e. e <> get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e)));
  assume ((forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e)));
  ()*)

let lin_comm_ind_a3_aneq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Add? (snd (snd last1)) /\ 
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     //get_rid last1 <> get_rid last2' /\
                     Add? (snd (snd last2')) /\ get_ele last2' <> get_ele last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_comm_ind_a3_rneq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Add? (snd (snd last1)) /\ 
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     //get_rid last1 <> get_rid last2' /\
                     Rem? (snd (snd last2')) /\ get_ele last2' <> get_ele last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_comm_ind_a3_req (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Add? (snd (snd last1)) /\ 
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     //get_rid last1 <> get_rid last2' /\
                     Rem? (snd (snd last2')) /\ get_ele last2' = get_ele last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let merge_pre_ext l a b =
  (forall e. M.contains l e ==> M.contains a e /\ M.contains b e) /\
  (forall e id. M.contains l e /\ M.contains (sel l e) id ==> M.contains (sel a e) id /\ M.contains (sel b e) id) /\
  (forall e. M.contains (concrete_merge l a b) e ==>
        (forall id. M.contains (sel (concrete_merge l a b) e) id ==>
               fst (E.sel (sel a e) id) >= fst (E.sel (sel l e) id) /\
               fst (E.sel (sel b e) id) >= fst (E.sel (sel l e) id)))
               
let lin_comm_ind_a3_aeq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Add? (snd (snd last1)) /\ 
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     //get_rid last1 <> get_rid last2' /\
                     Add? (snd (snd last2')) /\ get_ele last2' = get_ele last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = 
  assert (forall e rid. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e /\ 
              rid <> get_rid last2 ==> E.sel (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid =
                                      E.sel (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid);
  assert (forall e rid. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e /\ 
              rid = get_rid last2 ==> fst (E.sel (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid) =
                                      fst (E.sel (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid));
  assert (forall e rid. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e /\ 
              rid = get_rid last2 ==> snd (E.sel (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid) =
                                      snd (E.sel (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid));
  ()

let lin_comm_ind_a3 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Add? (snd (snd last1)) /\ 
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     //get_rid last1 <> get_rid last2' /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2))) =
  let _, last2' = un_snoc (ops_of s2) in
  if Rem? (snd (snd last2')) && get_ele last2' = get_ele last2 then lin_comm_ind_a3_req lca s1 s2 last1 last2
  else if Rem? (snd (snd last2')) && get_ele last2' <> get_ele last2 then lin_comm_ind_a3_rneq lca s1 s2 last1 last2
  else if Add? (snd (snd last2')) && get_ele last2' = get_ele last2 then lin_comm_ind_a3_aeq lca s1 s2 last1 last2
  else lin_comm_ind_a3_aneq lca s1 s2 last1 last2

let lin_comm_ind_a4_aneq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Rem? (snd (snd last1)) /\ get_ele last1 <> get_ele last2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     //get_rid last1 <> get_rid last2' /\
                     Add? (snd (snd last2')) /\ get_ele last2' <> get_ele last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_comm_ind_a4_aeq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Rem? (snd (snd last1)) /\ get_ele last1 <> get_ele last2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     //get_rid last1 <> get_rid last2' /\
                     Add? (snd (snd last2')) /\ get_ele last2' = get_ele last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_comm_ind_a4_rneq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Rem? (snd (snd last1)) /\ get_ele last1 <> get_ele last2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     //get_rid last1 <> get_rid last2' /\
                     Rem? (snd (snd last2')) /\ get_ele last2' <> get_ele last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()

let lin_comm_ind_a4_req (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\ 
                    Add? (snd (snd last2)) /\ Rem? (snd (snd last1)) /\ get_ele last1 <> get_ele last2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     //get_rid last1 <> get_rid last2' /\
                     Rem? (snd (snd last2')) /\ get_ele last2' = get_ele last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures (forall e. e = get_ele last2 /\ M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==> 
                      E.eq (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) 
                           (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e))) = ()
                           
let lin_comm_ind_a4 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\
                    Add? (snd (snd last2)) /\ Rem? (snd (snd last1)) /\ get_ele last1 <> get_ele last2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let _, last2' = un_snoc (ops_of s2) in
  if Rem? (snd (snd last2')) && get_ele last2' = get_ele last2 then lin_comm_ind_a4_req lca s1 s2 last1 last2
  else if Rem? (snd (snd last2')) && get_ele last2' <> get_ele last2 then lin_comm_ind_a4_rneq lca s1 s2 last1 last2
  else if Add? (snd (snd last2')) && get_ele last2' = get_ele last2 then lin_comm_ind_a4_aeq lca s1 s2 last1 last2
  else lin_comm_ind_a4_aneq lca s1 s2 last1 last2

let lin_comm_ind1_a (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires get_rid last1 <> get_rid last2 /\
                    ops_of s1 = ops_of lca /\
                    Add? (snd (snd last2)) /\ 
                    ((Add? (snd (snd last1))) \/ (Rem? (snd (snd last1)) /\ get_ele last1 <> get_ele last2)) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =
  if Add? (snd (snd last1)) then lin_comm_ind_a3 lca s1 s2 last1 last2
  else lin_comm_ind_a4 lca s1 s2 last1 last2
                        
let rec lin_comm_a (lca s1 s2:st) (last1 last2:op_t)
    : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                      consistent_branches lca s1 s2 /\
                      get_rid last1 <> get_rid last2 /\
                      Add? (snd (snd last2)) /\
                      ((Add? (snd (snd last1))) \/ (Rem? (snd (snd last1)) /\ get_ele last1 <> get_ele last2)) /\
                      not (reorder last2 (diff (snoc (ops_of s1) last1) (ops_of lca))))
            (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
            (decreases %[length (ops_of s2); length (ops_of s1)]) =
    if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then () //done
    else if ops_of s1 = ops_of lca then 
      (let s2' = inverse_st s2 in
       assume (consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
               consistent_branches lca s1 s2'); //can be done
       lin_comm_a lca s1 s2' last1 last2;
       lin_comm_ind1_a lca s1 s2 last1 last2)
    else 
      (let _, last1' = un_snoc (ops_of s1) in
       let s1' = inverse_st s1 in
       assume (v_of s1 == do (v_of s1') last1');
       assume (get_rid last1' <> get_rid last2);
       assume (consistent_branches lca s1' s2); //can be done
       assume (consistent_branches lca s1 (do_st s2 last2)); //can be done
       assume ((Add? (snd (snd last1'))) \/ (Rem? (snd (snd last1')) /\ get_ele last1' <> get_ele last2));
       assume (not (reorder last2 (diff (ops_of s1) (ops_of lca)))); //can be done
       lin_comm_a lca s1' s2 last1' last2;
       lin_comm_ind_a lca s1 s2 last1 last2)

#push-options "--z3rlimit 100 --split_queries always"
let linearizable_gt0_s2' (lca s1 s2:st)
  : Lemma (requires //consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (length (ops_of s1) > length (ops_of lca) /\
                     length (ops_of s2) > length (ops_of lca) /\
                     (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     get_rid last1 <> get_rid last2 /\
                     Rem? (snd (snd last1)) /\ Add? (snd (snd last2)) /\ get_ele last1 = get_ele last2)))
                     //not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     //not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     //Second_then_first? (resolve_conflict last1 last2) /\
                     //consistent_branches lca s1 (inverse_st s2)))
        
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = ()
                       
let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca)
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = admit()

let pre1_pre2_s2 (lca s1 s2:st)
    : Lemma (requires consistent_branches_s2_gt0 lca s1 s2)
            (ensures consistent_branches lca s1 (inverse_st s2)) = 
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2);
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  assume (forall rid. mem_rid rid (diff (ops_of s1) (ops_of lca)) ==> ~ (mem_rid rid (diff (fst (un_snoc (ops_of s2))) (ops_of lca)))); ()

let pre1_pre2_s1 (lca s1 s2:st)
    : Lemma (requires consistent_branches_s1_gt0 lca s1 s2)
            (ensures consistent_branches lca (inverse_st s1) s2) = 
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s1);
  inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
  assume (forall rid. mem_rid rid (diff (fst (un_snoc (ops_of s1))) (ops_of lca)) ==> ~ (mem_rid rid (diff (ops_of s2) (ops_of lca)))); ()


                              
let lem_exists (lastop:op_t) (l:log)
  : Lemma (requires true)
          (ensures exists_triple lastop l <==> (Rem? (snd (snd lastop)) /\
                   (exists op. mem op l /\ Add? (snd (snd op)) /\ get_ele op = get_ele lastop /\ fst op <> fst lastop /\
                    (let _, suf = pre_suf l op in
                    (forall r. mem r suf /\ get_ele r = get_ele lastop ==> Add? (snd (snd r)))))))
  = ()

let fst_t (f,_,_) = f
let snd_t (_,s,_) = s
let thr_t (_,_,t) = t

// returns an operation op in l such that
// 1. last_op and op are non-commutative
// 2. op is commutative with all the operations in the suffix of l
// 3. op should be applied after last_op according to resolve_conflict
#push-options "--z3rlimit 200" 
let rec find_op (last_op:op_t) (l l1:log)
  : Pure op_t
         (requires length l > 0 /\ length l1 > 0 /\
                   (exists op. mem op l /\ mem op l1 /\ 
                          fst last_op <> fst op /\ 
                          not (commutative last_op op) /\
                          Second_then_first? (resolve_conflict last_op op) /\
                          (let _, suf = pre_suf l1 op in
                          commutative_seq op suf)))
         (ensures (fun op -> mem op l /\ mem op l1 /\ 
                          fst last_op <> fst op /\
                          not (commutative last_op op) /\
                          Second_then_first? (resolve_conflict last_op op) /\
                          (let _, suf = pre_suf l1 op in
                          commutative_seq op suf))) (decreases length l) =

 match length l with
  |1 -> last l
  |_ -> let pre, op = un_snoc l in
       if (mem op l1 && fst last_op <> fst op &&
           not (commutative last_op op) &&
           Second_then_first? (resolve_conflict last_op op) &&
           (let _, suf = pre_suf l1 op in
            commutative_seq op suf)) then op 
        else (lemma_mem_snoc pre op;
              find_op last_op pre l1)
              
// returns a triple such that 
// 1. l = (snoc prefix op) ++ suffix
// 2. last_op and op are non-commutative
// 3. op is commutative with all the operations in the suffix of l
// 4. op should be applied after last_op according to resolve_conflict
let find_triple (last_op:op_t) (l:log{(exists_triple last_op l)}) 
  : (t:(log & op_t & log) {mem (snd_t t) l /\ (fst_t t, thr_t t) = pre_suf l (snd_t t) /\
                                is_prefix (fst_t t) l /\ is_suffix (thr_t t) l /\
                                Seq.equal l ((Seq.snoc (fst_t t) (snd_t t)) ++ (thr_t t)) /\
                                length l = length (fst_t t) + 1 + length (thr_t t) /\

                                fst last_op <> fst (snd_t t) /\
                                not (commutative last_op (snd_t t)) /\
                                Second_then_first? (resolve_conflict last_op (snd_t t)) /\
                                commutative_seq (snd_t t) (thr_t t)}) =
  let op = find_op last_op l l in
  let pre, suf = pre_suf l op in
  (pre, op, suf)

let lem_eq_is_equiv_st (x:concrete_st) (a b:log)
  : Lemma (requires (a == b /\ apply_log x a == apply_log x b))
          (ensures eq (apply_log x a) (apply_log x b))
          [SMTPat (eq (apply_log x a) (apply_log x b))] = 
  eq_is_equiv (apply_log x a) (apply_log x b)
  
let lem_eq_is_equiv (a b:log)
  : Lemma (requires (a == b /\ (forall x. apply_log x a == apply_log x b)))
          (ensures (forall x. eq (apply_log x a) (apply_log x b))) = ()

let rec split_prefix_forall (l:log) (a:log)
  : Lemma (requires is_prefix l a)
          (ensures (forall s. (apply_log s a == apply_log (apply_log s l) (diff a l))) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) == (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |1 -> ()
    |_ -> split_prefix_forall (tail l) (tail a)
    
let lem_eq_is_equiv_c3_st (x:concrete_st) (l:log) (op hd:op_t) (tl:log)
  : Lemma (requires eq (apply_log x (cons op l)) (apply_log (do x hd) (cons op tl)) /\
                    eq (apply_log (do x hd) (cons op tl)) (apply_log (do x hd) (snoc tl op)))
          (ensures eq (apply_log x (cons op l)) (apply_log (do x hd) (snoc tl op)))
          [SMTPat (eq (apply_log x (cons op l)) (apply_log (do x hd) (snoc tl op)))] = 
  transitive (apply_log x (cons op l)) 
             (apply_log (do x hd) (cons op tl))
             (apply_log (do x hd) (snoc tl op))

let rec lem_equiv_st_foldl_st (a b:concrete_st) (l:log)
  : Lemma (requires eq a b) 
          (ensures eq (apply_log a l) (apply_log b l))
          (decreases length l)
          [SMTPat (eq (apply_log a l) (apply_log b l))] =
  match length l with
  |0 -> ()
  |_ -> lem_do a b (head l);
       lem_equiv_st_foldl_st (do a (head l)) (do b (head l)) (tail l)
       
let lem_case1 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. apply_log x (cons op l) == (apply_log (apply_log x (cons op (create 1 hd))) tl))))
          (decreases length l) = 
  let hd = head l in let tl = tail l in
  assert (is_prefix (cons op (create 1 hd)) (cons op l));
  assert (cons op l = cons op (cons hd tl));
  assert (cons op (cons hd tl) = cons op (append (create 1 hd) tl)); 
  append_assoc (create 1 op) (create 1 hd) tl;
  assert (cons op (append (create 1 hd) tl) = (cons op (create 1 hd)) ++ tl);
  assert ((cons op (cons hd tl)) = (cons op (create 1 hd)) ++ tl); 
  assert (cons op l = (cons op (create 1 hd)) ++ tl);

  lem_is_diff ((cons op (create 1 hd)) ++ tl) (cons op (create 1 hd)) tl;  
  assert (tl = diff (cons op l) (cons op (create 1 hd)));
  split_prefix_forall (cons op (create 1 hd)) (cons op l)

let rec lem_seq_foldl_forall (l:log) 
  : Lemma (requires true)
          (ensures (forall x. (length l > 0 ==> (apply_log x l == apply_log (do x (head l)) (tail l)) /\
                                          (apply_log x l == do (apply_log x (fst (un_snoc l))) (last l))) /\
                         (length l = 0 ==> apply_log x l == x)))
                   
                   (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_seq_foldl_forall (tail l)
  
let lem_case3 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. apply_log x (cons hd (cons op tl)) == (apply_log (do x hd) (cons op tl)))))
                   (decreases length l) = 
  let hd = head l in let tl = tail l in
  assert (head (cons hd (cons op tl)) = hd); 
  lemma_tl hd (cons op tl);
  assert (tail (cons hd (cons op tl)) = (cons op tl));
  lem_seq_foldl_forall (cons hd (cons op tl))

let lem_case4 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. apply_log (do x hd) (snoc tl op) == (apply_log x (snoc l op)))))
          (decreases length l) = 
  let hd = head l in let tl = tail l in
  assert (head (cons hd (snoc tl op)) = hd);
  lemma_tl hd (snoc tl op);
  lemma_tail_snoc (cons hd tl) op;
  assert (tail (cons hd (snoc tl op)) = (snoc tl op));
  lem_seq_foldl_forall (cons hd (snoc tl op))

let lem_equiv_st_foldl (a b:log) (l:log)
  : Lemma (ensures (forall x. eq (apply_log x a) (apply_log x b) ==>
                         eq (apply_log (apply_log x a) l) (apply_log (apply_log x b) l))) = ()
                         
let lem_case2_help (l:log) (op:op_t) //check
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. eq (apply_log (apply_log x (cons op (create 1 hd))) tl) 
                             (apply_log (apply_log x (cons hd (create 1 op))) tl))))
          (decreases length l) = 
  let hd = head l in let tl = tail l in
  commutative_prop op hd;
  assert (forall x. eq (apply_log x (cons op (create 1 hd))) (apply_log x (cons hd (create 1 op))));
  lem_equiv_st_foldl (cons op (create 1 hd)) (cons hd (create 1 op)) tl

let lem_case2_help1 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. eq (apply_log (apply_log x (cons op (create 1 hd))) tl) 
                             (apply_log (apply_log x (cons hd (create 1 op))) tl))))
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. apply_log (apply_log x (cons hd (create 1 op))) tl ==
                          apply_log x (cons hd (cons op tl))))) = 
  let hd = head l in let tl = tail l in
  assert (is_prefix (cons hd (create 1 op)) (cons hd (cons op tl)));
  append_assoc (create 1 hd) (create 1 op) tl;
  assert (cons hd (cons op tl) = (cons hd (create 1 op) ++ tl));
  lem_is_diff (cons hd (cons op tl)) (cons hd (create 1 op)) tl;
  assert (tl = diff (cons hd (cons op tl)) (cons hd (create 1 op)));
  split_prefix_forall (cons hd (create 1 op)) (cons hd (cons op tl));
  ()

let lem_case2 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. eq (apply_log (apply_log x (cons op (create 1 hd))) tl) 
                             (apply_log (apply_log x (cons hd (create 1 op))) tl) /\
                          apply_log (apply_log x (cons hd (create 1 op))) tl ==
                          apply_log x (cons hd (cons op tl)))))
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. eq (apply_log (apply_log x (cons op (create 1 hd))) tl) 
                             (apply_log x (cons hd (cons op tl)))))) = ()

let rec lem_foldl_comm (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l)
          (ensures (forall x. eq (apply_log x (cons op l)) (apply_log x (snoc l op)))) (decreases length l) =
  match length l with
  |0 -> lemma_empty l; 
       append_empty_r (create 1 op); 
       append_empty_l (create 1 op);
       assert (forall x. apply_log x (cons op l) == apply_log x (snoc l op));
       lem_eq_is_equiv (cons op l) (snoc l op)
      
  |_ -> let hd = head l in let tl = tail l in
       assert (l == cons hd tl);
       distinct_invert_append (create 1 hd) tl;
       assert (commutative_seq op tl /\ distinct_ops tl);
       lem_foldl_comm tl op;  
       lem_case1 l op; // eq (apply_log x (cons op l)) (seq_foldl (apply_log x (cons op (create 1 hd))) tl))
       lem_case2_help l op;
       lem_case2_help1 l op;
       lem_case2 l op; // eq (apply_log (seq_foldl x (cons op (create 1 hd))) tl) (apply_log x (cons hd (cons op tl))));      
       lem_case3 l op; // eq (apply_log x (cons hd (cons op tl))) (apply_log (do x hd) (cons op tl)))       
       assert (forall x. eq (apply_log (do x hd) (cons op tl)) (apply_log (do x hd) (snoc tl op))); // from IH       
       lem_case4 l op // eq (apply_log (do x hd) (snoc tl op)) (apply_log x (snoc l op)));

let lem_seq_foldl_split (x:concrete_st) (p:log) (s:log)
  : Lemma (ensures apply_log (apply_log x p) s == (apply_log x (p ++ s)))
          (decreases length p) =
  lem_is_diff (p ++ s) p s;
  split_prefix x p (p ++ s)  
let lem_seq_foldl_op (x:concrete_st) (l:log) (op:op_t)
  : Lemma (requires distinct_ops l /\ mem op l /\
                    (let _, s = pre_suf l op in commutative_seq op s))
          (ensures (let p,s = pre_suf l op in
                      eq (apply_log x l) (do (apply_log x (p ++ s)) op)))
          (decreases length l) = 
  let pre, suf = pre_suf l op in
  assert (commutative_seq op suf); 
  pre_suf_prop l op;
  lem_foldl_comm suf op;
  assert (forall x. eq (apply_log x (cons op suf)) (apply_log x (snoc suf op)));
  split_prefix x pre l;
  append_assoc pre (create 1 op) suf;
  assert (l == (snoc pre op) ++ suf /\ l == pre ++ (cons op suf)); 
  lem_is_diff l pre (cons op suf);

  pre_suf_prop l op;
  assert (distinct_ops (pre ++ suf));
  assert (not (mem_id (fst op) (pre ++ suf)));
  distinct_append pre suf;
  distinct_append (pre ++ suf) (create 1 op);
  append_assoc pre suf (create 1 op);
  assert (distinct_ops (pre ++ (snoc suf op)));

  append_assoc pre suf (create 1 op); 
  lem_is_diff (snoc (pre ++ suf) op) (pre ++ suf) (create 1 op);
  assert (is_prefix (pre ++ suf) (snoc (pre ++ suf) op));
  split_prefix x (pre ++ suf) (snoc (pre ++ suf) op); 
  assert (length (snoc (pre ++ suf) op) > 0);
  lem_apply_log x (snoc (pre ++ suf) op);
  lem_last (snoc (pre ++ suf) op); 
  un_snoc_snoc (pre ++ suf) op;
  
  assert (apply_log x l == apply_log (apply_log x pre) (cons op suf));
  assert (eq (apply_log x l) (apply_log (apply_log x pre) (snoc suf op))); 
  lem_seq_foldl_split x pre (snoc suf op);

  assert (apply_log x (snoc (pre ++ suf) op) == do (apply_log x (pre ++ suf)) op);
  assert (apply_log x (snoc (pre ++ suf) op) == apply_log x (pre ++ (snoc suf op)));
  assert (apply_log x (pre ++ (snoc suf op)) == apply_log (apply_log x pre) (snoc suf op));
  
  assert (apply_log (apply_log x pre) (snoc suf op) == do (apply_log x (pre ++ suf)) op);
  
  eq_is_equiv (apply_log (apply_log x pre) (snoc suf op)) (do (apply_log x (pre ++ suf)) op);
  transitive (apply_log x l) (apply_log (apply_log x pre) (snoc suf op)) (do (apply_log x (pre ++ suf)) op)

// returns the inverse state by undoing operation op in (ops_of s)
let inverse_st_op (s:st) (op:op_t{mem op (ops_of s) /\ 
                           (let _, suf = pre_suf (ops_of s) op in
                            commutative_seq op suf)})
  : GTot (i:st{(let (pre,suf) = pre_suf (ops_of s) op in
               eq (v_of s) (do (v_of i) op) /\
               (ops_of i == (pre ++ suf)) /\
               (ops_of s == (Seq.snoc pre op) ++ suf) /\
               is_prefix pre (ops_of s) /\ is_prefix pre (ops_of i) /\
               length (ops_of i) = length (ops_of s) - 1 /\
               (forall id. (mem_id id (ops_of i) \/ id = fst op) <==> mem_id id (ops_of s)) /\
               (forall id. mem_id id (ops_of i) <==> (mem_id id (ops_of s) /\ id <> fst op)))}) = 
  let pre, suf = pre_suf (ops_of s) op in
  pre_suf_prop (ops_of s) op;
  lem_seq_foldl_op init_st (ops_of s) op;
  let v_i = apply_log init_st (pre ++ suf) in
  assert (eq (v_of s) (do v_i op));
  (v_i, hide (pre ++ suf))

#push-options "--z3rlimit 50 --ifuel 3"
let lem_l2a_l1r_eq''_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    Add? (snd (snd last2)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

#push-options "--z3rlimit 100"
let rec lem_l2a_l1r_eq''_s10 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Add? (snd (snd last2)) /\
                    get_rid last1 <> get_rid last2)
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2)]) =
  if ops_of s2 = ops_of lca then
     lem_l2a_l1r_eq''_base lca s1 s2 last1 last2
  else 
    (admit();lem_l2a_l1r_eq''_s10 lca s1 (inverse_st s2) last1 last2) //done below

let rec lem_l2a_l1r_eq'' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires Add? (snd (snd last2)) /\ Rem? (snd (snd last1)) /\ get_ele last1 = get_ele last2 /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    get_rid last1 <> get_rid last2)
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2); length (ops_of s1)]) = 
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    lem_l2a_l1r_eq''_base lca s1 s2 last1 last2
  else if ops_of s1 = ops_of lca then
    lem_l2a_l1r_eq''_s10 lca s1 s2 last1 last2
  else (let s1' = inverse_st s1 in
        lem_inverse (ops_of lca) (ops_of s1); 
        lem_l2a_l1r_eq'' lca s1' s2 last1 last2; admit())

let linearizable_gt0_s2'_op (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\                   
                    (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    suf2 == snd (pre_suf (ops_of s2) op2) /\
                    (let s2' = inverse_st_op s2 op2 in
                    get_rid last1 <> get_rid op2 /\
                    consistent_branches lca s1 s2' /\
                    consistent_branches lca s1 (do_st s2' op2)))))
     
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let s2' = inverse_st_op s2 op2 in                      
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) op2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') op2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let pre2, op2, suf2 = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  let s2' = inverse_st_op s2 op2 in
  lem_exists last1 (diff (ops_of s2) (ops_of lca)); 
  lem_inverse (ops_of lca) (ops_of s1);
  lem_diff (ops_of s1) (ops_of lca);
  lem_suf_equal2_last (ops_of lca) (ops_of s1);
  lem_diff (ops_of s2) (ops_of lca);
  lem_suf_equal2 (ops_of lca) (ops_of s2) op2;
  lem_inverse_op (ops_of lca) (ops_of s2) op2;
  lem_l2a_l1r_eq'' lca (inverse_st s1) s2' last1 op2

////////////////////////////////////////////////////////////////

let rem_add_lastop_neq_ele (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    consistent_branches_s2_gt0 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    fst last1 <> fst last2 /\
                    Add? (snd (snd last1)) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    ~ (Rem? (snd (snd last2)) /\ get_ele last1 = get_ele last2))) =
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  let s1' = inverse_st s1 in
  lemma_mem_snoc (ops_of s1') last1;
  assert (mem last1 (ops_of s1));
  lem_last (ops_of s1);
  assert (last (ops_of s1) = last1);
  lem_diff (ops_of s1) (ops_of lca);
  assert (last (diff (ops_of s1) (ops_of lca)) = last1);
  assert (mem last1 (diff (ops_of s1) (ops_of lca)));
  let pre, suf = pre_suf (diff (ops_of s1) (ops_of lca)) last1 in
  lem_lastop_suf_0 (diff (ops_of s1) (ops_of lca)) pre suf last1;
  assert (length suf = 0);
  lemma_empty suf; 
  comm_empty_log last1 suf; 
  
  assert (Rem? (snd (snd last2)) /\ get_ele last1 = get_ele last2 ==> commutative_seq last1 suf); 
  assert (Rem? (snd (snd last2)) /\ get_ele last1 = get_ele last2 ==> not (commutative last1 last2));
  assert (Rem? (snd (snd last2)) /\ get_ele last1 = get_ele last2 ==> First_then_second? (resolve_conflict last1 last2));
  assert (Rem? (snd (snd last2)) /\ get_ele last1 = get_ele last2 ==> 
          (not (commutative last1 last2) /\
          First_then_second? (resolve_conflict last1 last2) /\
          commutative_seq last1 suf));
  assert (Rem? (snd (snd last2)) /\ get_ele last1 = get_ele last2 ==> 
           exists_triple last2 (diff (ops_of s1) (ops_of lca)));
  ()

let linearizable_gt0_s1' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\                    
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     First_then_second? (resolve_conflict last1 last2) /\
                     consistent_branches lca (inverse_st s1) s2))
        
          (ensures (let _, last1 = un_snoc (ops_of s1) in                  
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  assert (Add? (snd (snd last1)) /\ Rem? (snd (snd last2)) /\ get_ele last1 = get_ele last2);
  if Rem? (snd (snd last1)) then ()
    else (assert (Add? (snd (snd last1))); 
          rem_add_lastop_neq_ele lca s1 s2;
          assert (~ (Rem? (snd (snd last2)) /\ get_ele last1 = get_ele last2)); ()); 
  assert (~ (Add? (snd (snd last1)) /\ Rem? (snd (snd last2)) /\ get_ele last1 = get_ele last2)); 
  ()

////////////////////////////////////////////////////////////////

let lem_l2a''_s20_ind_l1r_eq (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s2 = ops_of lca /\ 
                    length (ops_of s1) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    Add? (snd (snd last2)) /\ Rem? (snd (snd last1)) /\ get_ele last1 = get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) /\

                    (let s1' = inverse_st s1 in
                     consistent_branches lca s1' s2 /\
                     not (exists_triple last2 (diff (ops_of s1') (ops_of lca))) /\                  
                     eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2))))
                     
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) = 
  let _, last1 = un_snoc (ops_of s1) in
  assume (get_rid last1 <> get_rid last2); // can be done
  lem_inverse (ops_of lca) (ops_of s1);
  lem_diff (ops_of s1) (ops_of lca); 
  lem_suf_equal2_last (ops_of lca) (ops_of s1); 
  lem_l2a_l1r_eq'' lca (inverse_st s1) s2 last1 last2
  
//#push-options "--z3rlimit 50"
let lem_l2a''_s20_ind (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s2 = ops_of lca /\ 
                    length (ops_of s1) > length (ops_of lca) /\
                    Add? (snd (snd last2)) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    
                    (let s1' = inverse_st s1 in
                     consistent_branches lca s1' s2 /\
                     not (exists_triple last2 (diff (ops_of s1') (ops_of lca))) /\                  
                     eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2))))
                     
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) = 
  let _, last1 = un_snoc (ops_of s1) in
  if Rem? (snd (snd last1)) && get_ele last1 <> get_ele last2 then admit()
  else if Add? (snd (snd last1)) then admit()
  else lem_l2a''_s20_ind_l1r_eq lca s1 s2 last2
#pop-options

let rec lem_l2a''_s20 (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s2 = ops_of lca /\
                    Add? (snd (snd last2)) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1)]) = 
  if ops_of s1 = ops_of lca then ()
  else 
    (let s1' = inverse_st s1 in
     pre1_pre2_s1 lca s1 s2;
     assert (consistent_branches lca s1' s2);
     let pre1, last1 = un_snoc (ops_of s1) in
     let pre1d, last1d = un_snoc (diff (ops_of s1) (ops_of lca)) in
     lem_diff (ops_of s1) (ops_of lca);
     assert (last1 = last1d);
     assert ((diff (ops_of s1') (ops_of lca)) = pre1d);
       //lem_not_exists_add last2 (diff (ops_of s1) (ops_of lca));
     assert (not (exists_triple last2 (diff (ops_of s1') (ops_of lca))));
     lem_inverse (ops_of lca) (ops_of s1);
     lem_l2a''_s20 lca s1' s2 last2;
     lem_l2a''_s20_ind lca s1 s2 last2)
     
let rec lem_l2a' (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    Add? (snd (snd last2)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) 
          (decreases %[length (ops_of s2)]) =
  if ops_of s2 = ops_of lca then
    lem_l2a''_s20 lca s1 s2 last2
  else 
    (pre1_pre2_s2 lca s1 s2;
     lem_l2a' lca s1 (inverse_st s2) last2; admit())

let lem_l2a (lca s1 s2:st)
 : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Add? (snd (snd last2)) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
   let _, last2 = un_snoc (ops_of s2) in
   let s2' = inverse_st s2 in
   pre1_pre2_s2 lca s1 s2;
   lem_diff (ops_of s2) (ops_of lca); 
   lem_suf_equal2_last (ops_of lca) (ops_of s2); 
   lem_l2a' lca s1 s2' last2;
   //assert (S.mem (fst last2, get_ele last2) (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2));
   //assert (S.mem (fst last2, get_ele last2) (concrete_merge (v_of lca) (v_of s1) (v_of s2)));
   ()

let lem_l2r_s10p (lca s1 s2:st)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Rem? (snd (snd last2)) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
          (ensures (let s2' = inverse_st s2 in
                    let _, last2 = un_snoc (ops_of s2) in
                    consistent_branches lca s1 s2')) =
  lastop_diff (ops_of lca) (ops_of s2);
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  lem_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  let s2' = inverse_st s2 in
  assume (forall rid. mem_rid rid (diff (ops_of s1) (ops_of lca)) ==> ~ (mem_rid rid (diff (ops_of s2') (ops_of lca)))); ()

let lem_common_pre1_s2' (lca s1 s2:st) (last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\
                    not (mem_id (fst last2) (ops_of s2)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of s1)) /\
                   ops_of s1 = ops_of lca /\
                   not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   is_prefix (ops_of lca) (ops_of s2))
          (ensures (let s2' = inverse_st s2 in
                   consistent_branches lca s1 s2' /\ 
                   not (mem_id (fst last2) (ops_of s2')) /\
                   is_prefix (ops_of lca) (ops_of s2'))) =
  lem_inverse (ops_of lca) (ops_of s2);
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2);
  let s2' = inverse_st s2 in
  assume (forall rid. mem_rid rid (diff (ops_of s1) (ops_of lca)) ==> ~ (mem_rid rid (diff (ops_of s2') (ops_of lca)))); ()

//#push-options "--z3rlimit 50"
let rec lem_l2r_s10 (lca s1 s2:st) (last2:op_t)
 : Lemma (requires consistent_branches lca s1 s2 /\ 
                   ops_of s1 = ops_of lca /\
                   Rem? (snd (snd last2)) /\
                   not (mem_id (fst last2) (ops_of lca)) /\
                   not (mem_id (fst last2) (ops_of s1)) /\
                   not (mem_id (fst last2) (ops_of s2)) /\
                   not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   is_prefix (ops_of lca) (ops_of s2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
         (decreases %[length (ops_of s2)]) =
   admit();if ops_of s2 = ops_of lca then ()
   else 
     (lem_common_pre1_s2' lca s1 s2 last2;
      lem_l2r_s10 lca s1 (inverse_st s2) last2; admit())
#pop-options

let not_add_eq (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    consistent_branches_s2_gt0 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                     Rem? (snd (snd last2)) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     (let s2' = inverse_st s2 in
                     is_prefix (ops_of lca) (ops_of s2')))) 
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    ~ (Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2))) = 
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2); 
  assert (fst last1 <> fst last2);

  let s1' = inverse_st s1 in
  lemma_mem_snoc (ops_of s1') last1;
  assert (mem last1 (ops_of s1)); 
  lem_last (ops_of s1);
  assert (last (ops_of s1) = last1);
  lem_diff (ops_of s1) (ops_of lca);
  assert (last (diff (ops_of s1) (ops_of lca)) = last1);
  assert (mem last1 (diff (ops_of s1) (ops_of lca)));
  let pre, suf = pre_suf (diff (ops_of s1) (ops_of lca)) last1 in
  lem_lastop_suf_0 (diff (ops_of s1) (ops_of lca)) pre suf last1;
  assert (length suf = 0);
  lemma_empty suf; 
  comm_empty_log last1 suf; 
  assert (commutative_seq last1 suf);

  assert ((Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2) ==> not (commutative last1 last2));
  //resolve_conflict_prop last2 last1;
  assert ((Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2) ==> 
                First_then_second? (resolve_conflict last2 last1));
  assert ((Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2) ==> 
                not (commutative last2 last1) /\
                First_then_second? (resolve_conflict last2 last1) /\
                commutative_seq last1 suf);
  assert ((Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2) ==> exists_triple last2 (diff (ops_of s1) (ops_of lca)));
  assert (~ (Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2)); ()

let lem_l2r_neq_p1 (lca s1 s2:st)
 : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2)
         (ensures consistent_branches_s2_gt0 lca (inverse_st s1) s2) =
 lem_inverse (ops_of lca) (ops_of s1);
 inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
 lastop_diff (ops_of lca) (ops_of s1);
 assume (forall rid. mem_rid rid (diff (fst (un_snoc (ops_of s1))) (ops_of lca)) ==> ~ (mem_rid rid (diff (ops_of s2) (ops_of lca)))); ()

let lem_l2r_neq_p2'_help (l:log) (last2:op_t)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd (snd last2)) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 <> get_ele last2 /\
                    exists_triple last2 l'))
          (ensures exists_triple last2 l) 
          [SMTPat (let l', last1 = un_snoc l in
                   (exists_triple last2 l'))] =
  let l', last1 = un_snoc l in
  let pre', op', suf' = find_triple last2 l' in
  lemma_mem_snoc l' last1;
  assert (mem op' l);
  let pre, suf = pre_suf l op' in
  
  assert ((snoc pre op') ++ suf = snoc ((snoc pre' op') ++ suf') last1);
  append_assoc (snoc pre' op') suf' (create 1 last1);
  assert ((snoc pre op') ++ suf = ((snoc pre' op') ++ (snoc suf' last1)));
  lem_suf_equal4 l op';
  distinct_invert_append l' (create 1 last1);
  lem_suf_equal4 l' op';

  not_mem_id l' last1;
  mem_ele_id op' l;
  mem_ele_id op' l';
  lem_id_not_snoc l' suf' last1 op'; 
  assert (not (mem_id (fst op') (snoc suf' last1)));
 
  count_1 l;
  assert (count_assoc_fst (fst op') (snoc pre op' ++ suf) = 1);
  lem_count_1 pre suf pre' (snoc suf' last1) op';
  
  assert (length suf = length (snoc suf' last1));
  lemma_append_inj (snoc pre op') suf (snoc pre' op') (snoc suf' last1);
  assert (suf = snoc suf' last1);
  lemma_mem_snoc suf' last1;
  assert (commutative_seq op' suf); 
  ()
  
let lem_l2r_neq_p2' (l:log) (last2:op_t)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd (snd last2)) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 <> get_ele last2))
          (ensures (let l', last1 = un_snoc l in 
                    (exists_triple last2 l' ==> exists_triple last2 l) /\
                    (not (exists_triple last2 l) ==> not (exists_triple last2 l')))) = ()
                    
let lem_l2r_neq_p2 (lca s1 s2:st)
 : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                   length (ops_of s1) > length (ops_of lca) /\
                   (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd (snd last2)) /\ get_ele last1 <> get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
         (ensures (let s1' = inverse_st s1 in
                   let s2' = inverse_st s2 in
                   let _, last2 = un_snoc (ops_of s2) in
                   (lem_l2r_neq_p1 lca s1 s2;
                    (not (exists_triple last2 (diff (ops_of s1') (ops_of lca))))))) = 
 lem_l2r_neq_p1 lca s1 s2;
 let s1' = inverse_st s1 in
 let _, last2 = un_snoc (ops_of s2) in
 let pre1, last1 = un_snoc (ops_of s1) in
 let pre1d, last1d = un_snoc (diff (ops_of s1) (ops_of lca)) in
 lem_diff (ops_of s1) (ops_of lca);
 assert (last1 = last1d);
 assert (get_ele last1d <> get_ele last2);
 assert ((diff (ops_of s1') (ops_of lca)) = pre1d);
 lem_l2r_neq_p2' (diff (ops_of s1) (ops_of lca)) last2

//#push-options "--z3rlimit 50"
let rec lem_l2r (lca s1 s2:st)
 : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Rem? (snd (snd last2)) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))
         (decreases %[length (ops_of s1)]) = 
   let _, last2 = un_snoc (ops_of s2) in
   if ops_of s1 = ops_of lca then
     (let s2' = inverse_st s2 in
      lem_l2r_s10p lca s1 s2;
      lem_l2r_s10 lca s1 s2' last2) 
   else 
     (let _, last1 = un_snoc (ops_of s1) in
      not_add_eq lca s1 s2;
      assert (~ (Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2));
      let s1' = inverse_st s1 in
      if Rem? (snd (snd last1)) && get_ele last1 = get_ele last2 then
        (admit();lem_last (ops_of s2);
         lem_last (ops_of s1))
         //lem_l2r_l1r_eq lca s1 s2
      else if get_ele last1 <> get_ele last2 then
        (admit();lem_inverse (ops_of lca) (ops_of s1);
         inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
         lastop_diff (ops_of lca) (ops_of s1);
         lem_l2r_neq_p2 lca s1 s2;
         lem_l2r lca s1' s2;
         lem_last (ops_of s2);
         lem_last (ops_of s1))
      else ())
//#pop-options
        
let linearizable_gt0_s2' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     Second_then_first? (resolve_conflict last1 last2) /\
                     consistent_branches lca s1 (inverse_st s2)))
        
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last2 = un_snoc (ops_of s2) in
  if Add? (snd (snd last2)) then
    lem_l2a lca s1 s2
  else lem_l2r lca s1 s2
  
////////////////////////////////////////////////////////////////////////
(*#push-options "--z3rlimit 50 --ifuel 3"
let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires //consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0)
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires //consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    //consistent_branches l' s1' (do_st s2'' last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let merge_pre l a b =
  (forall e. M.contains (concrete_merge l a b) e ==>
        (forall id. M.contains (sel (concrete_merge l a b) e) id ==>
               fst (E.sel (sel a e) id) >= fst (E.sel (sel l e) id) /\
               fst (E.sel (sel b e) id) >= fst (E.sel (sel l e) id)))
               
let linearizable_s1_0''_ind_help (lca s1 s2':st) (last2:op_t)
  : Lemma (requires //consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures (let inv2 = inverse_st s2' in
                   merge_pre (v_of lca) (v_of s1) (do (v_of inv2) last2) /\
                   (forall ele. M.contains (v_of lca) ele ==> M.contains (v_of s1) ele /\ M.contains (do (v_of inv2) last2) ele) /\
                   (forall ele rid. M.contains (v_of lca) ele /\ M.contains (sel (v_of lca) ele) rid ==>
                               M.contains (sel (v_of s1) ele) rid /\ M.contains (sel (do (v_of inv2) last2) ele) rid))) =
                     //(forall ele rid. M.contains (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2)) ele /\ M.contains (sel (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2)) ele) rid ==>
            //                fst (E.sel (sel (v_of s1) ele) rid) >= fst (E.sel (sel (v_of lca) ele) rid) /\
              //              fst (E.sel (sel (do (v_of inv2) last2) ele) rid) >= fst (E.sel (sel (v_of lca) ele) rid)))) = 
  let inv2 = inverse_st s2' in
  split_prefix init_st (ops_of lca) (ops_of (do_st inv2 last2));
  lem_apply init_st (ops_of lca);
  lem_apply (v_of lca) (diff (snoc (ops_of inv2) last2) (ops_of lca))

#push-options "--z3rlimit 200"
let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires //consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = 
  linearizable_s1_0''_ind_help lca s1 s2' last2; 
  //let inv2 = inverse_st s2' in
  //assume (merge_pre (v_of lca) (v_of s1) (do (v_of inv2) last2));
  //assume (merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2));
  ()

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires //consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)       
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_gt0_base_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2))
         
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_base_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2))
         
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_ind_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (let s2' = inverse_st s2 in
                    First_then_second? (resolve_conflict last1 last2) /\
                    //consistent_branches lca s1 (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    //consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let merge_pre_ext l a b =
  (forall e. M.contains l e ==> M.contains a e /\ M.contains b e) /\
  (forall e id. M.contains l e /\ M.contains (sel l e) id ==> M.contains (sel a e) id /\ M.contains (sel b e) id) /\
  (forall e. M.contains (concrete_merge l a b) e ==>
        (forall id. M.contains (sel (concrete_merge l a b) e) id ==>
               fst (E.sel (sel a e) id) >= fst (E.sel (sel l e) id) /\
               fst (E.sel (sel b e) id) >= fst (E.sel (sel l e) id)))

let linearizable_gt0_ind_stf_help (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (let s2' = inverse_st s2 in
                    ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    //Rem? (snd (snd last1)) /\ Add? (snd (snd last2)) /\
                    //consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
        
          (ensures (let s2' = inverse_st s2 in
                   merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                   (forall ele. M.contains (v_of lca) ele ==> M.contains (do (v_of s1) last1) ele /\ M.contains (do (v_of s2') last2) ele) /\
                   (forall ele rid. M.contains (v_of lca) ele /\ M.contains (sel (v_of lca) ele) rid ==>
                               M.contains (sel (do (v_of s1) last1) ele) rid /\ M.contains (sel (do (v_of s2') last2) ele) rid))) =
  let s2' = inverse_st s2 in
  split_prefix init_st (ops_of lca) (ops_of (do_st s2' last2));
  lem_apply init_st (ops_of lca);
  lem_apply (v_of lca) (diff (snoc (ops_of s2') last2) (ops_of lca));
  split_prefix init_st (ops_of lca) (ops_of (do_st s1 last1));
  lem_apply init_st (ops_of lca);
  lem_apply (v_of lca) (diff (snoc (ops_of s1) last1) (ops_of lca))

let linearizable_gt0_ind_stf_ra (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    get_rid last1 <> get_rid last2 /\
                    (let s2' = inverse_st s2 in
                    ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Rem? (snd (snd last1)) /\ Add? (snd (snd last2)) /\ //get_ele last1 <> get_ele last2 /\
                    //consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let s2' = inverse_st s2 in
  linearizable_gt0_ind_stf_help lca s1 s2 last1 last2;
  assert (merge_pre_ext (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2));
  assert (forall e. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e =
               M.contains (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e);
  assert (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==>
                   M.contains (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid =
                   M.contains (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid); 
  assert (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==>
                   E.sel (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid ==
                   E.sel (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid);
  assert (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
             (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)));
  ()

let linearizable_gt0_ind_stf_rr (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    get_rid last1 <> get_rid last2 /\
                    (let s2' = inverse_st s2 in
                    ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Rem? (snd (snd last1)) /\ Rem? (snd (snd last2)) /\ //get_ele last1 <> get_ele last2 /\
                    //consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let s2' = inverse_st s2 in
  linearizable_gt0_ind_stf_help lca s1 s2 last1 last2;
  assert (merge_pre_ext (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2));
  assert (forall e. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e =
               M.contains (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e); 
  assert (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==>
                   M.contains (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid =
                   M.contains (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid);
  assert (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==>
                   E.sel (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid ==
                   E.sel (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid); 
  assert (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
             (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)));
  ()

let linearizable_gt0_ind_stf_ar (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    get_rid last1 <> get_rid last2 /\
                    (let s2' = inverse_st s2 in
                    ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Add? (snd (snd last1)) /\ Rem? (snd (snd last2)) /\ get_ele last1 <> get_ele last2 /\
                    //consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let s2' = inverse_st s2 in
  linearizable_gt0_ind_stf_help lca s1 s2 last1 last2;
  assert (merge_pre_ext (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2));
  assert (forall e. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e =
               M.contains (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e);
  assert (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==>
                   M.contains (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid =
                   M.contains (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid);
  assert (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==>
                   E.sel (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid ==
                   E.sel (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid);
  assert (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
             (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)));
  ()

let linearizable_gt0_ind_stf_aaa (lca s2:st) (last1 last2:op_t) // s1 = lca
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    //fst last1 <> fst last2 /\
                    get_rid last1 <> get_rid last2 /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     Add? (snd (snd last2')) /\
                    //ops_of s1 = ops_of lca /\
                    //Second_then_first? (resolve_conflict last1 last2) /\
                    Add? (snd (snd last1)) /\ Add? (snd (snd last2)) /\ //get_ele last1 = get_ele last2 /\
                    //consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st lca last1) (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2') last2))))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2))) = 
  let s2' = inverse_st s2 in
  linearizable_gt0_ind_stf_help lca lca s2 last1 last2;
  assert (merge_pre_ext (v_of lca) (do (v_of lca) last1) (do (v_of s2') last2));
  assert (forall e. M.contains (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e =
               M.contains (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2)) e);
  assert (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e ==>
                   M.contains (sel (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e) rid =
                   M.contains (sel (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2)) e) rid);
  assert (forall e rid. (e = get_ele last2 /\  M.contains (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e) ==>
                   E.sel (sel (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e) rid ==
                   E.sel (sel (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2)) e) rid);
  assert (eq (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2)
             (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2)));
  ()

let linearizable_gt0_ind_stf_aar (lca s2:st) (last1 last2:op_t) // s1 = lca
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    //fst last1 <> fst last2 /\
                    get_rid last1 <> get_rid last2 /\
                    (let s2' = inverse_st s2 in
                     let _, last2' = un_snoc (ops_of s2) in
                     Rem? (snd (snd last2')) /\
                    //ops_of s1 = ops_of lca /\
                    //Second_then_first? (resolve_conflict last1 last2) /\
                    Add? (snd (snd last1)) /\ Add? (snd (snd last2)) /\ //get_ele last1 = get_ele last2 /\
                    //consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st lca last1) (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2') last2))))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2))) = 
  let s2' = inverse_st s2 in
  linearizable_gt0_ind_stf_help lca lca s2 last1 last2;
  assert (merge_pre_ext (v_of lca) (do (v_of lca) last1) (do (v_of s2') last2));
  assert (forall e. M.contains (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e =
               M.contains (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2)) e);
  assert (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e ==>
                   M.contains (sel (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e) rid =
                   M.contains (sel (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2)) e) rid);
  assert (forall e rid. (e = get_ele last2 /\  M.contains (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e) ==>
                   E.sel (sel (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2) e) rid ==
                   E.sel (sel (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2)) e) rid);
  assert (eq (do (concrete_merge (v_of lca) (do (v_of lca) last1) (v_of s2)) last2)
             (concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2)));
  ()
  
let linearizable_gt0_ind1_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (let s1' = inverse_st s1 in
                    ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    //consistent_branches lca s1' (do_st s2 last2) /\
                    //consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
                           
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_ind1_stf_help (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of s1) > length (ops_of lca) /\
                    (let s1' = inverse_st s1 in
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
        
          (ensures (let s1' = inverse_st s1 in
                   merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                   (forall ele. M.contains (v_of lca) ele ==> M.contains (do (v_of s1') last1) ele /\ M.contains (do (v_of s2) last2) ele) /\
                   (forall ele rid. M.contains (v_of lca) ele /\ M.contains (sel (v_of lca) ele) rid ==>
                               M.contains (sel (do (v_of s1') last1) ele) rid /\ M.contains (sel (do (v_of s2) last2) ele) rid))) =
  let s1' = inverse_st s1 in
  split_prefix init_st (ops_of lca) (ops_of (do_st s1' last1));
  lem_apply init_st (ops_of lca);
  lem_apply (v_of lca) (diff (snoc (ops_of s1') last1) (ops_of lca));
  split_prefix init_st (ops_of lca) (ops_of (do_st s2 last2));
  lem_apply init_st (ops_of lca);
  lem_apply (v_of lca) (diff (snoc (ops_of s2) last2) (ops_of lca))
  
let linearizable_gt0_ind1_stf_rr (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    //fst last1 <> fst last2 /\
                    get_rid last1 <> get_rid last2 /\
                    Rem? (snd (snd last1)) /\ Rem? (snd (snd last2)) /\
                    (let s1' = inverse_st s1 in
                     let _, last1' = un_snoc (ops_of s1) in
                     Add? (snd (snd last1')) /\
                    //Second_then_first? (resolve_conflict last1 last2) /\
                    //consistent_branches lca (do_st s1' last1) s2 /\
                    //consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
                           
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let s1' = inverse_st s1 in
  //linearizable_gt0_ind1_stf_help lca s1 s2 last1 last2;
  assume (merge_pre_ext (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2));
  assume (forall e. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e =
               M.contains (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e);
  assume (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==>
                   M.contains (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid =
                   M.contains (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid);
  assert (forall e rid. M.contains (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e ==>
                   E.sel (sel (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2) e) rid ==
                   E.sel (sel (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) e) rid);  admit();
  assert (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
             (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)));
  ()


let linearizable_gt0_ind1_stf_de (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    Disable? (snd (snd last1)) /\ Enable? (snd (snd last2)) /\
                    (let s1' = inverse_st s1 in
                    Second_then_first? (resolve_conflict last1 last2) /\
                    //consistent_branches lca (do_st s1' last1) s2 /\
                    //consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
                           
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

////////////////////////////////////////////////////////////////
//// Linearization properties - intermediate merge //////

let prop1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second)
                    //get_rid o1 = get_rid o2 /\ get_rid o3 <> get_rid o1))
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
