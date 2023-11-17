module Ewflag_rid_map

module M = Map_extended
module S = FStar.Set
open SeqUtils
open FStar.Seq
open FStar.Ghost

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

// apply an operation to a state
let do (s:concrete_st) (o:op_t) 
  : (r:concrete_st{(Enable? (snd (snd o)) ==> sel r (get_rid o) = (fst (sel s (get_rid o)) + 1, true) /\
                                              (forall rid. rid <> get_rid o ==> sel r rid = sel s rid)) /\
                   (Disable? (snd (snd o)) ==> (forall rid. sel r rid = (fst (sel s rid), false)))}) =
  match o with
  |(_, (rid, Enable)) -> M.upd s rid (fst (sel s rid) + 1, true) 
  |(_, (rid, Disable)) -> M.map_val (fun (c,f) -> (c, false)) s 

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()

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
                        (forall rid. M.contains x rid ==> M.contains r rid) /\
                        (forall rid. fst (sel r rid) >= fst (sel x rid))))
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

let concrete_merge (lca s1 s2:concrete_st) 
  : (r:concrete_st{(forall rid. M.contains r rid <==> M.contains lca rid \/ M.contains s1 rid \/ M.contains s2 rid) /\
                   (forall rid. sel r rid = merge_cf (sel lca rid) (sel s1 rid) (sel s2 rid))}) =  
  let keys = S.union (M.domain lca) (S.union (M.domain s1) (M.domain s2)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun k v -> merge_cf (sel lca k) (sel s1 k) (sel s2 k)) u

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

let lin_rc_ind_s1' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of s1) > length (ops_of lca) /\
                    Disable? (snd (snd last1)) /\ Enable? (snd (snd last2)) /\
                    (let s1' = inverse_st s1 in
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
                           
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()
                      
let lin_rc_ind_s2' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of s2) > length (ops_of lca) /\
                    Disable? (snd (snd last1)) /\ Enable? (snd (snd last2)) /\
                    (let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
                           
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()
                      
let rec lin_rc (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\ 
                    //fst last1 <> fst last2 /\
                    get_rid last1 <> get_rid last2 /\
                    Disable? (snd (snd last1)) /\ Enable? (snd (snd last2)))       
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
                       
#push-options "--z3rlimit 50 --ifuel 3"
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

let linearizable_s1_0''_ind_help (lca s1 s2':st) (last2:op_t)
  : Lemma (requires //consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures (let inv2 = inverse_st s2' in
                   (forall id. M.contains (v_of lca) id ==> M.contains (v_of s1) id /\ M.contains (do (v_of inv2) last2) id) /\
                     (forall id. M.contains (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2)) id ==>
                            fst (sel (v_of s1) id) >= fst (sel (v_of lca) id) /\
                            fst (sel (do (v_of inv2) last2) id) >= fst (sel (v_of lca) id)))) = 
  let inv2 = inverse_st s2' in
  split_prefix init_st (ops_of lca) (ops_of (do_st inv2 last2));
  lem_apply init_st (ops_of lca);
  lem_apply (v_of lca) (diff (snoc (ops_of inv2) last2) (ops_of lca))

let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires //consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = 
  linearizable_s1_0''_ind_help lca s1 s2' last2

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

let linearizable_gt0_ind_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (let s2' = inverse_st s2 in
                    ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    //consistent_branches lca (do_st s1 last1) s2' /\
                    //consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

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

let linearizable_gt0_ind1_stf_dd (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires //consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    //consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    Disable? (snd (snd last1)) /\ Disable? (snd (snd last2)) /\
                    (let s1' = inverse_st s1 in
                    Second_then_first? (resolve_conflict last1 last2) /\
                    //consistent_branches lca (do_st s1' last1) s2 /\
                    //consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
                           
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()

let linearizable_gt0_ind1_stf_ee_help (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2)
          (ensures (forall id. M.contains (v_of lca) id ==> M.contains (do (v_of s1) last1) id /\  M.contains (v_of s2) id) /\
                   (forall id. M.contains (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) id ==>
                      fst (sel (do (v_of s1) last1) id) >= fst (sel (v_of lca) id) /\
                      fst (sel (v_of s2) id) >= fst (sel (v_of lca) id))) =
  lem_apply init_st (ops_of lca);  
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_apply (v_of lca) (diff (ops_of s2) (ops_of lca));
  split_prefix init_st (ops_of lca) (ops_of (do_st s1 last1));
  lem_apply (v_of lca) (diff (snoc (ops_of s1) last1) (ops_of lca))

#push-options "--z3rlimit 200"
let linearizable_gt0_ind1_stf_ee (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    Enable? (snd (snd last1)) /\ Enable? (snd (snd last2)) /\
                    (let s1' = inverse_st s1 in
                    Second_then_first? (resolve_conflict last1 last2) /\
                    //consistent_branches lca (do_st s1' last1) s2 /\
                    //consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    //consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
                           
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  linearizable_gt0_ind1_stf_ee_help lca s1 s2 last1 last2
#push-options

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
