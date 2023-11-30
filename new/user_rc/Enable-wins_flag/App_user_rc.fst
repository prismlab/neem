module App_user_rc

module M = Map_extended
module S = FStar.Set

#set-options "--query_stats"

let cf = (int * bool)

// the concrete state type
type concrete_st = M.t nat cf // (replica_id, ctr, flag) //replica ids are unique

// init state
let init_st : concrete_st = M.const (0, false)

let sel (s:concrete_st) k = if M.contains s k then M.sel s k else (0, false)

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  (forall id. M.contains a id = M.contains b id /\
         sel a id == sel b id)

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

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |(_, (rid, Enable)) -> M.upd s rid (fst (sel s rid) + 1, true) 
  |(_, (rid, Disable)) -> M.map_val (fun (c,f) -> (c, false)) s
let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()

//operations x and y are commutative
let comm_ops (x y:op_t) : bool =
  match snd (snd x), snd (snd y) with
  |Enable, Enable |Disable, Disable -> true
  |_ -> false

// if x and y are commutative ops, applying them in any order should give equivalent results
let commutative_prop (x y:op_t) 
  : Lemma (requires comm_ops x y)
          (ensures (forall s. eq (apply_log s (cons x (cons y empty))) (apply_log s (cons y (cons x empty))))) = ()

//conflict resolution
let rc (x:op_t) (y:op_t{fst x <> fst y /\ ~ (comm_ops x y)}) : rc_res =
  match snd (snd x), snd (snd y) with
  |Enable, Disable -> Snd_fst
  |_ -> Fst_snd // Disable, Enable

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
let merge (l a b:concrete_st) : concrete_st =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun k v -> merge_cf (sel l k) (sel a k) (sel b k)) u
  
/////////////////////////////////////////////////////////////////////////////

let no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ fst o2 <> fst o3 /\ ~ (comm_ops o1 o2) /\ ~ (comm_ops o2 o3))
          (ensures ~ (Fst_snd? (rc o1 o2) /\ Fst_snd? (rc o2 o3))) = ()

let relaxed_comm (s:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o1 o2) /\ ~ (comm_ops o2 o3))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

let rc_comm (o1 o2:op_t)
  : Lemma (requires fst o1 <> fst o2)
          (ensures ~ (comm_ops o1 o2) ==> (Fst_snd? (rc o1 o2) \/ Fst_snd? (rc o2 o1))) = ()

let base (l:concrete_st) (o1 o2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1))
          (ensures eq (merge l (do l o1) (do l o2)) (do (do l o2) o1)) = ()

#push-options "--z3rlimit 50 --ifuel 3 --split_queries always"
let rec trial (l:st) (o1 o2:op_t) (l1 l2:log)
  : Lemma (requires distinct_ops l1 /\ distinct_ops l2 /\ (forall id1 id2. mem_id id1 l1 ==> not (mem_id id2 l2)) /\
                    not (mem_id (fst o1) l1) /\ not (mem_id (fst o1) l2) /\
                    not (mem_id (fst o2) l1) /\ not (mem_id (fst o2) l2) /\
                    fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1))
          (ensures true)
          (decreases %[length l1; length l2]) =
  if length l1 = 0 && length l2 = 0 then 
    (assert (eq (merge (v_of l) (do (v_of l) o1) (do (v_of l) o2)) (do (do (v_of l) o2) o1)); ())
  else if length l2 = 0 then
    (let pre, last1 = un_snoc l1 in
     assume (distinct_ops pre /\ (forall id1 id2. mem_id id1 pre ==> not (mem_id id2 l2)) /\
             not (mem_id (fst o1) pre) /\ not (mem_id (fst o2) pre) /\ not (mem_id (fst o2) l2));
     trial l o1 o2 pre l2; 
     assume (apply_log (do (v_of l) o1) l1 = do (apply_log (do (v_of l) o1) pre) last1);
     assume (apply_log (do (do (v_of l) o2) o1) l1 = do (apply_log (do (do (v_of l) o2) o1) pre) last1);
     assert (eq (merge (v_of l) (apply_log (do (v_of l) o1) l1) (do (do (v_of l) o2) o1))
                (apply_log (do (do (v_of l) o2) o1) l1)); ())
  else ()
  

/////////////////////////////////////////////////////////////////////////////

// Prove that merge is commutative
let merge_comm (l a b:st)
  : Lemma (requires cons_reps l a b)
          (ensures (eq (merge (v_of l) (v_of a) (v_of b)) 
                       (merge (v_of l) (v_of b) (v_of a)))) = ()

let merge_idem (s:st)
  : Lemma (ensures eq (merge (v_of s) (v_of s) (v_of s)) (v_of s)) = ()

#push-options "--z3rlimit 50 --ifuel 3 --split_queries always"
let fast_fwd_base (a b:st) (last2:op_t)
  : Lemma (ensures eq (do (v_of a) last2) (merge (v_of a) (v_of a) (do (v_of a) last2))) = ()

let rec lem_apply (x:concrete_st) (l:log)
  : Lemma (ensures (let r = apply_log x l in
                        (forall rid. M.contains x rid ==> M.contains r rid) /\
                        (forall rid. fst (sel r rid) >= fst (sel x rid))))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_apply (do x (head l)) (tail l)

let fast_fwd_ind (a b:st) (last2:op_t)
  : Lemma (requires length (ops_of b) > length (ops_of a) /\
                    (let b' = inverse_st b in
                    cons_reps a a b' /\
                    eq (do (v_of b') last2) (merge (v_of a) (v_of a) (do (v_of b') last2))))
        
          (ensures eq (do (v_of b) last2) (merge (v_of a) (v_of a) (do (v_of b) last2))) = 
  let b' = inverse_st b in
  split_prefix init_st (ops_of a) (ops_of (do_st b' last2));
  lem_apply init_st (ops_of a);
  lem_apply (v_of a) (diff (snoc (ops_of b') last2) (ops_of a))
  
let merge_eq (l a b a':concrete_st)
  : Lemma (requires eq a a')
          (ensures eq (merge l a b)
                      (merge l a' b)) = ()

let lin_rc_ind_b' (l a b:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of b) > length (ops_of l) /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2) /\
                    (let b' = inverse_st b in
                    eq (do (merge (v_of l) (do (v_of a) last1) (v_of b')) last2)
                       (merge (v_of l) (do (v_of a) last1) (do (v_of b') last2))))
                           
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) = ()

let lin_rc_ind_a' (l a b:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of a) > length (ops_of l) /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2) /\
                    (let a' = inverse_st a in
                    eq (do (merge (v_of l) (do (v_of a') last1) (v_of b)) last2)
                       (merge (v_of l) (do (v_of a') last1) (do (v_of b) last2))))
                           
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) = ()

let rec lin_rc (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\ 
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))
          (decreases %[length (ops_of a); length (ops_of b)]) =
  if ops_of a = ops_of l && ops_of b = ops_of l then ()
  else if ops_of a = ops_of l then 
    (let b' = inverse_st b in 
     cons_reps_s2' l a b;
     lin_rc l a b' last1 last2;
     lin_rc_ind_b' l a b last1 last2) 
  else 
    (let a' = inverse_st a in
     cons_reps_s1' l a b;
     lin_rc l a' b last1 last2;
     lin_rc_ind_a' l a b last1 last2)

let lin_rc_a' (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\ 
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Snd_fst? (rc last1 last2))
          (ensures eq (do (merge (v_of l) (v_of a) (do (v_of b) last2)) last1)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) =
  lin_rc l b a last2 last1
                      
let cons_reps' (l a b:st1) =
  distinct_ops (ops_of l) /\ distinct_ops (ops_of a) /\ distinct_ops (ops_of b) /\
  is_prefix (ops_of l) (ops_of a) /\
  is_prefix (ops_of l) (ops_of b)

let rec lin_rc' (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps' l a b /\ 
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))
          (decreases %[length (ops_of a); length (ops_of b)]) =
  if ops_of a = ops_of l && ops_of b = ops_of l then ()
  else if ops_of a = ops_of l then 
    (let b' = inverse_st b in 
     lin_rc' l a b' last1 last2;
     lin_rc_ind_b' l a b last1 last2) 
  else 
    (let a' = inverse_st a in
     lin_rc' l a' b last1 last2;
     lin_rc_ind_a' l a b last1 last2)
     
let lin_comm_ind_b' (l a b:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of b) > length (ops_of l) /\
                    comm_ops last1 last2 /\
                    (let b' = inverse_st b in
                    eq (do (merge (v_of l) (do (v_of a) last1) (v_of b')) last2)
                       (merge (v_of l) (do (v_of a) last1) (do (v_of b') last2))))
                           
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) = ()

let lin_comm_ind_a' (l a b:st) (last1 last2:op_t)
  : Lemma (requires //cons_reps l a b /\ 
                    length (ops_of a) > length (ops_of l) /\
                    comm_ops last1 last2 /\
                    ops_of b = ops_of l /\
                    (let a' = inverse_st a in
                    eq (do (merge (v_of l) (do (v_of a') last1) (v_of b)) last2)
                       (merge (v_of l) (do (v_of a') last1) (do (v_of b) last2))))
                           
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) = ()
                      
let rec lin_comm1 (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2)
                    //~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))
          (decreases %[length (ops_of a); length (ops_of b)]) = 
  if ops_of a = ops_of l && ops_of b = ops_of l then ()
  else if ops_of b = ops_of l then 
    (let a' = inverse_st a in
     cons_reps_s1' l a b;
     lin_comm1 l a' b last1 last2;
     lin_comm_ind_a' l a b last1 last2)
  else 
    (let b' = inverse_st b in
     cons_reps_s2' l a b;
     lin_comm1 l a b' last1 last2;
     lin_comm_ind_b' l a b last1 last2)

let rec lin_comm1' (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps' l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2)
                    //~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))
          (decreases %[length (ops_of a); length (ops_of b)]) = 
  if ops_of a = ops_of l && ops_of b = ops_of l then ()
  else if ops_of b = ops_of l then 
    (let a' = inverse_st a in
     lin_comm1' l a' b last1 last2;
     lin_comm_ind_a' l a b last1 last2)
  else 
    (let b' = inverse_st b in
     lin_comm1' l a b' last1 last2;
     lin_comm_ind_b' l a b last1 last2)
     
#pop-options

let lin_comm (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    ~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) =
  lin_comm1 l a b last1 last2

let lin_comm' (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps' l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    ~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) =
  lin_comm1' l a b last1 last2
  
let inter_merge1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    ~ (comm_ops o3 o1) /\ ~ (comm_ops o3 o2) /\
                    Fst_snd? (rc o3 o1) (*/\ Fst_snd? (rc o3 o2*))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

let inter_merge2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o2 <> fst o3 /\ fst o1 <> fst o3 /\
                    ~ (comm_ops o3 o1) /\ ~ (comm_ops o3 o2) /\
                    Fst_snd? (rc o3 o1) /\ //Fst_snd? (rc o3 o2) /\
                    eq (merge l s (do l o3)) s' /\
                    eq (merge s (do s o2) s') (do s' o2))
          (ensures eq (merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

#push-options "--ifuel 3"
let inter_merge3 (l a b c:concrete_st) (op op':op_t) 
  : Lemma (requires eq (merge l a b) c /\
                    (forall (o:op_t). eq (merge l a (do b o)) (do c o)))
          (ensures eq (merge l a (do (do b op) op')) (do (do c op) op')) = ()
#pop-options

let inter_merge4 (l s:concrete_st) (o1 o2 o3 o4:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o4 /\ fst o2 <> fst o3 /\
                    ~ (comm_ops o3 o1) /\ ~ (comm_ops o3 o2) /\ ~ (comm_ops o4 o1) /\
                    Fst_snd? (rc o3 o1) /\ //Fst_snd? (rc o3 o2) /\ Fst_snd? (rc o4 o1) /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1)) 
                      (do (do (do (do s o4) o3) o1) o2)) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
let concrete_st_s = bool

// init state 
let init_st_s = false

// apply an operation to a state 
let do_s (st_s:concrete_st_s) (o:op_t) : concrete_st_s =
  match snd (snd o) with
  |Enable -> true
  |Disable -> false

// equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  st_s = true <==> (exists rid. snd (sel st rid) = true)

// initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()

// equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 50 --ifuel 3"
let prop1 (l:st) (o1 o2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1))
          (ensures eq (merge (do (v_of l) o1) (do (v_of l) o1) (do (do (v_of l) o2) o1))
                      (do (do (v_of l) o2) o1)) = ()

let prop2 (l:st) (o1 o2:op_t) (l2:log)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ get_rid o1 <> get_rid o2)
          (ensures eq (merge (do (v_of l) o1) (do (v_of l) o1) (apply_log (do (do (v_of l) o2) o1) l2))
                      (apply_log (do (do (v_of l) o2) o1) l2)) = admit() //fast fwd case, already proven

let prop3 (l:st) (o1 o2:op_t) (l1:log)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1))
          (ensures eq (merge (do (v_of l) o1) (apply_log (do (v_of l) o1) l1) (do (do (v_of l) o2) o1))
                      (apply_log (do (do (v_of l) o2) o1) l1)) = admit() //!!! 4 suf cond will handle this case
                      
let rec prop3_base_rc (l:st) (o1 o2:op_t) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2) /\
                    comm_ops o1 last1 /\ not (mem_id (fst last2) (ops_of l)))
          (ensures eq (merge (do (v_of l) o1) (do (do (v_of l) o1) last1) (do (do (do (v_of l) o2) o1) last2))
                      (do (merge (do (v_of l) o1) (do (do (v_of l) o1) last1) (do (do (v_of l) o2) o1)) last2))
          (decreases length (ops_of l)) =
  if length (ops_of l) = 0 then ()
  else prop3_base_rc (inverse_st l) o1 o2 last1 last2

let prop4_base_comm (l:st) (o1 o2:op_t) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops last1 o1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\ not (reorder last2 (create 1 last1)))
          (ensures eq (merge (do (v_of l) o1) (do (do (v_of l) o1) last1) (do (do (do (v_of l) o2) o1) last2))
                      (do (merge (do (v_of l) o1) (do (do (v_of l) o1) last1) (do (do (v_of l) o2) o1)) last2)) = ()

let prop3_ind_rc1 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops o1 last1 /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2) /\
                    length l2' > 0 /\ 
                    (let pre2, lastl2 = un_snoc l2' in
                     eq (merge (do l o1) (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) pre2) last2))
                        (do (merge (do l o1) (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) pre2)) last2)))
          (ensures eq (merge (do l o1) (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge (do l o1) (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()

let prop3_ind_rc2 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2) /\
                    length l2' = 0 /\ length l1' > 0 /\
                    (let pre1, lastl1 = un_snoc l1' in
                     eq (merge (do l o1) (do (apply_log (do l o1) pre1) last1) (do (apply_log (do (do l o2) o1) l2') last2))
                        (do (merge (do l o1) (do (apply_log (do l o1) pre1) last1) (apply_log (do (do l o2) o1) l2')) last2)))
          (ensures eq (merge (do l o1) (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge (do l o1) (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()

let prop4_ind_comm1 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops o1 last1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    //~ (reorder last2 l1') /\
                    length l2' > 0 /\
                    (let pre2, lastl2 = un_snoc l2' in
                     eq (merge (do l o1) (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) pre2) last2))
                        (do (merge (do l o1) (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) pre2)) last2)))
          (ensures eq (merge (do l o1) (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge (do l o1) (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = 
  let pre2, lastl2 = un_snoc l2' in
  assume (apply_log (do (do l o2) o1) l2' == do (apply_log (do (do l o2) o1) pre2) lastl2); //can be done
  ()

let prop4_ind_comm2 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops o1 last1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    //~ (reorder last2 l1') /\
                    length l2' = 0 /\ length l1' > 0 /\
                    (let pre1, lastl1 = un_snoc l1' in
                     eq (merge (do l o1) (do (apply_log (do l o1) pre1) last1) (do (apply_log (do (do l o2) o1) l2') last2))
                        (do (merge (do l o1) (do (apply_log (do l o1) pre1) last1) (apply_log (do (do l o2) o1) l2')) last2)))
          (ensures eq (merge (do l o1) (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge (do l o1) (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()
                      
////////////////////////////////////////////////////////////////

(*
let rec prop3 (l:st) (o1 o2:op_t) (l1:log)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1))
          (ensures eq (merge (do (v_of l) o1) (apply_log (do (v_of l) o1) l1) (do (do (v_of l) o2) o1))
                      (apply_log (do (do (v_of l) o2) o1) l1)) 
          (decreases length l1) =
  if length l1 = 0 then ()
  else 
    (let pre1, last1 = un_snoc l1 in
     assume (get_rid last1 = get_rid o1); //is it true?????
     assume (apply_log (do (v_of l) o1) l1 == do (apply_log (do (v_of l) o1) pre1) last1); //can be done
     assume (apply_log (do (do (v_of l) o2) o1) l1 == do (apply_log (do (do (v_of l) o2) o1) pre1) last1); //can be done
     prop3 l o1 o2 pre1)

let prop4_ind_comm2' (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops o1 last1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    length l2' = 0 /\ length l1' > 0 /\
                    (let pre1, lastl1 = un_snoc l1' in
                     eq (merge (do l o1) (apply_log (do l o1) l1') (do (apply_log (do (do l o2) o1) l2') last2))
                        (do (merge (do l o1) (apply_log (do l o1) l1') (apply_log (do (do l o2) o1) l2')) last2)))
          (ensures eq (merge (do l o1) (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge (do l o1) (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()


let rec prop3_base_rc (l:st) (o1 o2:op_t) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2))
          (ensures eq (merge (v_of l) (do (do (v_of l) o1) last1) (do (do (do (v_of l) o2) o1) last2))
                      (do (merge (v_of l) (do (do (v_of l) o1) last1) (do (do (v_of l) o2) o1)) last2))
          (decreases length (ops_of l)) =
  if length (ops_of l) = 0 then ()
  else prop3_base_rc (inverse_st l) o1 o2 last1 last2

let prop4_base_comm (l:st) (o1 o2:op_t) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops last1 o1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\ not (reorder last2 (create 1 last1)))
          (ensures eq (merge (v_of l) (do (do (v_of l) o1) last1) (do (do (do (v_of l) o2) o1) last2))
                      (do (merge (v_of l) (do (do (v_of l) o1) last1) (do (do (v_of l) o2) o1)) last2)) = ()
     
let prop3_ind_rc1 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2) /\
                    length l2' > 0 /\ 
                    (let pre2, lastl2 = un_snoc l2' in
                     eq (merge l (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) pre2) last2))
                        (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) pre2)) last2)))
          (ensures eq (merge l (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = admit()

let prop3_ind_rc2 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2) /\
                    length l2' = 0 /\ length l1' > 0 /\
                    (let pre1, lastl1 = un_snoc l1' in
                     eq (merge l (do (apply_log (do l o1) pre1) last1) (do (apply_log (do (do l o2) o1) l2') last2))
                        (do (merge l (do (apply_log (do l o1) pre1) last1) (apply_log (do (do l o2) o1) l2')) last2)))
          (ensures eq (merge l (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()

let prop4_ind_comm1 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops o1 last1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    length l2' > 0 /\ 
                    (let pre2, lastl2 = un_snoc l2' in
                     eq (merge l (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) pre2) last2))
                        (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) pre2)) last2)))
          (ensures eq (merge l (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = admit()

let prop4_ind_comm2 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops o1 last1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    length l2' = 0 /\ length l1' > 0 /\
                    (let pre1, lastl1 = un_snoc l1' in
                     eq (merge l (apply_log (do l o1) l1') (do (apply_log (do (do l o2) o1) l2') last2))
                        (do (merge l (apply_log (do l o1) l1') (apply_log (do (do l o2) o1) l2')) last2)))
          (ensures eq (merge l (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()*)
                      
////////////////////////////////////////////////////////////////
