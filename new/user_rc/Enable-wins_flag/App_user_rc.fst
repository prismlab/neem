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
#pop-options

let lin_comm (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    ~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) =
  lin_comm1 l a b last1 last2
                      
let inter_merge1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    ~ (comm_ops o3 o1) /\ ~ (comm_ops o3 o2) /\
                    Fst_snd? (rc o3 o1) /\ Fst_snd? (rc o3 o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

let inter_merge2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o2 <> fst o3 /\ fst o1 <> fst o3 /\
                    ~ (comm_ops o3 o1) /\ ~ (comm_ops o3 o2) /\
                    Fst_snd? (rc o3 o1) /\ Fst_snd? (rc o3 o2) /\
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
                    Fst_snd? (rc o3 o1) /\ Fst_snd? (rc o3 o2) /\ Fst_snd? (rc o4 o1) /\
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
