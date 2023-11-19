module App_user_rc

module S = Set_extended_new

#set-options "--query_stats"

// the concrete state type
type concrete_st = S.t (pos & nat) // (timestamp, ele) //timestamps are unique

// init state
let init_st : concrete_st = S.empty

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  S.equal a b

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

let get_ele (o:op_t) : nat =
  match snd (snd o) with
  |Add e -> e
  |Rem e -> e
  
// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |(ts, (rid, Add e)) -> S.insert (ts, e) s 
  |(_, (rid, Rem e)) -> S.filter s (fun ele -> snd ele <> e)
  
let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()

//operations x and y are commutative
let comm_ops (x y:op_t) : bool =
  match snd (snd x), snd (snd y) with
  |Add x, Rem y -> if x = y then false else true
  |Rem x, Add y -> if x = y then false else true
  |_ -> true

// if x and y are commutative ops, applying them in any order should give equivalent results
let commutative_prop (x y:op_t) 
  : Lemma (requires comm_ops x y)
          (ensures (forall s. eq (apply_log s (cons x (cons y empty))) (apply_log s (cons y (cons x empty))))) = ()

//conflict resolution
let rc (x:op_t) (y:op_t{fst x <> fst y /\ ~ (comm_ops x y)}) : rc_res =
  match snd (snd x), snd (snd y) with
  |Add x, Rem y -> if x = y then Snd_fst else Fst_snd
  |Rem x, Add y -> Snd_fst // Rem x, Add y && x = y
  
// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let da = S.difference a l in    //a - l
  let db = S.difference b l in    //b - l
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in            // intersect l a b
  S.union i_lab (S.union da db)          // (intersect l a b) U (a - l) U (b - l)

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

let fast_fwd_ind (a b:st) (last2:op_t)
  : Lemma (requires length (ops_of b) > length (ops_of a) /\
                    (let b' = inverse_st b in
                    cons_reps a a b' /\
                    eq (do (v_of b') last2) (merge (v_of a) (v_of a) (do (v_of b') last2))))
        
          (ensures eq (do (v_of b) last2) (merge (v_of a) (v_of a) (do (v_of b) last2))) = ()
  
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

let rec lin_comm1_r (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\ Rem? (snd (snd last2)) /\
                    ~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))
          (decreases %[length (ops_of b); length (ops_of a)]) = 
  if ops_of a = ops_of l && ops_of b = ops_of l then ()
  else if ops_of a = ops_of l then 
    (let b' = inverse_st b in
     lin_comm1_r l a b' last1 last2)
  else 
    (let a' = inverse_st a in
     cons_reps_s1' l a b;
     let _, last1' = un_snoc (ops_of a) in
     assume (fst last1' <> fst last2); //can be done
     assume (~ (reorder last2 (diff (snoc (ops_of a') last1') (ops_of l)))); //can be done
     assume (Rem? (snd (snd last1')) \/ (Add? (snd (snd last1')) /\ get_ele last1' <> get_ele last2)); //above one implies this
     lin_comm1_r l a' b last1' last2)    

let rec lin_comm1_a (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\
                    fst last1 <> fst last2 /\ Add? (snd (snd last2)))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))
          (decreases %[length (ops_of l); length (ops_of a); length (ops_of b)]) = 
  if ops_of a = ops_of l && ops_of b = ops_of l then 
    (if length (ops_of l) = 0 then ()
     else 
       (let l' = inverse_st l in
        let _, lastl' = un_snoc (ops_of l) in
        assume (fst lastl' <> fst last2); //can be done
        lin_comm1_a l' l' l' last1 last2; ()))
  else if ops_of b = ops_of l then 
    (let a' = inverse_st a in
     let _, last1' = un_snoc (ops_of a) in
     cons_reps_s1' l a b;
     assume (fst last1' <> fst last2); //can be done
     if Rem? (snd (snd last1)) && get_ele last1 = get_ele last2 then
       lin_comm1_a l a' b last1 last2
     else lin_comm1_a l a' b last1' last2)
  else 
    (let b' = inverse_st b in
     cons_reps_s2' l a b;
     lin_comm1_a l a b' last1 last2)  
#pop-options

let lin_comm (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    ~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) =
  if Rem? (snd (snd last2)) then lin_comm1_r l a b last1 last2
  else lin_comm1_a l a b last1 last2
                      
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
let concrete_st_s = S.t nat

// init state 
let init_st_s = S.empty

// apply an operation to a state 
let do_s (st_s:concrete_st_s) (o:op_t) : concrete_st_s =
  match o with
  |(ts, (rid, Add e)) -> S.insert e st_s
  |(_, (rid, Rem e)) -> S.filter st_s (fun ele -> ele <> e)

let mem_ele (ele:nat) (s:concrete_st) : bool =
  S.exists_s s (fun e -> snd e = ele)
  
// equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  (forall e. S.mem e st_s <==> mem_ele e st)

// initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()
  
// equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = 
  if Add? (snd (snd op)) then 
    (if S.mem (get_ele op) st_s then () else ()) 
  else ()

////////////////////////////////////////////////////////////////
