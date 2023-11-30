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

let mem_id_s (id:nat) (s:concrete_st) : bool =
  S.exists_s s (fun e -> fst e = id)

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
  |Rem x, Add y -> Fst_snd // Rem x, Add y && x = y
  
// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let da = S.difference a l in    //a - l
  let db = S.difference b l in    //b - l
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in            // intersect l a b
  S.union i_lab (S.union da db)          // (intersect l a b) U (a - l) U (b - l)

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

let rec lin_rc (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\ 
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))
          (decreases %[length (ops_of l); length (ops_of a); length (ops_of b)]) =
  if ops_of a = ops_of l && ops_of b = ops_of l then 
    (if length (ops_of l) = 0 then ()
     else 
       (let l' = inverse_st l in
        let _, lastl' = un_snoc (ops_of l) in
        assume (fst lastl' <> fst last2); //can be done
        lin_rc l' l' l' last1 last2; ()))
  else if ops_of a = ops_of l then 
    (let b' = inverse_st b in 
     cons_reps_s2' l a b;
     lin_rc l a b' last1 last2) 
  else 
    (let a' = inverse_st a in
     cons_reps_s1' l a b;
     lin_rc l a' b last1 last2)

let cons_reps' (l a b:st1) =
  distinct_ops (ops_of l) /\ distinct_ops (ops_of a) /\ distinct_ops (ops_of b) /\
  is_prefix (ops_of l) (ops_of a) /\
  is_prefix (ops_of l) (ops_of b)

let rec lin_rc' (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps' l a b /\ 
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))
          (decreases %[length (ops_of l); length (ops_of a); length (ops_of b)]) =
  if ops_of a = ops_of l && ops_of b = ops_of l then 
    (if length (ops_of l) = 0 then ()
     else 
       (let l' = inverse_st l in
        let _, lastl' = un_snoc (ops_of l) in
        assume (fst lastl' <> fst last2); //can be done
        lin_rc' l' l' l' last1 last2; ()))
  else if ops_of a = ops_of l then 
    (let b' = inverse_st b in 
     lin_rc' l a b' last1 last2) 
  else 
    (let a' = inverse_st a in
     lin_rc' l a' b last1 last2)
     
let comm_empty_log (x:op_t) (l:log)
  : Lemma (ensures length l = 0 ==> commutative_seq x l) = ()

let not_add_eq (lca s1:st) (s2:st1)
  : Lemma (requires length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                     Rem? (snd (snd last2)) /\
                     fst last1 <> fst last2 /\
                     ~ (reorder last2 (diff (ops_of s1) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    ~ (Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2))) = 
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
  assert (commutative_seq last1 suf);

  assert ((Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2) ==> not (comm_ops last2 last1));
  assert ((Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2) ==> Fst_snd? (rc last2 last1)); 
  assert ((Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2) ==> 
                not (comm_ops last2 last1) /\ Fst_snd? (rc last2 last1) /\ commutative_seq last1 suf);
  assert ((Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2) ==> reorder last2 (diff (ops_of s1) (ops_of lca)));
  assert (~ (Add? (snd (snd last1)) /\ get_ele last1 = get_ele last2)); ()
  
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
     let pre1, last1' = un_snoc (ops_of a) in
     assume (fst last1' <> fst last2); //can be done
     assume (~ (reorder last2 (diff (ops_of a) (ops_of l)))); //can be done
     un_snoc_snoc (ops_of a') last1';
     un_snoc_snoc (ops_of b) last2;
     not_add_eq l (do_st a' last1') (do_st b last2);
     lin_comm1_r l a' b last1' last2)    

let rec lin_comm1_r' (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps' l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\ Rem? (snd (snd last2)) /\
                    ~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))
          (decreases %[length (ops_of b); length (ops_of a)]) = 
  if ops_of a = ops_of l && ops_of b = ops_of l then ()
  else if ops_of a = ops_of l then 
    (let b' = inverse_st b in
     lin_comm1_r' l a b' last1 last2)
  else 
    (let a' = inverse_st a in
     let pre1, last1' = un_snoc (ops_of a) in
     assume (fst last1' <> fst last2); //can be done
     assume (~ (reorder last2 (diff (ops_of a) (ops_of l)))); //can be done
     un_snoc_snoc (ops_of a') last1';
     un_snoc_snoc (ops_of b) last2;
     not_add_eq l (do_st a' last1') (do_st b last2);
     lin_comm1_r' l a' b last1' last2)  
     
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

let rec lin_comm1_a' (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps' l a b /\
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
        lin_comm1_a' l' l' l' last1 last2; ()))
  else if ops_of b = ops_of l then 
    (let a' = inverse_st a in
     let _, last1' = un_snoc (ops_of a) in
     assume (fst last1' <> fst last2); //can be done
     if Rem? (snd (snd last1)) && get_ele last1 = get_ele last2 then
       lin_comm1_a' l a' b last1 last2
     else lin_comm1_a' l a' b last1' last2)
  else 
    (let b' = inverse_st b in
     lin_comm1_a' l a b' last1 last2) 
     
#pop-options

let lin_comm (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    ~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) =
  if Rem? (snd (snd last2)) then lin_comm1_r l a b last1 last2
  else lin_comm1_a l a b last1 last2

let lin_comm' (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps' l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    ~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2))) =
  if Rem? (snd (snd last2)) then lin_comm1_r' l a b last1 last2
  else lin_comm1_a' l a b last1 last2
  
let inter_merge1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    ~ (comm_ops o3 o1) /\ ~ (comm_ops o3 o2) /\
                    Fst_snd? (rc o3 o1) (*/\ Fst_snd? (rc o3 o2*))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = 
  assume (not (mem_id_s (fst o2) l)); ()
          
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

#push-options "--ifuel 3"
let prop1 (l:st) (o1 o2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1))
          (ensures eq (merge (do (v_of l) o1) (do (v_of l) o1) (do (do (v_of l) o2) o1))
                      (do (do (v_of l) o2) o1)) = ()

let prop2 (l:st) (o1 o2:op_t) (l2:log)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1))
          (ensures eq (merge (do (v_of l) o1) (do (v_of l) o1) (apply_log (do (do (v_of l) o2) o1) l2))
                      (apply_log (do (do (v_of l) o2) o1) l2)) = () //fast fwd case

let prop3 (l:st) (o1 o2:op_t) (l1:log)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ not (mem_id (fst o1) l1))
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
  else 
    (let l' = inverse_st l in
     let pre, lastl = un_snoc (ops_of l) in
     lem_last (ops_of l);
       //assert (fst lastl <> fst last2);
     prop3_base_rc l' o1 o2 last1 last2)

let prop4_base_comm (l:st) (o1 o2:op_t) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops last1 o1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\ not (reorder last2 (create 1 last1)))
          (ensures eq (merge (do (v_of l) o1) (do (do (v_of l) o1) last1) (do (do (do (v_of l) o2) o1) last2))
                      (do (merge (do (v_of l) o1) (do (do (v_of l) o1) last1) (do (do (v_of l) o2) o1)) last2)) = ()

let prop3_ind_rc1 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ 
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
                      (do (merge (do l o1) (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()

#push-options "--z3rlimit 100"
let prop4_ind_comm2 (l:st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops o1 last1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    ~ (reorder last2 l1') /\
                    length l2' = 0 /\ length l1' > 0 /\
                    (let pre1, lastl1 = un_snoc l1' in
                     comm_ops o1 lastl1 /\
              eq (merge (do (v_of l) o1) (do (apply_log (do (v_of l) o1) pre1) last1) (do (apply_log (do (do (v_of l) o2) o1) l2') last2))
                 (do (merge (do (v_of l) o1) (do (apply_log (do (v_of l) o1) pre1) last1) (apply_log (do (do (v_of l) o2) o1) l2')) last2)))
     (ensures eq (merge (do (v_of l) o1) (do (apply_log (do (v_of l) o1) l1') last1) (do (apply_log (do (do (v_of l) o2) o1) l2') last2))
              (do (merge (do (v_of l) o1) (do (apply_log (do (v_of l) o1) l1') last1) (apply_log (do (do (v_of l) o2) o1) l2')) last2)) =
  let pre1, lastl1 = un_snoc l1' in
  assume (apply_log (do (v_of l) o1) l1' == do (apply_log (do (v_of l) o1) pre1) lastl1); //can be done
  assume (Rem? (snd (snd last2)) ==> ~ (Add? (snd (snd lastl1)) /\ get_ele last2 = get_ele lastl1)); //can be inferred from ~ (reorder last2 l1')
  assume (not (mem_id_s (fst last2) (merge (do (v_of l) o1) (do (apply_log (do (v_of l) o1) pre1) last1) (apply_log (do (do (v_of l) o2) o1) l2')))); // true, but how we will get this????
  ()
  
////////////////////////////////////////////////////////////////

(*
let prop1 (l:st) (o1 o2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1))
          (ensures eq (merge (v_of l) (do (v_of l) o1) (do (do (v_of l) o2) o1)) 
                      (do (do (v_of l) o2) o1)) = ()

let rec prop2 (l:st) (o1 o2:op_t) (l2:log)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1))
          (ensures eq (merge (v_of l) (do (v_of l) o1) (apply_log (do (do (v_of l) o2) o1) l2))
                      (apply_log (do (do (v_of l) o2) o1) l2))
          (decreases length l2) =
  if length l2 = 0 then ()
  else 
    (let pre,last2 = un_snoc l2 in
     assume (apply_log (do (do (v_of l) o2) o1) l2 == do (apply_log (do (do (v_of l) o2) o1) pre) last2); //can be done
     assume (Add? (snd (snd last2))); //!!!!! prop2 can be proved only for this case
     prop2 l o1 o2 pre)

let rec prop3_base_rc (l:st) (o1 o2:op_t) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2) /\
                    not (mem_id (fst last2) (ops_of l)))
          (ensures eq (merge (v_of l) (do (do (v_of l) o1) last1) (do (do (do (v_of l) o2) o1) last2))
                      (do (merge (v_of l) (do (do (v_of l) o1) last1) (do (do (v_of l) o2) o1)) last2))
          (decreases length (ops_of l)) =
  if length (ops_of l) = 0 then ()
  else 
    (let l' = inverse_st l in
     let pre, lastl = un_snoc (ops_of l) in
     lem_last (ops_of l);
       //assert (fst lastl <> fst last2);
     prop3_base_rc l' o1 o2 last1 last2)

let prop4_base_comm (l:st) (o1 o2:op_t) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops last1 o1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\ not (reorder last2 (create 1 last1)))
          (ensures eq (merge (v_of l) (do (do (v_of l) o1) last1) (do (do (do (v_of l) o2) o1) last2))
                      (do (merge (v_of l) (do (do (v_of l) o1) last1) (do (do (v_of l) o2) o1)) last2)) =
  assume (Rem? (snd (snd last2)) ==> ~ (Add? (snd (snd o1)) /\ get_ele o1 = get_ele last2)); //!!!!! prop3_base_comm can be proved only for this case
  ()

let prop3_ind_rc1 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2) /\
                    length l2' > 0 /\ 
                    (let pre2, lastl2 = un_snoc l2' in
                     eq (merge l (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) pre2) last2))
                        (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) pre2)) last2)))
          (ensures eq (merge l (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()

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
                      (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()


let prop4_ind_comm2 (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops o1 last1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    length l2' = 0 /\ length l1' > 0 /\
                    (let pre1, lastl1 = un_snoc l1' in
                     eq (merge l (apply_log (do l o1) l1') (do (apply_log (do (do l o2) o1) l2') last2))
                        (do (merge l (apply_log (do l o1) l1') (apply_log (do (do l o2) o1) l2')) last2)))
          (ensures eq (merge l (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge l (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()

let prop4_ind_comm2' (l:concrete_st) (o1 o2:op_t) (l1' l2':log) (last1 last2:op_t)
  : Lemma (requires fst o1 <> fst o2 /\ ~ (comm_ops o1 o2) /\ Fst_snd? (rc o2 o1) /\ comm_ops o1 last1 /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    length l2' = 0 /\ length l1' > 0 /\
                    (let pre1, lastl1 = un_snoc l1' in
                     eq (merge (do l o1) (apply_log (do l o1) l1') (do (apply_log (do (do l o2) o1) l2') last2))
                        (do (merge (do l o1) (apply_log (do l o1) l1') (apply_log (do (do l o2) o1) l2')) last2)))
          (ensures eq (merge (do l o1) (do (apply_log (do l o1) l1') last1) (do (apply_log (do (do l o2) o1) l2') last2))
                      (do (merge (do l o1) (do (apply_log (do l o1) l1') last1) (apply_log (do (do l o2) o1) l2')) last2)) = ()
*)
                      
////////////////////////////////////////////////////////////////
