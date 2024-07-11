module App_new

module S = Set_extended

#set-options "--query_stats"

// the concrete state type
type concrete_st = S.t (pos & (nat & nat)) //set of (timestamp, (key, value))

// init state
let init_st : concrete_st = S.empty
  
// equivalence between 2 concrete states
let eq (a b:concrete_st) = a == b

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
  |Set : nat -> nat -> app_op_t //key-value pair
  |Del : nat -> app_op_t //key

let get_key (o:op_t) : nat =
  match snd (snd o) with
  |Set k v -> k
  |Del k -> k
  
// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |(ts, (_, Set k v)) -> S.add (ts, (k,v)) s 
  |(_, (_, Del k)) -> S.filter s (fun e -> fst (snd e) <> k)

//conflict resolution
let rc (o1 o2:op_t) =
  match snd (snd o1), snd (snd o2) with
  |Set k1 v2, Del k2 -> if k1 = k2 then Snd_then_fst else Either 
  |Del k1, Set k2 v2 -> if k1 = k2 then Fst_then_snd else Either
  |_ -> Either

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let da = S.difference a l in    //a - l
  let db = S.difference b l in    //b - l
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in   // intersect l a b
  S.union i_lab (S.union da db) 

/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 300 --ifuel 3"
let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Set? (snd (snd o1)) /\ Del? (snd (snd o2)) /\ get_key o1 = get_key o2) ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1)))) = ()

let rc_non_comm_help2 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Del? (snd (snd o1)) /\ Set? (snd (snd o2)) /\ get_key o1 = get_key o2) ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1)))) = ()
          
let rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = 
  rc_non_comm_help1 o1 o2;
  rc_non_comm_help2 o1 o2

let no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3))) = ()

let cond_comm_base (s:concrete_st) (o1 o2 o3:op_t) 
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ distinct_ops o1 o3 /\
                    Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3)) = ()

let cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:seq op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3 /\ 
                    Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)) /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3)) = ()
          
/////////////////////////////////////////////////////////////////////////////
// Merge commutativity
let merge_comm (l a b:concrete_st)
   : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

// Merge idempotence
let merge_idem (s:concrete_st)
   : Lemma (ensures eq (merge s s s) s) = ()

///////////////////////////////////////////////////////////////////////////

let base_2op o1 o2 = ()

let ind_lca_2op l o1 o2 ol = ()

let inter_right_base_2op l a b o1 o2 ob ol = ()
     
let inter_left_base_2op l a b o1 o2 ob ol = ()

let inter_right_2op l a b o1 o2 ob ol o = ()

let inter_left_2op l a b o1 o2 ob ol o = ()

let inter_lca_2op l a b o1 o2 ol = ()

let ind_right_2op l a b o1 o2 o2' = ()

let ind_left_2op l a b o1 o2 o1' = ()

let base_1op o1 = ()

let ind_lca_1op l o1 ol = ()

let inter_right_base_1op l a b o1 ob ol = ()
     
let inter_left_base_1op l a b o1 ob ol = ()

let inter_right_1op l a b o1 ob ol o = ()

let inter_left_1op l a b o1 ob ol o = ()

let inter_lca_1op l a b o1 ol oi = ()
           
let ind_left_1op l a b o1 o1' ol = ()

let ind_right_1op l a b o2 o2' ol = ()

let lem_0op l a b ol = ()
