module App_new

#set-options "--query_stats"
module M = Map_extended
module S = Set_extended

type cf = (int & int)

let cond (s1:M.t nat cf) =
  forall rid. M.contains s1 rid ==> fst (M.sel s1 rid) >= snd (M.sel s1 rid)
 
// the concrete state type
type concrete_st = s:M.t nat cf//{cond s}

// init state
let init_st = M.const_on S.empty ((0,0))

let sel (s:concrete_st) k = if M.contains s k then M.sel s k else (0,0)

// equivalence between 2 concrete states
let eq (a b:concrete_st) = 
  (forall id. M.contains a id = M.contains b id /\ sel a id = sel b id)

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
  |Set
  |Reset

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st = 
  match o with
  |(ts, (rid, Set)) -> let v = sel s rid in M.upd s rid (fst v + 1, snd v)
  |(_, (rid, Reset)) -> M.map_val (fun (p,_) -> (p,p)) s

//conflict resolution
let rc (o1 o2:op_t) = 
  match snd (snd o1), snd (snd o2) with
  |Set, Reset -> Snd_then_fst
  |Reset, Set -> Fst_then_snd
  |_ -> Either

(*let merge_flag (l a b:cf) : bool =
  let lc = pctr l in
  let ac = pctr a in
  let bc = pctr b in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac > lc
          else bc > lc*)

let merge_snd (l a b:int & int) : int =
  let ls,lr = l in
  let as',ar = a in
  let bs,br = b in
  let m = min (min (ar - lr) (br - lr)) (ls - lr) in
  //let m' = lr + m in
  let r = ar + br - lr - m in   //lr + m + ar - m' + br - m'
  let f = as' + bs - ls in
  r
  //if r > f then f else r

  //ar -> total no. of sets reset in branch A
  //br -> total no. of sets reset in branch B 
  //lr -> total no. of LCA sets reset in LCA. we subtract lr from ar + br as 2 copies of lr will be present in ar + br
  //m -> this will give the no. of LCA sets not reset by LCA but reset by both branches. we subtract one copy of m from ar + br
            
// concrete merge operation
let merge_cf (l a b:cf) : cf =
  ((fst a + fst b - fst l, merge_snd l a b)(*, merge_flag l a b*))

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys ((0,0)) in
  let r = M.iter_upd (fun k v -> merge_cf (sel l k) (sel a k) (sel b k)) u in
  //assume (cond r);  
  r

/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 100 --ifuel 3"
let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Set? (snd (snd o1)) /\ Reset? (snd (snd o2))) ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1)))) = ()
         
let rc_non_comm_help2 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Reset? (snd (snd o1)) /\ Set? (snd (snd o2))) ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1)))) = ()
          
let rc_non_comm o1 o2 =
  rc_non_comm_help1 o1 o2;
  rc_non_comm_help2 o1 o2
          
let no_rc_chain o1 o2 o3 = ()

let cond_comm_base s o1 o2 o3 = ()

let cond_comm_ind s o1 o2 o3 o l = ()

/////////////////////////////////////////////////////////////////////////////
// Merge commutativity
let merge_comm l a b = ()

let merge_idem_base (_:unit)
  : Lemma (ensures eq (merge init_st init_st init_st) init_st) = ()

let merge_idem_ind (s:concrete_st) (o:op_t)
  : Lemma (requires eq (merge s s s) s)
          (ensures (eq (merge (do s o) (do s o) (do s o)) (do s o))) = ()

// Merge idempotence
let merge_idem (s:concrete_st)
   : Lemma (ensures eq (merge s s s) s) = admit()

///////////////////////////////////////////////////////////////////////////

let base_2op o1 o2 = ()

let ind_lca_2op l o1 o2 ol = ()

let inter_right_base_2op l a b o1 o2 ob ol = () 
     
let inter_left_base_2op l a b o1 o2 ob ol = ()

let inter_right_2op l a b o1 o2 ob ol o = ()

let inter_left_2op l a b o1 o2 ob ol o = ()

let ind_right_2op l a b o1 o2 o2' = ()

let ind_left_2op l a b o1 o2 o1' = ()

let base_1op o1 = ()

let ind_lca_1op l o1 ol = ()

let inter_right_base_1op l a b o1 ob ol = admit()

//l=2,1 a=0,0 b=2,0 ol=set o1=ob=reset
let inter_right_base_1op' (l a b :concrete_st) (o1 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    //Fst_then_snd? (rc ob o1) /\
                    (Fst_then_snd? (rc ob o1) ==> eq (merge l (do a o1) (do b ob)) (do (merge l a (do b ob)) o1)) /\ //from app.fsti
                    //eq (merge l (do a o1) (do b ob)) (do (merge l a (do b ob)) o1) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ob) ol)) (do (merge (do l ol) (do a ol) (do (do b ob) ol)) o1)) = admit()
          
(*let inter_right_base_1op' (l a b :concrete_st) (o1 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (Fst_then_snd? (rc ob o1) ==> eq (merge l (do a o1) (do b ob)) (do (merge l a (do b ob)) o1)) /\ //from app.fsti
                    eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ob) ol)) (do (merge (do l ol) (do a ol) (do (do b ob) ol)) o1)) = ()
          
let inter_right_base_1op' (l a b :concrete_st) (o1 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (forall id. fst (sel a id) >= fst (sel l id)) /\
                    (forall id. fst (sel b id) >= fst (sel l id)) /\
                    //(Fst_then_snd? (rc ob o1) ==> eq (merge l (do a ob) (do b o1)) (do (merge l (do a ob) b) o1) /\
                      //                            eq (merge l (do a o1) (do b ob)) (do (merge l a (do b ob)) o1)) /\ //from app.fsti
                    //eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (merge l (do a ob) b) ol) /\ //zero_op_inter_base_left 
                    eq (merge l (do a o1) b) (do (merge l a b) o1) /\ //from pre-cond of ind_right_2op
                    //eq (merge l (do a ob) (do b ol)) (do (merge l (do a ob) b) ol) /\
                    //eq (merge (do l ol) (do (do l ol) o1) (do (do l ob) ol)) (do (merge (do l ol) (do l ol) (do (do l ob) ol)) o1) /\
                    //eq (merge l (do a o1) (do b ob) ) (do (merge l a (do b ob)) o1) /\
                    //eq (merge l (do a o1) (do b ol)) (do (merge l a (do b ol)) o1) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ob) ol)) (do (merge (do l ol) (do a ol) (do (do b ob) ol)) o1)) = ()*)

let inter_left_base_1op l a b o1 ob ol = ()

let inter_right_1op l a b o1 ob ol o = ()

let inter_left_1op l a b o1 ob ol o = admit()

let inter_left_1op' (l a b:concrete_st) (o1 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge l (do (do (do a o) ob) o1) b) (do (merge l (do (do a o) ob) b) o1) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do a ob) ol) (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) o1)) = ()

//l = 0,0 a = 0,0 b = 2,2 ol = set o1' = set o1 = reset
let ind_left_1op l a b o1 o1' ol = admit()

let ind_left_1op' (l a b:concrete_st) (o1 o1' ol:op_t)
  : Lemma (requires ~ (Fst_then_snd? (rc o1 ol)) /\
                    eq (merge (do l ol) (do a o1) (do b ol)) (do (merge (do l ol) a (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do a o1') o1) (do b ol)) (do (merge (do l ol) (do a o1') (do b ol)) o1)) = ()
          
let ind_right_1op l a b o2 o2' ol = admit()

let ind_right_1op' (l a b:concrete_st) (o2 o2' ol:op_t)
  : Lemma (requires ~ (Fst_then_snd? (rc o2 ol)) /\
                    eq (merge (do l ol) (do a ol) (do b o2)) (do (merge (do l ol) (do a ol) b) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do b o2') o2)) (do (merge (do l ol) (do a ol) (do b o2')) o2)) = ()
          
let lem_0op l a b ol = admit()

let ind_lca_0op (l:concrete_st) (ol:op_t)
  : Lemma (requires eq (merge l l l) l)
          (ensures eq (merge (do l ol) (do l ol) (do l ol)) (do (merge l l l) ol)) = ()

//l=0,0 a=2,2 b=2,0 
let inter_right_base_0op (l a b :concrete_st) (ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops ob ol /\
                    eq (merge l (do a ol) b) (do (merge l a b) ol) /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do (merge l a b) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (merge l a (do b ob)) ol)) = admit()

let inter_left_base_0op (l a b:concrete_st) (ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do (merge l a b) ol))
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (merge l (do a ob) b) ol)) = admit()

let inter_right_0op (l a b:concrete_st) (ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (merge l a (do b ob)) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (merge l a (do (do b o) ob)) ol)) = ()

let inter_left_0op (l a b:concrete_st) (ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (merge l (do a ob) b) ol))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (merge l (do (do a o) ob) b) ol)) = ()
