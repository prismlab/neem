module App_new

module M = Map_extended
module S = Set_extended

#set-options "--query_stats"

type concrete_st_l = (nat & nat)

let sel (s:M.t nat ((int & bool) & concrete_st_l)) k = if M.contains s k then M.sel s k else ((0,false), (0,0))

// the concrete state type
type concrete_st = s:M.t nat ((int & bool) & concrete_st_l)
                   {forall id. M.contains s id ==> (snd (fst (sel s id)) = false <==> snd (sel s id) = (0,0))}

let init_st_l : concrete_st_l = (0,0)

// init state
let init_st = M.const_on S.empty ((0, false), init_st_l)
  
// equivalence between 2 concrete states
let eq (a b:concrete_st) = 
  forall id. M.contains a id = M.contains b id /\ sel a id = sel b id

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
  |Set : nat -> app_op_t
  |Unset

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =  
  match o with
  |(ts, (rid, Set v)) -> M.upd s rid ((fst (fst (sel s rid)) + 1, true), (ts,v))
  |(_, (_, Unset)) -> M.map_val (fun ((c,f), (ts,v)) -> ((c, false), init_st_l)) s

//conflict resolution
let rc (o1 o2:op_t) = 
  match snd (snd o1), snd (snd o2) with
  |Set _, Unset -> Snd_then_fst
  |Unset, Set _ -> Fst_then_snd
  |_ -> Either

let merge_l (l a b:concrete_st_l) : concrete_st_l =
  if fst a = fst b then (fst a, (snd a + snd b)/2)
  else if fst a > fst b then a else b

let merge_flag (l a b:(int & bool)) : bool =
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
let merge_cf (l a b:(int & bool)) : (int & bool) =
  (fst a + fst b - fst l, merge_flag l a b)

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun k v -> let mf = merge_cf (fst (sel l k)) (fst (sel a k)) (fst (sel b k)) in
                      let ml = if not (snd mf) then init_st_l
                               else if snd mf && not (snd (fst (sel a k))) then snd (sel b k)
                               else if snd mf && not (snd (fst (sel b k))) then snd (sel a k)
                               else merge_l (snd (sel l k)) (snd (sel a k)) (snd (sel b k)) in
                      (mf, ml)) u
    
/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 50 --ifuel 3"
let rc_non_comm_help1 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Set? (snd (snd o1)) /\ Unset? (snd (snd o2))) ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1)))) = ()
         
let rc_non_comm_help2 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures ((Unset? (snd (snd o1)) /\ Set? (snd (snd o2))) ==> ~ (eq (do (do init_st o1) o2) (do (do init_st o2) o1)))) = ()
          
let rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = admit()

let rc_non_comm' (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ get_rid o1 <> get_rid o2)
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
  
let merge_comm' (l a b:concrete_st)
   : Lemma (ensures (eq (merge l a b) (merge l b a))) =
   let lhs = merge l a b in
   let rhs = merge l b a in
   assert (forall k. M.contains lhs k = M.contains rhs k);
   assert (forall k. fst (sel lhs k) = fst (sel rhs k));
   //assume (forall k. M.contains lhs k ==> (fst (snd (sel lhs k)) = fst (snd (sel rhs k)) ==> snd (snd (sel lhs k)) = snd (snd (sel rhs k))));
   assert (forall k. snd (snd (sel lhs k)) = snd (snd (sel rhs k)));
   ()

// Merge idempotence
let merge_idem (s:concrete_st)
   : Lemma (ensures eq (merge s s s) s) = ()

let base_2op o1 o2 = ()

let ind_lca_2op l o1 o2 ol = admit()

let ind_lca_2op' (l:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    eq (merge (do l ol) (do (do l ol) o1) (do l ol)) (do (merge (do l ol) (do l ol) (do l ol)) o1) /\ //EXTRA!! ind_lca_1op
                    eq (merge l (do l o1) (do l o2)) (do (merge l l (do l o2)) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (merge (do l ol) (do l ol) (do (do l ol) o2)) o1)) = ()

#set-options "--z3rlimit 300 --ifuel 3 --split_queries always"
let inter_right_base_2op l a b o1 o2 ob ol = ()
     
let inter_left_base_2op l a b o1 o2 ob ol = ()

let inter_right_2op l a b o1 o2 ob ol o = ()

let inter_left_2op l a b o1 o2 ob ol o = ()

let inter_lca_2op l a b o1 o2 ol = ()

let ind_right_2op l a b o1 o2 o2' = ()

let ind_left_2op l a b o1 o2 o1' = ()

let base_1op o1 = ()

let ind_lca_1op l o1 ol = admit()

let ind_lca_1op' (l:concrete_st) (o1 ol:op_t)
  : Lemma (requires distinct_ops o1 ol /\ 
                    (get_rid o1 <> get_rid ol \/ fst ol < fst o1) /\ //EXTRA!!
                    eq (merge l (do l o1) l) (do (merge l l l) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do l ol)) (do (merge (do l ol) (do l ol) (do l ol)) o1)) = ()
          
let inter_right_base_1op l a b o1 ob ol = ()
     
let inter_left_base_1op l a b o1 ob ol = ()

let inter_right_1op l a b o1 ob ol o = ()

let inter_left_1op l a b o1 ob ol o = ()

let inter_lca_1op l a b o1 ol oi = ()             

let ind_left_1op l a b o1 o1' ol = ()

let ind_right_1op l a b o2 o2' ol = ()

let lem_0op l a b ol = ()
