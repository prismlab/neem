module App

#set-options "--query_stats"
module M = Map_extended
module S = Set_extended

type cf = ((int & int) & bool)

let pctr (c:cf) =
  let ((p,_),_) = c in p

let nctr (c:cf) =
  let ((_,n),_) = c in n

let flag (c:cf) =
  let ((_,_),f) = c in f

let cond (s1:M.t nat cf) =
  forall rid. M.contains s1 rid ==> pctr (M.sel s1 rid) >= nctr (M.sel s1 rid)
 
// the concrete state type
type concrete_st = s:M.t nat cf{cond s}

// init state
let init_st = M.const_on S.empty ((0,0), false)

let sel (s:concrete_st) k = if M.contains s k then M.sel s k else ((0,0), false)

// equivalence between 2 concrete states
let eq (a b:concrete_st) = 
  (forall id. M.contains a id = M.contains b id /\ sel a id == sel b id)

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
  |(ts, (rid, Set)) -> let v = sel s rid in M.upd s rid ((pctr v + 1, nctr v), true)
  |(_, (rid, Reset)) -> M.map_val (fun ((p,_),_) -> ((p,p), false)) s

//conflict resolution
let rc (o1 o2:op_t) = 
  match snd (snd o1), snd (snd o2) with
  |Set, Reset -> Snd_then_fst
  |Reset, Set -> Fst_then_snd
  |_ -> Either

let merge_flag (l a b:cf) : bool =
  let lc = pctr l in
  let ac = pctr a in
  let bc = pctr b in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac > lc
          else bc > lc

let merge_snd (l a b:int & int) : int =
  let ls,lr = l in
  let as',ar = a in
  let bs,br = b in
  let m = min (min (ar - lr) (br - lr)) (ls - lr) in
  //let m' = lr + m in
  let r = ar + br - lr - m in   //lr + m + ar - m' + br - m'
  let f = as' + bs - ls in
  if r > f then f else r

  //ar -> total no. of sets reset in branch A
  //br -> total no. of sets reset in branch B 
  //lr -> total no. of LCA sets reset in LCA. we subtract lr from ar + br as 2 copies of lr will be present in ar + br
  //m -> this will give the no. of LCA sets not reset by LCA but reset by both branches. we subtract one copy of m from ar + br
  

  (*if l = a && l = b then lr
  else if l = (0,0) then ar + br
  else if l = a then br 
  else if l = b then ar 
  else if as' = ar && bs = br then as' + bs - ls 
  else if ls = lr then ar + br - lr else
  
  //if ar = ls then max ar br else if br = ls then max ar br else
  //let r = if lr = ar || lr = br then 0 else ls - lr in
  (ar + br - ls)*)
  (*if ar = ls then max ar br else if br = ls then max ar br else
  //if ls = lr then ar + br - lr else
  let m = min (min ar br) lr in
  m + ar - m + br - m*)
  (*let a' = if ar < ls -lr then 0 else ar - (ls - lr) in
  let b' = if br < ls -lr then 0 else br - (ls - lr) in
  let m = if ar < ls - lr || br < ls - lr then max (ls -lr) (max ar br)
          else min (min ar br) (ls - lr) in
  if ls = lr then a' + b' - lr
  else
  a' + b' + m*)
  
  (*if l = (0,0) then ar + br
  else if l = a then br
  else if l = b then ar
  else if as' = ar && bs = br then as' + bs - ls
  else if a = b then  (as' + bs - ls) //(ar + br - lr)
  else let s = as' + bs - ls in
  let a' = if as' = ar then ar else if as' = s then 0 else as' - ar in
  let b' = if bs = br then br else if bs = s then 0 else bs - br in
   (a' + b' )*)

  //min (as' + bs - ls - (as' - ar) - (bs - br)) (ar + br)
  //max ar br
  
  (*if l = a then br else if l = b then ar else
  if lr = ar && lr = br then if as' + bs - ls < lr then  as' + bs - ls else lr 
  else if ar = br then if as' + bs - ls < ar then as' + bs - ls else ar 
  //else if lr = ar then br else if lr = br then ar else
  else 
    (let r = if ls = lr then ar + br - ls else ar + br - lr in
     if as' + bs - ls < r //- (ls - lr) - lr
    then as' + bs - ls 
    else r)*)
  (*if as' = ar then (ar + br - ls + lr)
  else if bs = br then (ar + br - ls + lr)
  else if lr = ar && lr = br then lr
  else if lr = ar then max ar br
  else max ar br*)
        
  (*let ls = fst (fst l) in
  let lr = snd (fst l) in
  let as' = fst (fst a) in
  let ar = snd (fst a) in
  let bs = fst (fst b) in
  let br = snd (fst b) in
  if fst l = fst a then br 
  else if fst l = fst b then ar else
  (let r = ar + br - lr in
  let s = as' + bs - ls in
  if r = s && (as' > ar || bs > br) then if ar + br - (ls - lr) > s then s else ar + br - (ls - lr) else
  if r > s then s else r)*)
  //max ar br
  (*if fst a = (0,0) then br else if fst b = (0,0) then ar 
  else if fst l = (0,0) then ar + br 
  else if as' = ar &&  bs = br then as' + bs - ls 
  else if as' = ar then br else if bs = br then ar else
  (max ar br) *)
  
        
(*let merge_snd (l a b:cf) : int =
  
  let (l_sets_seen, l_sets_cancelled) = fst l in
  let (a_sets_seen, a_sets_cancelled) = fst a in
  let (b_sets_seen, b_sets_cancelled) = fst b in
  let avg_sets_seen = (a_sets_seen + b_sets_seen - l_sets_seen) in /// 2 in
  let avg_sets_cancelled = (a_sets_cancelled + b_sets_cancelled - l_sets_cancelled) in // / 2 in
  if a_sets_seen = b_sets_seen && a_sets_cancelled = b_sets_cancelled then a_sets_cancelled
  else if a_sets_seen = l_sets_seen && a_sets_cancelled = l_sets_cancelled then b_sets_cancelled
  else if b_sets_seen = l_sets_seen && b_sets_cancelled = l_sets_cancelled then a_sets_cancelled
  else if avg_sets_seen = a_sets_seen && avg_sets_cancelled = a_sets_cancelled then a_sets_cancelled
  else if avg_sets_seen = b_sets_seen && avg_sets_cancelled = b_sets_cancelled then b_sets_cancelled
  else if avg_sets_seen = l_sets_seen && avg_sets_cancelled = l_sets_cancelled then l_sets_cancelled
  else avg_sets_cancelled*)

          
// concrete merge operation
let merge_cf (l a b:cf) : cf =
  ((pctr a + pctr b - pctr l, merge_snd (fst l) (fst a) (fst b)), merge_flag l a b)

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

(*Two OP RC*)
//////////////// 
#set-options "--z3rlimit 500 --ifuel 5"

let lem_st s : prop = (forall id. snd (sel s id) = false <==> fst (fst (sel s id)) = snd (fst (sel s id)))

let merge_pre (l a b:concrete_st) : prop =
  (forall id. M.contains l id <==> (M.contains a id /\ M.contains b id)) /\
  (forall id. M.contains l id ==> pctr (sel l id) <= pctr (sel a id) /\ pctr (sel l id) <= pctr (sel b id) /\
                             nctr (sel l id) <= nctr (sel a id) /\ nctr (sel l id) <= nctr (sel b id)) 

let rc_ind_right_pre (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    merge_pre l (do a o1) (do b o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()
          
let rc_ind_right' (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2) /\ //one_op_ind_right
                      //eq (merge l (do a o2) (do b o1)) (do (merge l a (do b o1)) o2) /\ //new
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = ()

let rc_ind_left_pre  (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    merge_pre l (do a o1) (do b o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()
          
let rc_ind_left' (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

let rc_ind_lca' (l:concrete_st) (o1 o2 o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()

let rc_base' (o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let rc_inter_base_right_pre (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    merge_pre (do l ol) (do (do a ol) o1) (do (do b ol) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()
          
let rc_inter_base_right' (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2) /\ //one_op_inter_base_right
                      //eq (merge (do l ol) (do (do a ol) o2) (do (do b ol) o1)) (do (do (do c ol) o1) o2) /\ //new
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let rc_inter_base_left' (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let rc_inter_right_pre (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    merge_pre (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()
      
let rc_inter_right' (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                      //eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2) /\ //one_op_inter_right
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let rc_inter_left_pre (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    merge_pre (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()
      
let rc_inter_left' (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                      //eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2) /\ //new
                    eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2) /\ //one_op_inter_left
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let rc_inter_lca_pre  (l a b c:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    merge_pre (do l oi) (do (do a oi) o1) (do (do b oi) o2) /\
                    merge_pre (do l ol) (do (do a ol) o1) (do (do b ol) o2) /\
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) = ()

let rc_inter_lca' (l a b c:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2) /\ //one_op_inter_lca
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) = ()

(*One op*)
///////////////
//l = 1,1, a = 2,1, b = 0,0, o2 = reset, o2' = set
//and then try el(eb(e'(l)))
//passes with pre-cond
let one_op_ind_right' (l a b c:concrete_st) (o2 o2' ob ol:op_t)
   : Lemma (requires //merge_pre l a b /\ //extra PRE!!
                     Fst_then_snd? (rc ob ol) /\ 
                     eq (merge (do l ol) (do (do l ob) ol) (do b o2)) (do (merge (do l ol) (do (do l ob) ol) b) o2))
           (ensures eq (merge (do l ol) (do (do l ob) ol) (do (do b o2') o2)) (do (merge (do l ol) (do (do l ob) ol) (do b o2')) o2)) = ()

let one_op_ind_right'' (l a b c:concrete_st) (o2 o2' ob ol o:op_t)
   : Lemma (requires //merge_pre l a b /\ //extra PRE!!
                     Fst_then_snd? (rc ob ol) /\ 
                     eq (merge (do l ol) (do (do (do l o) ob) ol) (do b o2)) (do (merge (do l ol) (do (do (do l o) ob) ol) b) o2) /\
                     eq (merge (do l ol) (do (do l ob) ol) (do (do b o2') o2)) (do (merge (do l ol) (do (do l ob) ol) (do b o2')) o2))
           (ensures eq (merge (do l ol) (do (do (do l o) ob) ol) (do (do b o2') o2)) 
                       (do (merge (do l ol) (do (do (do l o) ob) ol) (do b o2')) o2)) = ()

let one_op_ind_right' (l a b c:concrete_st) (o2 o2' ob ol:op_t)
   : Lemma (requires //merge_pre l a b /\ //extra PRE!!
                     Fst_then_snd? (rc ob ol) /\ 
                     eq (merge (do l ol) (do (do l ob) ol) (do b o2)) (do (merge (do l ol) (do (do l ob) ol) b) o2))
           (ensures eq (merge (do l ol) (do (do l ob) ol) (do (do b o2') o2)) (do (merge (do l ol) (do (do l ob) ol) (do b o2')) o2)) = ()
           
//passes with pre-cond
let one_op_ind_left' (l a b c:concrete_st) (o1 o1' ob ol:op_t)
   : Lemma (requires merge_pre l (do a o1) b /\ //extra PRE!!
                     eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) = ()

let one_op_ind_lca' (l:concrete_st) (o2 o:op_t)
  : Lemma (requires eq (merge l l (do l o2)) (do l o2))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o2)) (do (do l o) o2)) = ()

let one_op_base' (o2:op_t)
  : Lemma (ensures eq (merge init_st init_st (do init_st o2)) (do init_st o2)) = ()

let one_op_inter_base_right_pre (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    lem_st l /\ lem_st a /\ lem_st b /\ lem_st c /\
                    merge_pre (do l ol) (do a ol) (do (do b ol) o2) /\ merge_pre l a (do b o2) /\
                    merge_pre l (do a ol) (do b ob) /\
                    merge_pre (do l ol) (do a ol) (do (do (do b ob) ol) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) = admit()
 
let one_op_inter_base_right' (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                       //eq (merge l a (do (do b ob) o2)) (do (merge l a (do b ob)) o2) /\ //EXTRA!!
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //rc_ind_right
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol) /\ //zero_op_inter_base_right
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) = ()

let one_op_inter_base_left_pre  (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    lem_st l /\ lem_st a /\ lem_st b /\ lem_st c /\
                    merge_pre (do l ol) (do a ol) (do (do b ol) o2) /\ merge_pre l a (do b o2) /\
                    merge_pre l (do a ob) (do b o2) /\ merge_pre l (do a ob) (do b ol) /\
                    merge_pre (do l ol) (do (do a ob) ol) (do (do b ol) o2) /\ merge_pre l (do a o2) (do b ob) /\ merge_pre l a (do b ob) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ 
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ //EXTRA!! 
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) = admit()

let one_op_inter_base_left' (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //rc_ind_right
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol) /\ //zero_op_inter_base_left
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ 
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) = ()

let one_op_inter_right_pre (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    merge_pre (do l ol) (do a ol) (do (do (do b ob) ol) o2) /\
                    merge_pre (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) = admit()
          
let one_op_inter_right' (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol) /\ //zero_op_inter_right
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) = ()

let one_op_inter_left_pre (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    merge_pre (do l ol) (do (do a ob) ol) (do (do b ol) o2) /\
                    merge_pre (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) = ()
          
let one_op_inter_left' (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol) /\ //zero_op_inter_left
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) = ()

let one_op_inter_lca_pre (l a b c:concrete_st) (o2 ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    merge_pre (do l oi) (do a oi) (do (do b oi) o2) /\ merge_pre (do l ol) (do a ol) (do (do b ol) o2) /\
                    merge_pre (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2) /\
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) = admit()
          
let one_op_inter_lca' (l a b c:concrete_st) (o2 ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol) /\ //zero_op_inter_lca_v2
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) = ()

(*Zero op *)
///////////////
let zero_op_inter_base_right_pre (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    lem_st l /\ lem_st a /\ lem_st b /\ lem_st c /\
                    merge_pre (do l ol) (do a ol) (do b ol) /\ merge_pre l a b /\
                    merge_pre l (do a ol) (do b ob) /\ merge_pre (do l ol) (do a ol) (do (do b ob) ol) /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) = admit()
          
let zero_op_inter_base_right' (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol) /\ //pre_cond of zero_op_inter_base_left
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) = () 

let zero_op_inter_base_left_pre (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    merge_pre (do l ol) (do a ol) (do b ol) /\ merge_pre l a b /\
                    merge_pre l (do a ob) (do b ol) /\ merge_pre (do l ol) (do (do a ob) ol) (do b ol) /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) = admit()

let zero_op_inter_base_left' (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol) /\ //pre_cond of zero_op_inter_base_right
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do b ol) ) (do (do c ob) ol)) = () 

let zero_op_inter_right_pre  (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    merge_pre (do l ol) (do a ol) (do (do b ob) ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol)) = ()
          
let zero_op_inter_right' (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ get_rid ob <> get_rid ol /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do b o) ol)) (do (do c o) ol) /\ //replacing ob with o
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol)) = ()

let zero_op_inter_left_pre (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ 
                    merge_pre (do l ol) (do (do a ob) ol) (do b ol) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol)) = ()
          
let zero_op_inter_left' (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a o) ol) (do b ol)) (do (do c o) ol) /\ //replacing ob with o
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol)) = ()

let zero_op_inter_lca_v1'' (l a b c:concrete_st) (ol:op_t)
  : Lemma (requires (exists o'. Fst_then_snd? (rc o' ol)) /\ eq (merge l a b) c /\ 
                    merge_pre l a b /\ merge_pre (do l ol) (do a ol) (do b ol))
          (ensures eq (merge (do l ol) (do a ol) (do b ol)) (do c ol)) = admit()

let zero_op_inter_lca_v2_pre (l a b c:concrete_st) (ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\
                    merge_pre (do l oi) (do a oi) (do b oi) /\ merge_pre (do l ol) (do a ol) (do b ol) /\
                    merge_pre (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol) /\ 
                    eq (merge (do l oi) (do a oi) (do b oi)) (do c oi)  /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol)) = admit()

let zero_op_inter_lca_v2' (l a b c:concrete_st) (ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\
                    eq (merge l a b) c /\ //EXTRA!!
                    eq (merge (do l oi) (do a oi) (do b oi)) (do c oi)  /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol)) = ()

(* 2 op Comm  *)
///////////////////

let comm_ind_right_pre  (l a b c:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    merge_pre l (do a o1) (do b o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    ~ (Fst_then_snd? (rc o1 o2')))      
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()
          
let comm_ind_right' (l a b c:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2) /\ //one_op_ind_right
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) )
                    //~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()

let comm_ind_left_pre (l a b c:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    merge_pre l (do a o1) (do b o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o1' o2) ==> (eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2))) /\
                    ~ (Fst_then_snd? (rc o2 o1')))                
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (do (merge l (do a o1') b) o2) o1)) = ()
          
let comm_ind_left' (l a b c:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o1' o2) ==> (eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2))) /\
                    eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1) /\ //one_op_ind_right
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o1')) )
                    //~ (exists o3 b'. eq (do (do b o1') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (do (merge l (do a o1') b) o2) o1)) = ()

let comm_ind_lca' (l:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base' (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2))
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_inter_base_right' (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (do (merge l a (do b ob)) o1) o2) /\ 
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_base_left' (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do (do a ob) o1) (do b o2)) (do (do (merge l (do a ob) b) o1) o2) /\ 
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) 
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_right_pre (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o1 <> get_rid o2 /\
                    merge_pre (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2) /\
                    merge_pre (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = admit()
          
let comm_inter_right' (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\

                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b o) ob) ol)) (do (do (do (do c o) ob) ol) o1) /\ //one_op_inter_left
                    eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2) /\ //one_op_inter_right
                    
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let comm_inter_left_pre (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o1 <> get_rid o2 /\
                    merge_pre (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2) /\
                    merge_pre (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = admit()
          
let comm_inter_left' (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\

                    eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o1) /\ //one_op_inter_left
                    eq (merge (do l ol) (do (do (do (do a o) ob) ol) o2) (do b ol)) (do (do (do (do c o) ob) ol) o2) /\ //one_op_inter_right
                    
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let comm_inter_lca_pre (l a b c:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    merge_pre l (do a o1) (do b o2) /\ merge_pre (do l ol) (do (do a ol) o1) (do (do b ol) o2) /\
                    (exists o'. Fst_then_snd? (rc o' ol)) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) = admit()
          
let comm_inter_lca' (l a b c:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    (exists o'. Fst_then_snd? (rc o' ol)) /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\ //zero_op_inter_lca_v1
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) = ()

