module App

#set-options "--query_stats"
module M = Map_extended
module S = Set_extended

type cf = ((int & int) & bool)

let cond (s:M.t nat cf) =
  //forall rid. M.contains s rid ==> (snd (M.sel s rid) = false <==> (fst (fst (M.sel s rid)) = snd (fst (M.sel s rid))))
  forall rid. M.contains s rid ==> fst (fst (M.sel s rid)) >= snd (fst (M.sel s rid))
  //forall rid. M.contains s rid ==> fst (fst (M.sel s rid)) >= snd (fst (M.sel s rid)) //(snd (M.sel s rid) = false ==> fst (fst (M.sel s rid)) = snd (fst (M.sel s rid))) 
                              //(snd (M.sel s rid) = true ==> fst (fst (M.sel s rid)) > snd (fst (M.sel s rid)))

// the concrete state type
type concrete_st = (*s:(option pos & int){(None? (fst s) ==> snd s = 0) /\ (snd s <> 0 ==> Some? (fst s))}*)
                 s:M.t nat cf{cond s}

// init state
let init_st = (*None,0*) M.const_on S.empty ((0,0),false)

let sel (s:concrete_st) k = if M.contains s k then M.sel s k else ((0,0), false)

// equivalence between 2 concrete states
let eq (a b:concrete_st) = //a == b //snd a == snd b
  (forall id. M.contains a id = M.contains b id /\ sel a id == sel b id)
  //fst (fst (sel a id)) - snd (fst (sel a id)) = fst (fst (sel b id)) - snd (fst (sel b id)) /\
    //     snd (sel a id) = snd (sel b id))
  ///\ sel a id == sel b id)

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
  |(ts, (rid, Set)) -> //if None? (fst s) then (Some ts, snd s + 1) 
                      //else (let Some ts1,x = s in let t = if ts > ts1 then ts else ts1 in (Some t, snd s +1) )
  
                      let r = let v = sel s rid in M.upd s rid ((fst (fst v) + 1, snd (fst v)), true) in r
  |(_, (rid, Reset)) -> (*None, 0*) M.map_val (fun ((p,n),f) -> ((p,p),false)) s

//conflict resolution
let rc (o1 o2:op_t) = 
  match snd (snd o1), snd (snd o2) with
  |Set, Set -> Either //if fst o1 > fst o2 then Snd_then_fst else Fst_then_snd
  |Set, Reset -> Snd_then_fst
  |Reset, Set -> Fst_then_snd
  |_ -> Either

let max a b = if a > b then a else b

let merge_flag (l a b:cf) : bool =
  let lc = fst (fst l) in
  let ac = fst (fst a) in
  let bc = fst (fst b) in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac > lc
          else bc > lc

let min a b = if a > b then b else a

let merge_snd (l a b:int & int) : int =
  let ls,lr = l in
  let as',ar = a in
  let bs,br = b in
  let m = min (min (ar - lr) (br - lr)) (ls - lr) in
  let m' = lr + m in
  //lr + m + ar - m' + br - m'
  ar + br - lr - m
  
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
  ((fst (fst a) + fst (fst b) - fst (fst l), merge_snd (fst l) (fst a) (fst b)), merge_flag l a b)

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys ((0,0), false) in
  let r = M.iter_upd (fun k v -> merge_cf (sel l k) (sel a k) (sel b k)) u in
  assume (cond r);  
  r

(*let merge l a b =
  match l,a,b with
  |_, (None,_), (None,_) -> (None,0)
  |(None,_), (None,_), _-> b
  |(None,_), _, (None,_) -> a
  |(None,_), (Some ts1,x), (Some ts2,y) -> (*if ts1 = ts2 then (Some ts1,x+y) else*) (Some (max ts1 ts2), x+y)
  |(Some ts,z), (Some ts1,x), (Some ts2,y) -> if l = a then b else if l = b then a 
                                             else if ts = ts1 && ts = ts2 then (Some ts, x+y-z)
                                             else if ts = ts1 then (Some (max (max ts1 ts2) ts), x+y-z)
                                             else if ts = ts2 then (Some (max (max ts1 ts2) ts), x+y-z)
                                             else (Some (max (max ts1 ts2) ts), x+y)
  |(Some ts,z), (Some ts1,x), (None,_) -> if l = a then b else (Some (max ts1 ts), x-z)
  |(Some ts,z), (None,_), (Some ts2,y) -> if l = b then a else (Some (max ts2 ts), y-z)
  //|_ -> admit()*)
  

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
   : Lemma (ensures eq (merge s s s) s) = 
   let lhs = merge s s s in
   (*assert (None? (fst s) ==> fst (merge s s s) = None);
   assert (None? (fst s) ==> snd (merge s s s) = 0);
   assert (None? (fst s) ==> snd s = 0);
   assert (Some? (fst s) ==> fst (merge s s s) = fst s);
   assert (Some? (fst s) ==> snd (merge s s s) = snd s);*)
   //assert (forall rid. M.contains lhs rid = M.contains s rid);
   //assert (forall rid. snd (sel lhs rid) = snd (sel s rid));
   //assert (forall rid. fst (fst (sel lhs rid)) = fst (fst (sel s rid)));
   //assert (forall rid. snd (fst (sel lhs rid)) = snd (fst (sel s rid)));
   ()

//let get (s:concrete_st{Some? (fst s)}) =
  //let Some ts,_ = s in ts


(*Two OP RC*)
//////////////// 
#set-options "--z3rlimit 500 --ifuel 5"

let lem_st s : prop = (forall id. snd (sel s id) = false <==> fst (fst (sel s id)) = snd (fst (sel s id)))

let merge_pre (l a b:concrete_st) : prop =
  (forall id. M.contains l id ==> M.contains a id /\ M.contains b id) /\
  (forall id. M.contains l id ==> fst (fst (sel l id)) <= fst (fst (sel a id)) /\ fst (fst (sel l id)) <= fst (fst (sel b id)) /\
                             snd (fst (sel l id)) <= snd (fst (sel a id)) /\ snd (fst (sel l id)) <= snd (fst (sel b id))) /\
  (forall id. M.contains a id /\ M.contains b id ==> M.contains l id)

// a== init not working
let rc_ind_right (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ (*get_rid o2' = get_rid o2 /\ Set? (snd (snd o2')) /\
                    //distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\*)
                    //lem_st l /\ lem_st a /\ lem_st b /\
                    //merge_pre l (do a o1) (do b o2) /\ merge_pre l (do a o1) b /\
                    //merge_pre l (do a o1) (do (do b o2') o2) /\ merge_pre l (do a o1) (do b o2') /\

                    //l == M.upd init_st 1 ((2,1), true) /\ 
                    //a == M.upd init_st 1 ((2,2), false) /\ 
                   // b == M.upd init_st 1 ((2,1), true) /\ Reset? (snd (snd o2')) /\
                    //get_rid o2 = 1 /\
                    //l == M.upd init_st 1 ((1,0), true) /\
                    //(do a o1) == M.upd init_st 1 ((1,1), false) /\
                    //(do (do b o2') o2) == M.upd init_st 1 ((3,2), true) /\ 
                    
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) = 
  //assert (fst (merge l (do a o1) (do (do b o2') o2)) = fst (do (merge l (do a o1) (do b o2')) o2));
   ()

let rc_ind_left (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    //lem_st l /\ lem_st a /\ lem_st b /\
                    //merge_pre l (do a o1) (do b o2) /\ merge_pre l (do a o1) b /\
                    //merge_pre l (do (do a o1') o1) (do b o2) /\ merge_pre l (do (do a o1') o1) b /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) = ()

//Special case of rc_intermediate_v1 //set o is problem
let rc_ind_lca (l:concrete_st) (o1 o2 o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ //Set? (snd (snd o)) /\
                    //l == M.upd init_st 1 ((1,0), true) /\ 
                    //get_rid o = get_rid o2 /\
                    //lem_st l /\
                    //merge_pre l (do l o1) (do l o2) /\ merge_pre (do l o) (do (do l o) o1) (do (do l o) o2) /\
                    
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) = ()

let rc_base (o1 o2:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let rc_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\
                    //distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let rc_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    //distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()
          
let rc_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    //distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    //distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

//passes with EXTRA!!
let rc_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    //distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    //distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    //eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = admit()

//passes with EXTRA!!
// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let rc_inter_lca (l a b c:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ Fst_then_snd? (rc o1 o2) /\ 
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    //eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2) /\ //EXTRA!!
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) = admit()

(*One op*)
///////////////
//passes with pre-cond
let one_op_ind_right (l a b c:concrete_st) (o2 o2':op_t)
   : Lemma (requires (*lem_st l /\ lem_st a /\ lem_st b /\ lem_st c /\
                     merge_pre l a (do b o2) /\ merge_pre l a b /\
                     merge_pre l a (do (do b o2') o2) /\
                     merge_pre l a (do b o2') /\*) 
                     eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2)) = admit()

//passes with pre-cond
let one_op_ind_left (l a b c:concrete_st) (o1 o1':op_t)
   : Lemma (requires (*lem_st l /\ lem_st a /\ lem_st b /\ lem_st c /\
                     merge_pre l (do a o1) b /\ merge_pre l a b /\
                     merge_pre l (do (do a o1') o1) b /\
                     merge_pre l (do a o1') b /\*)
                     eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) = admit()

let one_op_ind_lca (l:concrete_st) (o2 o:op_t) //set o is a problem
  : Lemma (requires eq (merge l l (do l o2)) (do l o2))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o2)) (do (do l o) o2)) = 
  //assert (None? (fst (do (do l o) o2)));
  //assert (None? (fst (merge (do l o) (do l o) (do (do l o) o2))));
  ()

let one_op_base (o2:op_t)
  : Lemma (ensures eq (merge init_st init_st (do init_st o2)) (do init_st o2)) = ()

//passes with EXTRA!!
let one_op_inter_base_right (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    //distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    (*lem_st l /\ lem_st a /\ lem_st b /\ lem_st c /\
                    merge_pre (do l ol) (do a ol) (do (do b ol) o2) /\
                    merge_pre l a (do b o2) /\ merge_pre l (do a ol) (do b ob) /\
                    merge_pre (do l ol) (do a ol) (do (do (do b ob) ol) o2) /\*)
                    //merge_pre l a b /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    //eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol) /\ //EXTRA!!
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) = admit()

//passes with EXTRA!!
let one_op_inter_base_left (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //***EXTRA***
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ //EXTRA!! 
                    //eq (merge (do l ol) (do (do a ob) ol) (do b ol) ) (do (do c ob) ol) /\ //EXTRA!!
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) = admit()

//passes with EXTRA!!
let one_op_inter_right (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    //eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol) /\ //EXTRA!!
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) = admit()

//passes with EXTRA!!
let one_op_inter_left (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    //eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) = admit()

//passes with EXTRA!!
// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let one_op_inter_lca (l a b c:concrete_st) (o2 ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    //eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol) /\ //EXTRA!!
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) = admit()

(*Zero op *)
///////////////
// because we proved that e_i^l rcp eb is not possible.
//e_i^l vis eb is not possible
// so either eb rcp e_i^l or eb rct e_i^l is possible
//passes with EXTRA!!
let zero_op_inter_base_right (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ //distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    //eq (merge l (do a ob) (do b ol)) (do (do c ob) ol) /\ //EXTRA!!
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) = admit() 

//passes with EXTRA!!
let zero_op_inter_base_left (l a b c:concrete_st) (ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\
                    eq (merge l a b) c /\
                    //eq (merge l (do a ol) (do b ob)) (do (do c ob) ol) /\ //EXTRA!!
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do b ol) ) (do (do c ob) ol)) = admit() 

//passes with EXTRA!!
let zero_op_inter_right (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    //eq (merge (do l ol) (do a ol) (do (do b o) ol)) (do (do c o) ol) /\ //EXTRA!!
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol)) = admit()

//passes with EXTRA!!
let zero_op_inter_left (l a b c:concrete_st) (ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ distinct_ops ob ol /\ 
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    //eq (merge (do l ol) (do (do a o) ol) (do b ol)) (do (do c o) ol) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol)) = admit()

// In general, the event "o" below should be such that these exists o', (rc o' o)
let zero_op_inter_lca_v1 (l a b c:concrete_st) (ol:op_t)
  : Lemma (requires //lem_st l /\ lem_st a /\ lem_st b /\ lem_st c /\
                    //merge_pre l a b /\ merge_pre (do l ol) (do a ol) (do b ol) /\
                    (exists o'. Fst_then_snd? (rc o' ol)) /\ eq (merge l a b) c)
          (ensures eq (merge (do l ol) (do a ol) (do b ol)) (do c ol)) = admit()

//passes with EXTRA!!
// In general, the events o',o_n, below should be such that these exists o, (rc o o')
let zero_op_inter_lca_v2 (l a b c:concrete_st) (ol oi:op_t)
  : Lemma (requires (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\
                    //eq (merge l a b) c /\ //EXTRA!!
                    eq (merge (do l oi) (do a oi) (do b oi)) (do c oi)  /\
                    eq (merge (do l ol) (do a ol) (do b ol)) (do c ol))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do b oi) ol)) (do (do c oi) ol)) = admit()

(* 2 op Comm  *)
///////////////////

let comm_ind_right (l a b c:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    //distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) )
                    //~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) = ()

let comm_ind_left (l a b c:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    //distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o1' o2) ==> (eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o1')) )
                    //~ (exists o3 b'. eq (do (do b o1') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (do (merge l (do a o1') b) o2) o1)) = ()

let comm_ind_lca (l:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    //distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge init_st (do init_st o1) (do init_st o2)) (do (do init_st o1) o2)) = ()

let comm_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                   // distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (do (merge l a (do b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    //distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do (do a ob) o1) (do b o2)) (do (do (merge l (do a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

//passes with EXTRA!!
let comm_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    //distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    //distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    //eq (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) (do (do (do c o) ob) ol) /\ //EXTRA!!
                    //eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = admit()

//passes with EXTRA!!
let comm_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    //distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    //distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    //eq (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) (do (do (do c o) ob) ol) /\ //EXTRA!!
                    //eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do b ol)) (do (do (do (do c o) ob) ol) o1) /\ //EXTRA!!
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = admit()

let comm_inter_lca (l a b c:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ //get_rid o1 <> get_rid o2 /\
                    //distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    (exists o'. Fst_then_snd? (rc o' ol)) /\
                    //eq (merge (do l ol) (do a ol) (do b ol)) (do c ol) /\ //EXTRA!!
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) = admit()

////////////////////////////////////////////////////////////////
////Equivalence of  MRDT & Sequential implementation  //////

// the concrete state 
let concrete_st_s = int

// init state 
let init_st_s = 0

// apply an operation to a state 
let do_s (st_s:concrete_st_s) (_:op_t) = st_s + 1

// equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  st_s = st

// initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()
         
////////////////////////////////////////////////////////////////
