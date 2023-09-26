module App

#set-options "--query_stats"
// the concrete state type
// It is a pair of counter and flag
type concrete_st = int * bool

// init state
let init_st = 0, false

// equivalence between 2 concrete states
let eq (a b:concrete_st) = a == b

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
// (the only operation is Write value, so nat is fine)
type app_op_t:eqtype =
  |Enable
  |Disable

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
 match snd op with
  |Enable -> (fst s + 1, true)
  |Disable -> (fst s, false)

let lem_do (a b:concrete_st) (op:op_t)
  : Lemma (requires eq a b)
          (ensures eq (do a op) (do b op)) = ()
           
//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if snd x = Enable && snd y = Disable then First_then_second else Second_then_first

let merge_flag l a b =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac - lc > 0
          else bc - lc > 0

// concrete merge operation
let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  (fst s1 + fst s2 - fst lca, merge_flag lca s1 s2)

let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = ()

let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0)
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    consistent_branches l' s1' (do_st s2'' last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2)
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second_then_first? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))  = ()              

#push-options "--z3rlimit 50"
let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2)
       
          (ensures (let s2' = inverse_st s2 in
                   ((First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()
                       
let linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2)
                           
          (ensures (let s1' = inverse_st s1 in
                   ((ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1' (do_st s2 last2) /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   ((Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()
                       
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
let concrete_st_s = bool

// init state 
let init_st_s = false

// apply an operation to a state 
let do_s (st_s:concrete_st_s) (op:op_t) : concrete_st_s =
  if snd op = Enable then true else false

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  st_s == snd st

//initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()
          
////////////////////////////////////////////////////////////////


let merge_pre (lca s1 s2:concrete_st) =
  (fst s1 >= fst lca) /\
  (fst s2 >= fst lca) /\
  ((fst s1 = fst s2) ==> (fst s1 = fst lca))

(*#push-options "--z3rlimit 50"
let convergence1 (lca s1' s2:st) (o:op_t)
  : Lemma (requires //consistent_branches lca s1 s2 /\
                    //consistent_branches lca s1' s2 /\
                    (exists l1 l2 l3. apply_log (v_of lca) l1 == v_of s1' /\ apply_log (v_of lca) l2 == v_of s2 /\
                                 apply_log (v_of lca) l3 == (do (v_of s1') o)) /\
                    (exists l1 l2. apply_log (v_of s1') l1 == (do (v_of s1') o) /\
                              apply_log (v_of s1') l2 == (concrete_merge (v_of lca) (v_of s1') (v_of s2))) /\
                    merge_pre (v_of lca) (do (v_of s1') o) (v_of s2) /\
                    merge_pre (v_of lca) (v_of s1') (v_of s2) /\
                    merge_pre (v_of s1') (do (v_of s1') o) (concrete_merge (v_of lca) (v_of s1') (v_of s2)) /\
                    v_of lca = init_st /\ Disable? (snd o) /\
                    v_of s1' = (2, true) /\ v_of s2 = (1, false))
          (ensures eq (concrete_merge (v_of lca) (do (v_of s1') o) (v_of s2)) 
                      (concrete_merge (v_of s1') (do (v_of s1') o) (concrete_merge (v_of lca) (v_of s1') (v_of s2)))) = ()

let convergence2 (lca' lca s3 s1' s2:st)
  : Lemma (requires //consistent_branches lca s3 s1' /\
                    //consistent_branches lca' s1' s2 /\
                    (exists l1 l2. apply_log (v_of lca) l1 == v_of s3 /\ apply_log (v_of lca) l2 == v_of s1') /\
                    (exists l1 l2. apply_log (v_of lca') l1 == v_of s1' /\ apply_log (v_of lca') l2 == v_of s2) /\
                    (exists l1. apply_log (v_of lca') l1 == (concrete_merge (v_of lca) (v_of s3) (v_of s1'))) /\
                    (exists l1 l2. apply_log (v_of s1') l1 == (concrete_merge (v_of lca') (v_of s1') (v_of s2)) /\ 
                              apply_log (v_of s1') l2 == (concrete_merge (v_of lca) (v_of s3) (v_of s1'))))
          (ensures eq (concrete_merge (v_of lca') (concrete_merge (v_of lca) (v_of s3) (v_of s1')) (v_of s2)) 
                      (concrete_merge (v_of s1') 
                                       (concrete_merge (v_of lca) (v_of s3) (v_of s1'))
                                       (concrete_merge (v_of lca') (v_of s1') (v_of s2)))) = admit()*)
#pop-options

let concrete_merge1 (lca s1 s2:concrete_st) =
  (fst s1 + fst s2 - fst lca, merge_flag lca s1 s2)

////////////////////////////////////////////////////////////////
//// Linearization properties //////

let prop1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ resolve_conflict o1 o3 = First_then_second) //o3.o1
          (ensures eq (concrete_merge1 (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

let prop2 (s s':concrete_st) (o1 o2:op_t)
  : Lemma (requires eq (concrete_merge1 s (do s o2) s') (do s' o2))
          (ensures eq (concrete_merge1 (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = admit()

let prop3 (s s':concrete_st)
  : Lemma (requires eq (concrete_merge1 s s s') s' /\
                    (forall o2'. eq (concrete_merge1 s (do s o2') s') (do s' o2')))
          (ensures (forall o2 o2'. (fst o2 <> fst o2') ==> eq (concrete_merge1 s (do (do s o2') o2) s') (do (do s' o2') o2))) = ()

let prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t)
  : Lemma (requires fst o2 <> fst o3 /\ resolve_conflict o2 o3 = First_then_second /\ //o3.o2
                    eq (concrete_merge1 (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (concrete_merge1 (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                   (do (do (do (do s o3') o3) o1) o2)) = ()

let prop5 (s s':concrete_st)
  : Lemma (eq (concrete_merge1 s s s') s' /\ 
           eq (concrete_merge1 s s' s) s') = admit() //can be done with some pre-cond

let rec_merge (l a' b' a b m:concrete_st)
  : Lemma (requires eq (concrete_merge1 l a' b') m /\
                    eq (concrete_merge1 m a b) (concrete_merge1 a' a (concrete_merge1 l a' b)) /\
                    eq (concrete_merge1 m a b) (concrete_merge1 b' b (concrete_merge1 l a b')))
          (ensures eq (concrete_merge1 m a b) (concrete_merge1 (concrete_merge1 l a' b') a b)) = ()
          
////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////

type ew_state = s:(nat * nat)//{snd s <= fst s}

let ew_merge_pre (l a b:ew_state) = true// (fst a >= fst l) /\ (snd a >= snd l) /\ (fst b >= fst l) /\ (snd b >= snd l)
                                   // /\ ((fst a = fst b) ==> (fst a = fst l)) /\
                                   // ((snd a = snd b) ==> (snd a = snd l))

let ew_get (s:nat * nat) = if fst s > snd s then true else false

let ew_eq (a b:ew_state) = ew_get a == ew_get b

let min (a b:nat) = if a < b then a else b

let max (a b:nat) = if a < b then b else a

let ew_merge (l a:ew_state) (b:ew_state{ew_merge_pre l a b}) : ew_state =
  let mina = min (fst a) (snd a) in
  let a' = fst a - mina, snd a - mina in
  let minb = min (fst b) (snd b) in
  let b' = fst b - minb, snd b - minb in
  if fst a' + fst b' - fst l > 0 && snd a' + snd b' - snd l > 0 then fst a' + fst b' - fst l, snd a' + snd b' - snd l
  else if fst a' + fst b' - fst l > 0 then fst a' + fst b' - fst l, 0
  else if snd a' + snd b' - snd l > 0 then 0, snd a' + snd b' - snd l
  else 0,0
 
let ew_do (s:ew_state) (op:op_t) : ew_state =
  match snd op with
  |Enable -> fst s + 1, snd s
  |Disable -> fst s, fst s 

let ew_conv1 (lca s1' s2:ew_state) (o:op_t)
  : Lemma (requires ew_merge_pre lca (ew_do s1' o) s2 /\
                    ew_merge_pre lca s1' s2 /\
                    ew_merge_pre s1' (ew_do s1' o) (ew_merge lca s1' s2))
          (ensures ew_eq (ew_merge lca (ew_do s1' o) s2)
                         (ew_merge s1' (ew_do s1' o) (ew_merge lca s1' s2))) = ()

let ew_conv2 (lca' lca s3 s1' s2:ew_state)
  : Lemma (requires ew_merge_pre lca s3 s1' /\
                    ew_merge_pre lca' (ew_merge lca s3 s1') s2 /\
                    ew_merge_pre lca' s1' s2 /\
                    ew_merge_pre s1' (ew_merge lca s3 s1') (ew_merge lca' s1' s2))
          (ensures ew_eq (ew_merge lca' (ew_merge lca s3 s1') s2)
                         (ew_merge s1' (ew_merge lca s3 s1') (ew_merge lca' s1' s2))) = ()                                      

let ew_conv3 (l a b:ew_state) (op1 op2:op_t)
  : Lemma (requires snd op2 = Enable /\
                    ew_merge_pre l (ew_do a op1) (ew_do b op2) /\
                    ew_merge_pre l (ew_do a op1) b)
          (ensures ew_eq (ew_merge l (ew_do a op1) (ew_do b op2)) (ew_do (ew_merge l (ew_do a op1) b) op2)) = ()

let idem (s:ew_state)
  : Lemma (ew_merge s s s = s) = ()

//////////////////////////////////////////

module S = Set_extended_new

type ew_state = S.t pos

let disjoint (a b:ew_state) =
  (forall e. S.mem e a ==> not (S.mem e b))

let ew_merge_pre (l a b:ew_state) = 
  //disjoint l (S.difference a l) /\
  //disjoint l (S.difference b l) /\
  disjoint (S.difference a l) (S.difference b l)

let ew_eq (a b:ew_state) = S.equal a b

let ew_merge (l a:ew_state) (b:ew_state{ew_merge_pre l a b}) : ew_state =
  let da = S.difference a l in    //a - l
  let db = S.difference b l in    //b - l
  let i_ab = S.intersection a b in
  let i_lab = S.intersection l i_ab in            // intersect l a b
  S.union i_lab (S.union da db)
  //S.union l (S.union a b)

let ew_do_pre (s:ew_state) (op:op_t) =
  ~ (S.mem (fst op) s)

let ew_do (s:ew_state) (op:op_t{ew_do_pre s op}) : ew_state =
  match snd op with
  |Enable -> S.insert (fst op) s
  |Disable -> S.empty

let ew_conv1 (lca s1' s2:ew_state) (o:op_t)
  : Lemma (requires ew_do_pre s1' o /\
                    ew_do_pre lca o /\ //extra
                    ew_merge_pre lca (ew_do s1' o) s2 /\
                    ew_merge_pre lca s1' s2 /\
                    ew_merge_pre s1' (ew_do s1' o) (ew_merge lca s1' s2))
          (ensures ew_eq (ew_merge lca (ew_do s1' o) s2)
                         (ew_merge s1' (ew_do s1' o) (ew_merge lca s1' s2))) = ()

let ew_conv2 (lca' lca s3 s1' s2:ew_state)
  : Lemma (requires ew_merge_pre lca s3 s1' /\
                    ew_merge_pre lca' (ew_merge lca s3 s1') s2 /\
                    ew_merge_pre lca' s1' s2 /\
                    ew_merge_pre s1' (ew_merge lca s3 s1') (ew_merge lca' s1' s2) /\                 
                    (forall e. S.mem e (S.intersection lca' s3) ==> S.mem e lca) /\ //extra
                    (forall e. S.mem e (S.intersection lca' s1') ==> S.mem e lca)) //extra
          (ensures ew_eq (ew_merge lca' (ew_merge lca s3 s1') s2)
                         (ew_merge s1' (ew_merge lca s3 s1') (ew_merge lca' s1' s2))) = ()                                      

let ew_conv3 (l a b:ew_state) (op1 op2:op_t)
  : Lemma (requires snd op2 = Enable /\
                    ew_do_pre a op1 /\ ew_do_pre b op2 /\
                    ew_do_pre l op2 /\ //extra
                    ew_merge_pre l (ew_do a op1) b /\
                    ew_do_pre (ew_merge l (ew_do a op1) b) op2 /\
                    ew_merge_pre l (ew_do a op1) (ew_do b op2))
          (ensures ew_eq (ew_merge l (ew_do a op1) (ew_do b op2)) (ew_do (ew_merge l (ew_do a op1) b) op2)) = ()

let idem (s:ew_state)
  : Lemma //(requires ew_merge_pre s s s)
          (ensures ew_eq (ew_merge s s s) s) = ()

//////////////////////////

(*module L = FStar.List.Tot

let rec unique (l:list pos) =
  match l with
  |[] -> true
  |x::xs -> not (L.mem x xs) && unique xs

type ew_state = l:list pos{unique l}

let rec diff (a b:ew_state) : (r:ew_state{forall e. L.mem e r <==> L.mem e a /\ not (L.mem e b)}) =
  match a with
  |[] -> []
  |x::xs -> if L.mem x b then diff xs b else x::diff xs b

let rec intersect (l a b:ew_state) : (r:ew_state{forall e. L.mem e r <==> L.mem e l /\ L.mem e a /\ L.mem e b}) =
  match l,a,b with
  |[],_,_ |_,[],_ |_,_,[] -> []
  |x::xs,y::ys,z::zs -> if L.mem x a && L.mem x b then x::intersect xs a b else intersect xs a b

let ew_merge_pre (l a b:ew_state) = 
  (forall e. L.mem e l ==> not (L.mem e (diff a l)) /\ not (L.mem e (diff b l))) /\
  (forall e. L.mem e (diff a l) ==> not (L.mem e (diff b l)))
  
let rec app (l a:ew_state) (b:ew_state{(forall e. L.mem e l ==> not (L.mem e a) /\ not (L.mem e b)) /\
                                       (forall e. L.mem e a ==> not (L.mem e b))})  
  : (r:ew_state{forall e. L.mem e r <==> L.mem e l \/ L.mem e a \/ L.mem e b}) =
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> x::app xs a b
  |[],y::ys,_ -> y::app l ys b
  |[],[],z::zs -> z::app l a zs

let ew_eq (a b:ew_state) = (forall e. L.mem e a <==> L.mem e b)

let ew_merge (l a:ew_state) (b:ew_state{ew_merge_pre l a b}) 
  : (r:ew_state{(forall e. L.mem e r <==> (L.mem e a /\ not (L.mem e l)) \/
                                   (L.mem e b /\ not (L.mem e l)) \/
                                   (L.mem e l /\ L.mem e a /\ L.mem e b))}) =
  let da = diff a l in    //a - l
  let db = diff b l in    //b - l
  let i = intersect l a b in           // intersect l a b
  app i da db

let ew_do_pre (s:ew_state) (op:op_t) =
  ~ (L.mem (fst op) s)

let ew_do (s:ew_state) (op:op_t{ew_do_pre s op}) 
  : (r:ew_state{(snd op = Enable ==> (forall e. L.mem e r <==> L.mem e s \/ e = fst op)) /\
                (snd op = Disable ==> r = [])}) =
  match snd op with
  |Enable -> (fst op)::s
  |Disable -> []

//#push-options "--z3rlimit 50"
let ew_conv1 (lca s1' s2:ew_state) (o:op_t)
  : Lemma (requires ew_do_pre s1' o /\ 
                    ew_do_pre lca o /\ //extra
                    ew_merge_pre lca (ew_do s1' o) s2 /\
                    ew_merge_pre lca s1' s2 /\
                    ew_merge_pre s1' (ew_do s1' o) (ew_merge lca s1' s2))
          (ensures ew_eq (ew_merge lca (ew_do s1' o) s2)
                         (ew_merge s1' (ew_do s1' o) (ew_merge lca s1' s2))) = ()

let ew_conv2 (lca' lca s3 s1' s2:ew_state)
  : Lemma (requires ew_merge_pre lca s3 s1' /\
                    ew_merge_pre lca' (ew_merge lca s3 s1') s2 /\
                    ew_merge_pre lca' s1' s2 /\
                    ew_merge_pre s1' (ew_merge lca s3 s1') (ew_merge lca' s1' s2) /\
                    (forall e. L.mem e lca' /\ L.mem e s3 ==> L.mem e lca) /\ //extra
                    (forall e. L.mem e lca' /\ L.mem e s1' ==> L.mem e lca)) //extra
          (ensures ew_eq (ew_merge lca' (ew_merge lca s3 s1') s2)
                         (ew_merge s1' (ew_merge lca s3 s1') (ew_merge lca' s1' s2))) = ()                                    

let ew_conv3 (l a b:ew_state) (op1 op2:op_t)
  : Lemma (requires snd op2 = Enable /\
                    ew_do_pre a op1 /\ ew_do_pre b op2 /\ 
                    ew_do_pre l op2 /\ //extra
                    ew_merge_pre l (ew_do a op1) b /\
                    ew_do_pre (ew_merge l (ew_do a op1) b) op2 /\
                    ew_merge_pre l (ew_do a op1) (ew_do b op2))
          (ensures ew_eq (ew_merge l (ew_do a op1) (ew_do b op2)) (ew_do (ew_merge l (ew_do a op1) b) op2)) = ()

let idem (s:ew_state)
  : Lemma //(requires ew_merge_pre s s s)
          (ensures ew_eq (ew_merge s s s) s) = ()*)
