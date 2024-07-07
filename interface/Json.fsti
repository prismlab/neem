module Json

module M = Dependent_map
open FStar.Seq
module S = Set_extended

type kt : eqtype =
  |Alpha_t : string -> kt
  |Beta_t : string -> kt

//concrete state of alpha type
val concrete_st_a : Type0

//concrete state of beta type
val concrete_st_b : Type0

let vt (c:kt) : Type0 =
  match c with
  |Alpha_t _ -> concrete_st_a
  |Beta_t _ -> concrete_st_b

//concrete state
type concrete_st = M.t kt vt

//init state of alpha type
val init_st_a : concrete_st_a 

//init state of beta type
val init_st_b : concrete_st_b

let init_st_v (k:kt) : vt k =
  match k with
  |Alpha_t _ -> init_st_a
  |Beta_t _ -> init_st_b

let init_st (k:kt) : concrete_st = M.const_on S.empty (fun k -> init_st_v k)

//Querying the map for its value at a given key
let sel (s:concrete_st) (k:kt) =
  match k with
  |Alpha_t _ -> if M.contains s k then M.sel s k else init_st_a
  |Beta_t _ -> if M.contains s k then M.sel s k else init_st_b

val eq_a (a b:concrete_st_a) : Type0
val eq_b (a b:concrete_st_b) : Type0

let eq (a b:concrete_st) =
  //M.equal a b
  //(forall k. M.contains a k = M.contains b k /\ sel a k == sel b k)
  (forall k. M.contains a (Alpha_t k) = M.contains b (Alpha_t k) /\ 
        M.contains a (Beta_t k) = M.contains b (Beta_t k) /\
        eq_a (sel a (Alpha_t k)) (sel b (Alpha_t k)) /\
        eq_b (sel a (Beta_t k)) (sel b (Beta_t k)))

val lem_eq_a (a b:concrete_st_a) 
  : Lemma (ensures eq_a a b <==> a == b)
          [SMTPat (eq_a a b)]

val lem_eq_b (a b:concrete_st_b) 
  : Lemma (ensures eq_b a b <==> a == b)
          [SMTPat (eq_b a b)]
          
let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = () 

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b) = () 

//alpha MRDT operation type
val app_op_a : eqtype

//beta MRDT operation type
val app_op_b : eqtype

type app_op_v : eqtype =
  |Alpha_op : app_op_a -> app_op_v
  |Beta_op : app_op_b -> app_op_v

type app_op_t:eqtype =
  |Set : string (* key *) -> app_op_v (* value op *) -> app_op_t

type op_t = pos (*timestamp*) & (nat (*replica ID*) & app_op_t)
type op_v = pos (*timestamp*) & (nat (*replica ID*) & app_op_v)
type op_a = pos (*timestamp*) & (nat (*replica ID*) & app_op_a)
type op_b = pos (*timestamp*) & (nat (*replica ID*) & app_op_b)

let get_rid (_,(rid,_)) = rid

let distinct_ops (ts1,_) (ts2,_) = ts1 =!= ts2

let is_alpha_op (o:op_t) =
  match snd (snd o) with
  |Set _ (Alpha_op _) -> true
  |_ -> false

let is_beta_op (o:op_t) = 
  match snd (snd o) with
  |Set _ (Beta_op _) -> true
  |_ -> false

let get_op_a (o:op_t{is_alpha_op o}) : op_a =
  match o with
  |ts, (rid, Set _ (Alpha_op op)) -> (ts,(rid,op))

let get_op_b (o:op_t{is_beta_op o}) : op_b =
  match o with
  |ts, (rid, Set _ (Beta_op op)) -> (ts,(rid,op))
  
//do function of alpha type
val do_a (s:concrete_st_a) (o:op_a) : concrete_st_a

//do function of beta type
val do_b (s:concrete_st_b) (o:op_b) : concrete_st_b

let get_key (_,(_,Set k _)) = k

//do function of map
let do (s:concrete_st) (o:op_t) 
  : (r:concrete_st{(is_alpha_op o ==> (forall k. M.contains r k <==> M.contains s k \/ k = Alpha_t (get_key o))) /\
                   (is_beta_op o ==> (forall k. M.contains r k <==> M.contains s k \/ k = Beta_t (get_key o)))}) =
  match snd (snd o) with
  |Set k (Alpha_op _) -> let v = sel s (Alpha_t k) in M.upd s (Alpha_t k) (do_a v (get_op_a o))
  |Set k (Beta_op _) -> let v = sel s (Beta_t k) in M.upd s (Beta_t k) (do_b v (get_op_b o))

type rc_res =
  |Fst_then_snd //o1 -> o2
  |Snd_then_fst //o2 -> o1
  |Either

val rc_a (o1 o2:op_a) : rc_res

val rc_b (o1 o2:op_b) : rc_res

//conflict resolution
let rc (o1 o2:op_t) : rc_res = 
  match snd (snd o1), snd (snd o2) with
  |Set k1 (Alpha_op _), Set k2 (Alpha_op _) -> if k1 = k2 then rc_a (get_op_a o1) (get_op_a o2) else Either
  |Set k1 (Beta_op _), Set k2 (Beta_op _) -> if k1 = k2 then rc_b (get_op_b o1) (get_op_b o2) else Either
  |_ -> Either

val merge_a (l a b:concrete_st_a) : concrete_st_a 

val merge_b (l a b:concrete_st_b) : concrete_st_b

let compose_values (k:kt) (l a b:concrete_st) : vt k =
  if Alpha_t? k then 
    merge_a (sel l k) (sel a k) (sel b k)
  else merge_b (sel l k) (sel a k) (sel b k)

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (fun k -> init_st k) in
  M.map (fun k _ -> compose_values k l a b) u

let commutes_with_a (o1 o2:op_a) =
  forall s. eq_a (do_a (do_a s o1) o2) (do_a (do_a s o2) o1)

let commutes_with_b (o1 o2:op_b) =
  forall s. eq_b (do_b (do_b s o1) o2) (do_b (do_b s o2) o1)
  
let commutes_with (o1 o2:op_t) =
  forall s. eq (do (do s o1) o2) (do (do s o2) o1)

type log = seq op_t

// applying a log of operations to a concrete state
let rec apply_log (x:concrete_st) (l:log) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |_ -> apply_log (do x (head l)) (tail l)  

/////////////////////////////////////////////////////////////////////////////

val rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2)

val no_rc_chain (o1 o2 o3:op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc o2 o3)))

val cond_comm_base (s:concrete_st) (o1 o2 o3:op_t) 
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ distinct_ops o1 o3 /\
                    Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do (do s o2) o1) o3))

val cond_comm_ind (s:concrete_st) (o1 o2 o3 o:op_t) (l:seq op_t)
  : Lemma (requires distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3 /\ 
                    Fst_then_snd? (rc o1 o2) /\ ~ (Either? (rc o2 o3)) /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do (apply_log (do (do s o2) o1) l) o) o3))
                  
////////////////////////////////////////////////////////////////////////////

//merge is commutative
val merge_comm_a (l a b: concrete_st_a) 
  : Lemma (ensures eq_a (merge_a l a b) (merge_a l b a))
          [SMTPat (merge_a l a b)]

val merge_comm_b (l a b: concrete_st_b) 
  : Lemma (ensures eq_b (merge_b l a b) (merge_b l b a))
          [SMTPat (merge_b l a b)]
          
let merge_comm (l a b:concrete_st)
  : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

//merge is idempotent
val merge_idem_a (s: concrete_st_a) 
  : Lemma (ensures eq_a (merge_a s s s) s)
          [SMTPat (merge_a s s s)]

val merge_idem_b (s: concrete_st_b) 
  : Lemma (ensures eq_b (merge_b s s s) s)
          [SMTPat (merge_b s s s)]

let merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s) = ()

//////////////////////////////////////////////////////////////////////////

(*Zero OP*)
//////////////// 
val lem_0op_a (l a b:concrete_st_a) (ol:op_a)
  : Lemma (ensures eq_a (merge_a (do_a l ol) (do_a a ol) (do_a b ol)) (do_a (merge_a l a b) ol))

val lem_0op_b (l a b:concrete_st_b) (ol:op_b)
  : Lemma (ensures eq_b (merge_b (do_b l ol) (do_b a ol) (do_b b ol)) (do_b (merge_b l a b) ol))

let lem_0op (l a b:concrete_st) (ol:op_t)
  : Lemma (ensures eq (merge (do l ol) (do a ol) (do b ol)) (do (merge l a b) ol)) =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if is_alpha_op ol then lem_0op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a ol)
  else if is_beta_op ol then lem_0op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b ol)
  else ()

(*One OP*)
//////////////// 
val base_1op_a (o1:op_a) 
  : Lemma (ensures eq_a (merge_a init_st_a (do_a init_st_a o1) init_st_a) (do_a (merge_a init_st_a init_st_a init_st_a) o1))

val base_1op_b (o1:op_b) 
  : Lemma (ensures eq_b (merge_b init_st_b (do_b init_st_b o1) init_st_b) (do_b (merge_b init_st_b init_st_b init_st_b) o1))

let base_1op (o1:op_t) (t:kt)
  : Lemma (ensures eq (merge (init_st t) (do (init_st t) o1) (init_st t)) (do (merge (init_st t) (init_st t) (init_st t)) o1)) =
  if is_alpha_op o1 then base_1op_a (get_op_a o1)
  else if is_beta_op o1 then base_1op_b (get_op_b o1)
  else ()

val ind_lca_1op_a (l:concrete_st_a) (o1 ol:op_a)
  : Lemma (requires distinct_ops o1 ol /\
                    eq_a (merge_a l (do_a l o1) l) (do_a (merge_a l l l) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a l ol) o1) (do_a l ol)) (do_a (merge_a (do_a l ol) (do_a l ol) (do_a l ol)) o1))

val ind_lca_1op_b (l:concrete_st_b) (o1 ol:op_b)
  : Lemma (requires distinct_ops o1 ol /\ 
                    eq_b (merge_b l (do_b l o1) l) (do_b (merge_b l l l) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b l ol) o1) (do_b l ol)) (do_b (merge_b (do_b l ol) (do_b l ol) (do_b l ol)) o1))

let ind_lca_1op (l:concrete_st) (o1 ol:op_t)
  : Lemma (requires distinct_ops o1 ol /\
                    eq (merge l (do l o1) l) (do (merge l l l) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do l ol)) (do (merge (do l ol) (do l ol) (do l ol)) o1)) =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && is_alpha_op o1 && is_alpha_op ol then
      ind_lca_1op_a (sel l ka) (get_op_a o1) (get_op_a ol)
  else if get_key o1 = k && is_beta_op o1 && is_beta_op ol then
      ind_lca_1op_b (sel l kb) (get_op_b o1) (get_op_b ol)
  else ()

val inter_right_base_1op_a (l a b :concrete_st_a) (o1 ob ol:op_a)
  : Lemma (requires Fst_then_snd? (rc_a ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    (Fst_then_snd? (rc_a ob o1) ==> eq_a (merge_a l (do_a a o1) (do_a b ob)) (do_a (merge_a l a (do_a b ob)) o1)) /\ //from app.fsti
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a b ol)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a b ol)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a b ob) ol)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a b ob) ol)) o1))

val inter_right_base_1op_b (l a b :concrete_st_b) (o1 ob ol:op_b)
  : Lemma (requires Fst_then_snd? (rc_b ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    (Fst_then_snd? (rc_b ob o1) ==> eq_b (merge_b l (do_b a o1) (do_b b ob)) (do_b (merge_b l a (do_b b ob)) o1)) /\ //from app.fsti
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b b ol)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b b ol)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b b ob) ol)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b b ob) ol)) o1))
          
let inter_right_base_1op (l a b :concrete_st) (o1 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    (Fst_then_snd? (rc ob o1) ==> eq (merge l (do a o1) (do b ob)) (do (merge l a (do b ob)) o1)) /\ //from app.fsti
                    eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ob) ol)) (do (merge (do l ol) (do a ol) (do (do b ob) ol)) o1)) =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key ob = k && is_alpha_op o1 && is_alpha_op ob && is_alpha_op ol && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then
      inter_right_base_1op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a ob) (get_op_a ol)
  else if get_key o1 = k && get_key ob = k && is_beta_op o1 && is_beta_op ob && is_beta_op ol && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then
      inter_right_base_1op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b ob) (get_op_b ol)
  else ()

val inter_left_base_1op_a (l a b :concrete_st_a) (o1 ob ol:op_a)
  : Lemma (requires Fst_then_snd? (rc_a ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a b ol)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a b ol)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a (do_a a ob) ol) o1) (do_a b ol)) (do_a (merge_a (do_a l ol) (do_a (do_a a ob) ol) (do_a b ol)) o1))

val inter_left_base_1op_b (l a b :concrete_st_b) (o1 ob ol:op_b)
  : Lemma (requires Fst_then_snd? (rc_b ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b b ol)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b b ol)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b (do_b a ob) ol) o1) (do_b b ol)) (do_b (merge_b (do_b l ol) (do_b (do_b a ob) ol) (do_b b ol)) o1))
          
let inter_left_base_1op (l a b:concrete_st) (o1 ob ol:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do a ob) ol) (do b ol)) o1)) =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key ob = k && is_alpha_op o1 && is_alpha_op ob && is_alpha_op ol && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then
      inter_left_base_1op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a ob) (get_op_a ol)
  else if get_key o1 = k && get_key ob = k && is_beta_op o1 && is_beta_op ob && is_beta_op ol && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then
      inter_left_base_1op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b ob) (get_op_b ol)
  else ()

val inter_right_1op_a (l a b :concrete_st_a) (o1 ob ol o:op_a)
  : Lemma (requires Fst_then_snd? (rc_a ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc_a o ob)) \/ Fst_then_snd? (rc_a o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a b ob) ol)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a b ob) ol)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a (do_a b o) ob) ol)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a (do_a b o) ob) ol)) o1))

val inter_right_1op_b (l a b :concrete_st_b) (o1 ob ol o:op_b)
  : Lemma (requires Fst_then_snd? (rc_b ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc_b o ob)) \/ Fst_then_snd? (rc_b o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b b ob) ol)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b b ob) ol)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b (do_b b o) ob) ol)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b (do_b b o) ob) ol)) o1))

#set-options "--z3rlimit 100 --ifuel 3"
let inter_right_1op (l a b:concrete_st) (o1 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ob) ol)) (do (merge (do l ol) (do a ol) (do (do b ob) ol)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b o) ob) ol)) (do (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) o1)) =
  let k = get_key o in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key ob = k && get_key ol = k && is_alpha_op o1 && is_alpha_op ob && is_alpha_op ol && is_alpha_op o && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) && (Fst_then_snd? (rc_a (get_op_a o) (get_op_a ob)) || Snd_then_fst? (rc_a (get_op_a o) (get_op_a ob)) || Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol))) then 
    inter_right_1op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a ob) (get_op_a ol) (get_op_a o)
  else if get_key o1 = k && get_key ob = k && get_key ol = k && is_beta_op o1 && is_beta_op ob && is_beta_op ol && is_beta_op o && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) && (Fst_then_snd? (rc_b (get_op_b o) (get_op_b ob)) || Snd_then_fst? (rc_b (get_op_b o) (get_op_b ob)) || Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol))) then
    inter_right_1op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b ob) (get_op_b ol) (get_op_b o)
  else ()

val inter_left_1op_a (l a b :concrete_st_a) (o1 ob ol o:op_a)
  : Lemma (requires Fst_then_snd? (rc_a ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc_a o ob)) \/ Fst_then_snd? (rc_a o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a (do_a a ob) ol) o1) (do_a b ol)) (do_a (merge_a (do_a l ol) (do_a (do_a a ob) ol) (do_a b ol)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a (do_a (do_a a o) ob) ol) o1) (do_a b ol)) (do_a (merge_a (do_a l ol) (do_a (do_a (do_a a o) ob) ol) (do_a b ol)) o1))

val inter_left_1op_b (l a b :concrete_st_b) (o1 ob ol o:op_b)
  : Lemma (requires Fst_then_snd? (rc_b ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc_b o ob)) \/ Fst_then_snd? (rc_b o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b (do_b a ob) ol) o1) (do_b b ol)) (do_b (merge_b (do_b l ol) (do_b (do_b a ob) ol) (do_b b ol)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b (do_b (do_b a o) ob) ol) o1) (do_b b ol)) (do_b (merge_b (do_b l ol) (do_b (do_b (do_b a o) ob) ol) (do_b b ol)) o1))
          
let inter_left_1op (l a b :concrete_st) (o1 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\               
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do a ob) ol) (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) o1)) =
  let k = get_key o in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key ob = k && get_key ol = k && is_alpha_op o1 && is_alpha_op ob && is_alpha_op ol && is_alpha_op o && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) && (Fst_then_snd? (rc_a (get_op_a o) (get_op_a ob)) || Snd_then_fst? (rc_a (get_op_a o) (get_op_a ob)) || Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol))) then 
    inter_left_1op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a ob) (get_op_a ol) (get_op_a o)
  else if get_key o1 = k && get_key ob = k && get_key ol = k && is_beta_op o1 && is_beta_op ob && is_beta_op ol && is_beta_op o && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) && (Fst_then_snd? (rc_b (get_op_b o) (get_op_b ob)) || Snd_then_fst? (rc_b (get_op_b o) (get_op_b ob)) || Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol))) then
    inter_left_1op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b ob) (get_op_b ol) (get_op_b o)
  else ()

val ind_right_1op_a (l a b:concrete_st_a) (o2 o2' ol:op_a)
  : Lemma (requires distinct_ops o2 o2' /\ distinct_ops o2 ol /\ distinct_ops o2' ol /\
                    eq_a (merge_a (do_a l ol) (do_a a ol) (do_a b o2)) (do_a (merge_a (do_a l ol) (do_a a ol) b) o2))
          (ensures eq_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a b o2') o2)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a b o2')) o2))

val ind_right_1op_b (l a b:concrete_st_b) (o2 o2' ol:op_b)
  : Lemma (requires distinct_ops o2 o2' /\ distinct_ops o2 ol /\ distinct_ops o2' ol /\
                    eq_b (merge_b (do_b l ol) (do_b a ol) (do_b b o2)) (do_b (merge_b (do_b l ol) (do_b a ol) b) o2))
          (ensures eq_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b b o2') o2)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b b o2')) o2))

val ind_right_1op' (l a b:concrete_st) (o2 o2' ol:op_t)
  : Lemma (requires distinct_ops o2 o2' /\ distinct_ops o2 ol /\ distinct_ops o2' ol /\ get_key o2 = get_key o2' /\
                    ~ (get_key o2 = get_key ol /\ get_key o2' = get_key ol /\ is_alpha_op o2 /\ is_alpha_op o2' /\ is_alpha_op ol) /\
                    ~ (get_key o2 = get_key ol /\ get_key o2' = get_key ol /\ is_beta_op o2 /\ is_beta_op o2' /\ is_beta_op ol) /\
                    eq (merge (do l ol) (do a ol) (do b o2)) (do (merge (do l ol) (do a ol) b) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do b o2') o2)) (do (merge (do l ol) (do a ol) (do b o2')) o2))

let ind_right_1op (l a b:concrete_st) (o2 o2' ol:op_t)
  : Lemma (requires distinct_ops o2 o2' /\ distinct_ops o2 ol /\ distinct_ops o2' ol /\
                    eq (merge (do l ol) (do a ol) (do b o2)) (do (merge (do l ol) (do a ol) b) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do b o2') o2)) (do (merge (do l ol) (do a ol) (do b o2')) o2)) =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o2 = k && get_key o2' = k && is_alpha_op o2 && is_alpha_op o2' && is_alpha_op ol then
      ind_right_1op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o2) (get_op_a o2') (get_op_a ol)
  else if get_key o2 = k && get_key o2' = k && is_beta_op o2 && is_beta_op o2' && is_beta_op ol then
      ind_right_1op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o2) (get_op_b o2') (get_op_b ol)
  else if get_key o2 = get_key o2' then ind_right_1op' l a b o2 o2' ol
  else ()

val ind_left_1op_a (l a b:concrete_st_a) (o1 o1' ol:op_a)
  : Lemma (requires distinct_ops o1 o1' /\ distinct_ops o1 ol /\ distinct_ops o1' ol /\
                    eq_a (merge_a (do_a l ol) (do_a a o1) (do_a b ol)) (do_a (merge_a (do_a l ol) a (do_a b ol)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a a o1') o1) (do_a b ol)) (do_a (merge_a (do_a l ol) (do_a a o1') (do_a b ol)) o1))

val ind_left_1op_b (l a b:concrete_st_b) (o1 o1' ol:op_b)
  : Lemma (requires distinct_ops o1 o1' /\ distinct_ops o1 ol /\ distinct_ops o1' ol /\
                    eq_b (merge_b (do_b l ol) (do_b a o1) (do_b b ol)) (do_b (merge_b (do_b l ol) a (do_b b ol)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b a o1') o1) (do_b b ol)) (do_b (merge_b (do_b l ol) (do_b a o1') (do_b b ol)) o1))

val ind_left_1op' (l a b:concrete_st) (o1 o1' ol:op_t)
  : Lemma (requires distinct_ops o1 o1' /\ distinct_ops o1 ol /\ distinct_ops o1' ol /\ get_key o1 = get_key o1' /\
                    ~ (get_key o1 = get_key ol /\ get_key o1' = get_key ol /\
                       is_alpha_op o1 /\ is_alpha_op o1' /\ is_alpha_op ol /\
                       is_beta_op o1 /\ is_beta_op o1' /\ is_beta_op ol) /\
                    eq (merge (do l ol) (do a o1) (do b ol)) (do (merge (do l ol) a (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do a o1') o1) (do b ol)) (do (merge (do l ol) (do a o1') (do b ol)) o1))

let ind_left_1op (l a b:concrete_st) (o1 o1' ol:op_t)
  : Lemma (requires distinct_ops o1 o1' /\ distinct_ops o1 ol /\ distinct_ops o1' ol /\
                    eq (merge (do l ol) (do a o1) (do b ol)) (do (merge (do l ol) a (do b ol)) o1))
          (ensures eq (merge (do l ol) (do (do a o1') o1) (do b ol)) (do (merge (do l ol) (do a o1') (do b ol)) o1)) = 
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o1' = k && is_alpha_op o1 && is_alpha_op o1' && is_alpha_op ol then
      ind_left_1op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a o1') (get_op_a ol)
  else if get_key o1 = k && get_key o1' = k && is_beta_op o1 && is_beta_op o1' && is_beta_op ol then
      ind_left_1op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b o1') (get_op_b ol)
  else if get_key o1 = get_key o1' then ind_left_1op' l a b o1 o1' ol
  else ()

(*Two OP*)
//////////////// 

val base_2op_a (o1 o2:op_a) 
  : Lemma (requires (Fst_then_snd? (rc_a o2 o1) \/ Either? (rc_a o2 o1)) /\ get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2)
          (ensures eq_a (merge_a init_st_a (do_a init_st_a o1) (do_a init_st_a o2)) 
                        (do_a (merge_a init_st_a init_st_a (do_a init_st_a o2)) o1))

val base_2op_b (o1 o2:op_b) 
  : Lemma (requires (Fst_then_snd? (rc_b o2 o1) \/ Either? (rc_b o2 o1)) /\ get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2)
          (ensures eq_b (merge_b init_st_b (do_b init_st_b o1) (do_b init_st_b o2)) 
                        (do_b (merge_b init_st_b init_st_b (do_b init_st_b o2)) o1))

let base_2op (o1 o2:op_t) (t:kt)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2)
                    //eq (merge (init_st t) (do (init_st t) o1) (init_st t)) (do (merge (init_st t) (init_st t) (init_st t)) o1)) //1op
          (ensures eq (merge (init_st t) (do (init_st t) o1) (do (init_st t) o2)) 
                      (do (merge (init_st t) (init_st t) (do (init_st t) o2)) o1)) =
  if get_key o1 = get_key o2 && is_alpha_op o1 && is_alpha_op o2 then
    base_2op_a (get_op_a o1) (get_op_a o2) 
  else if get_key o1 = get_key o2 && is_beta_op o1 && is_beta_op o2 then
    base_2op_b (get_op_b o1) (get_op_b o2) 
  else base_1op o1 t

val ind_lca_2op_a (l:concrete_st_a) (o1 o2 ol:op_a)
  : Lemma (requires (Fst_then_snd? (rc_a o2 o1) \/ Either? (rc_a o2 o1)) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    eq_a (merge_a l (do_a l o1) (do_a l o2)) (do_a (merge_a l l (do_a l o2)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a l ol) o1) (do_a (do_a l ol) o2)) (do_a (merge_a (do_a l ol) (do_a l ol) (do_a (do_a l ol) o2)) o1))

val ind_lca_2op_b (l:concrete_st_b) (o1 o2 ol:op_b)
  : Lemma (requires (Fst_then_snd? (rc_b o2 o1) \/ Either? (rc_b o2 o1)) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    eq_b (merge_b l (do_b l o1) (do_b l o2)) (do_b (merge_b l l (do_b l o2)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b l ol) o1) (do_b (do_b l ol) o2)) (do_b (merge_b (do_b l ol) (do_b l ol) (do_b (do_b l ol) o2)) o1))

#set-options "--z3rlimit 200 --ifuel 3"
let ind_lca_2op (l:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    eq (merge l (do l o1) l) (do (merge l l l) o1) /\ //1op
                    //eq (merge (do l ol) (do (do l ol) o1) (do l ol)) (do (merge (do l ol) (do l ol) (do l ol)) o1) /\ //1op
                    eq (merge l (do l o1) (do l o2)) (do (merge l l (do l o2)) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (merge (do l ol) (do l ol) (do (do l ol) o2)) o1)) =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ol && (Fst_then_snd? (rc_a (get_op_a o2) (get_op_a o1)) || Either? (rc_a (get_op_a o2) (get_op_a o1))) then
      ind_lca_2op_a (sel l ka) (get_op_a o1) (get_op_a o2) (get_op_a ol)
  else if get_key o1 = k && get_key o2 = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ol && (Fst_then_snd? (rc_b (get_op_b o2) (get_op_b o1)) || Either? (rc_b (get_op_b o2) (get_op_b o1))) then
      ind_lca_2op_b (sel l kb) (get_op_b o1) (get_op_b o2) (get_op_b ol)
  else ind_lca_1op l o1 ol

val inter_right_base_2op_a (l a b :concrete_st_a) (o1 o2 ob ol:op_a)
  : Lemma (requires (Fst_then_snd? (rc_a o2 o1) \/ Either? (rc_a o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc_a ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_a (merge_a l (do_a a o1) (do_a b o2)) (do_a (merge_a l a (do_a b o2)) o1) /\ //from pre-cond of ind_right_2op
                    eq_a (merge_a l (do_a a o1) (do_a (do_a b ob) o2)) (do_a (merge_a l a (do_a (do_a b ob) o2)) o1) /\ //from ind_right_2op
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a b ol) o2)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a b ol) o2)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a (do_a b ob) ol) o2)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a (do_a b ob) ol) o2)) o1))

val inter_right_base_2op_b (l a b :concrete_st_b) (o1 o2 ob ol:op_b)
  : Lemma (requires (Fst_then_snd? (rc_b o2 o1) \/ Either? (rc_b o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc_b ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_b (merge_b l (do_b a o1) (do_b b o2)) (do_b (merge_b l a (do_b b o2)) o1) /\ //from pre-cond of ind_right_2op
                    eq_b (merge_b l (do_b a o1) (do_b (do_b b ob) o2)) (do_b (merge_b l a (do_b (do_b b ob) o2)) o1) /\ //from ind_right_2op
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b b ol) o2)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b b ol) o2)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b (do_b b ob) ol) o2)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b (do_b b ob) ol) o2)) o1))

let inter_right_base_2op (l a b :concrete_st) (o1 o2 ob ol:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1) /\ //1op
                    //eq (merge (do l ol) (do (do a ol) o1) (do (do b ob) ol)) (do (merge (do l ol) (do a ol) (do (do b ob) ol)) o1) /\ //1op
                    eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) /\ //from pre-cond of ind_right_2op
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (merge l a (do (do b ob) o2)) o1) /\ //from ind_right_2op
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do a ol) (do (do b ol) o2)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) o1)) =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && get_key ob = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob && is_alpha_op ol && (Fst_then_snd? (rc_a (get_op_a o2) (get_op_a o1)) || Either? (rc_a (get_op_a o2) (get_op_a o1))) && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then
      inter_right_base_2op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a o2) (get_op_a ob) (get_op_a ol)
  else if get_key o1 = k && get_key o2 = k && get_key ob = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ob && is_beta_op ol && (Fst_then_snd? (rc_b (get_op_b o2) (get_op_b o1)) || Either? (rc_b (get_op_b o2) (get_op_b o1))) && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then
      inter_right_base_2op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b o2) (get_op_b ob) (get_op_b ol)
  else inter_right_base_1op l a b o1 ob ol

val inter_left_base_2op_a (l a b :concrete_st_a) (o1 o2 ob ol:op_a)
  : Lemma (requires (Fst_then_snd? (rc_a o2 o1) \/ Either? (rc_a o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc_a ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a b ol) o2)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a b ol) o2)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a (do_a a ob) ol) o1) (do_a (do_a b ol) o2)) (do_a (merge_a (do_a l ol) (do_a (do_a a ob) ol) (do_a (do_a b ol) o2)) o1))

val inter_left_base_2op_b (l a b :concrete_st_b) (o1 o2 ob ol:op_b)
  : Lemma (requires (Fst_then_snd? (rc_b o2 o1) \/ Either? (rc_b o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc_b ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b b ol) o2)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b b ol) o2)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b (do_b a ob) ol) o1) (do_b (do_b b ol) o2)) (do_b (merge_b (do_b l ol) (do_b (do_b a ob) ol) (do_b (do_b b ol) o2)) o1))

let inter_left_base_2op (l a b :concrete_st) (o1 o2 ob ol:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1) /\ //1op
                    //eq (merge (do l ol) (do (do (do a ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do a ob) ol) (do b ol)) o1) /\ //1op
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do a ol) (do (do b ol) o2)) o1))
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) o1)) =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && get_key ob = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob && is_alpha_op ol && (Fst_then_snd? (rc_a (get_op_a o2) (get_op_a o1)) || Either? (rc_a (get_op_a o2) (get_op_a o1))) && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then
      inter_left_base_2op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a o2) (get_op_a ob) (get_op_a ol)
  else if get_key o1 = k && get_key o2 = k && get_key ob = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ob && is_beta_op ol && (Fst_then_snd? (rc_b (get_op_b o2) (get_op_b o1)) || Either? (rc_b (get_op_b o2) (get_op_b o1))) && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then
      inter_left_base_2op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b o2) (get_op_b ob) (get_op_b ol)
  else inter_left_base_1op l a b o1 ob ol

val inter_right_2op_a (l a b :concrete_st_a) (o1 o2 ob ol o:op_a)
  : Lemma (requires (Fst_then_snd? (rc_a o2 o1) \/ Either? (rc_a o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc_a ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc_a o ob)) \/ Fst_then_snd? (rc_a o ol)) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a (do_a b ob) ol) o2)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a (do_a b ob) ol) o2)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a (do_a (do_a b o) ob) ol) o2)) (do_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a (do_a (do_a b o) ob) ol) o2)) o1))

val inter_right_2op_b (l a b :concrete_st_b) (o1 o2 ob ol o:op_b)
  : Lemma (requires (Fst_then_snd? (rc_b o2 o1) \/ Either? (rc_b o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc_b ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc_b o ob)) \/ Fst_then_snd? (rc_b o ol)) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b (do_b b ob) ol) o2)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b (do_b b ob) ol) o2)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b (do_b (do_b b o) ob) ol) o2)) (do_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b (do_b (do_b b o) ob) ol) o2)) o1))
          
let inter_right_2op (l a b :concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\               
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ob) ol)) (do (merge (do l ol) (do a ol) (do (do b ob) ol)) o1) /\ //1op
                    //eq (merge (do l ol) (do (do a ol) o1) (do (do (do b o) ob) ol)) (do (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) o1) /\ //1op
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) o1))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) o1)) =
  let k = get_key o in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && get_key ob = k && get_key ol = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob && is_alpha_op ol && is_alpha_op o && (Fst_then_snd? (rc_a (get_op_a o2) (get_op_a o1)) || Either? (rc_a (get_op_a o2) (get_op_a o1))) && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) && (Fst_then_snd? (rc_a (get_op_a o) (get_op_a ob)) || Snd_then_fst? (rc_a (get_op_a o) (get_op_a ob)) || Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol))) then 
    inter_right_2op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a o2) (get_op_a ob) (get_op_a ol) (get_op_a o)
  else if get_key o1 = k && get_key o2 = k && get_key ob = k && get_key ol = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ob && is_beta_op ol && is_beta_op o && (Fst_then_snd? (rc_b (get_op_b o2) (get_op_b o1)) || Either? (rc_b (get_op_b o2) (get_op_b o1))) && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) && (Fst_then_snd? (rc_b (get_op_b o) (get_op_b ob)) || Snd_then_fst? (rc_b (get_op_b o) (get_op_b ob)) || Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol))) then
    inter_right_2op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b o2) (get_op_b ob) (get_op_b ol) (get_op_b o)
  else inter_right_1op l a b o1 ob ol o

val inter_left_2op_a (l a b :concrete_st_a) (o1 o2 ob ol o:op_a)
  : Lemma (requires (Fst_then_snd? (rc_a o2 o1) \/ Either? (rc_a o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc_a ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc_a o ob)) \/ Fst_then_snd? (rc_a o ol)) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a (do_a a ob) ol) o1) (do_a (do_a b ol) o2)) (do_a (merge_a (do_a l ol) (do_a (do_a a ob) ol) (do_a (do_a b ol) o2)) o1))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a (do_a (do_a a o) ob) ol) o1) (do_a (do_a b ol) o2)) (do_a (merge_a (do_a l ol) (do_a (do_a (do_a a o) ob) ol) (do_a (do_a b ol) o2)) o1))

val inter_left_2op_b (l a b :concrete_st_b) (o1 o2 ob ol o:op_b)
  : Lemma (requires (Fst_then_snd? (rc_b o2 o1) \/ Either? (rc_b o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc_b ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc_b o ob)) \/ Fst_then_snd? (rc_b o ol)) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b (do_b a ob) ol) o1) (do_b (do_b b ol) o2)) (do_b (merge_b (do_b l ol) (do_b (do_b a ob) ol) (do_b (do_b b ol) o2)) o1))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b (do_b (do_b a o) ob) ol) o1) (do_b (do_b b ol) o2)) (do_b (merge_b (do_b l ol) (do_b (do_b (do_b a o) ob) ol) (do_b (do_b b ol) o2)) o1))
          
let inter_left_2op (l a b :concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires (Fst_then_snd? (rc o2 o1) \/ Either? (rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\ Fst_then_snd? (rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\               
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do a ob) ol) (do b ol)) o1) /\ //1op
                    //eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do b ol)) (do (merge (do l ol) (do (do (do a o) ob) ol) (do b ol)) o1) /\ //1op
                    get_rid o <> get_rid ol /\ //from app.fsti
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) o1))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) o1)) =
  let k = get_key o in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && get_key ob = k && get_key ol = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob && is_alpha_op ol && is_alpha_op o && (Fst_then_snd? (rc_a (get_op_a o2) (get_op_a o1)) || Either? (rc_a (get_op_a o2) (get_op_a o1))) && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) && (Fst_then_snd? (rc_a (get_op_a o) (get_op_a ob)) || Snd_then_fst? (rc_a (get_op_a o) (get_op_a ob)) || Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol))) then 
    inter_left_2op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a o2) (get_op_a ob) (get_op_a ol) (get_op_a o)
  else if get_key o1 = k && get_key o2 = k && get_key ob = k && get_key ol = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ob && is_beta_op ol && is_beta_op o && (Fst_then_snd? (rc_b (get_op_b o2) (get_op_b o1)) || Either? (rc_b (get_op_b o2) (get_op_b o1))) && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) && (Fst_then_snd? (rc_b (get_op_b o) (get_op_b ob)) || Snd_then_fst? (rc_b (get_op_b o) (get_op_b ob)) || Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol))) then
    inter_left_2op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b o2) (get_op_b ob) (get_op_b ol) (get_op_b o)
  else inter_left_1op l a b o1 ob ol o

val ind_right_2op_a (l a b:concrete_st_a) (o1 o2 o2':op_a)
  : Lemma (requires Fst_then_snd? (rc_a o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    eq_a (merge_a l (do_a a o1) (do_a b o2)) (do_a (merge_a l a (do_a b o2)) o1))
          (ensures eq_a (merge_a l (do_a a o1) (do_a (do_a b o2') o2)) (do_a (merge_a l a (do_a (do_a b o2') o2)) o1))

val ind_right_2op_b (l a b:concrete_st_b) (o1 o2 o2':op_b)
  : Lemma (requires Fst_then_snd? (rc_b o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    eq_b (merge_b l (do_b a o1) (do_b b o2)) (do_b (merge_b l a (do_b b o2)) o1))
          (ensures eq_b (merge_b l (do_b a o1) (do_b (do_b b o2') o2)) (do_b (merge_b l a (do_b (do_b b o2') o2)) o1))

let ind_right_2op (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l a (do (do b o2') o2)) o1)) =
  let k = get_key o2' in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op o2' && Fst_then_snd? (rc_a (get_op_a o2) (get_op_a o1)) then
      ind_right_2op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a o2) (get_op_a o2')
  else if get_key o1 = k && get_key o2 = k && is_beta_op o1 && is_beta_op o2 && is_beta_op o2' && Fst_then_snd? (rc_b (get_op_b o2) (get_op_b o1)) then
      ind_right_2op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b o2) (get_op_b o2')
  else ()

val ind_left_2op_a (l a b:concrete_st_a) (o1 o2 o1':op_a)
  : Lemma (requires Fst_then_snd? (rc_a o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq_a (merge_a l (do_a a o1) (do_a b o2)) (do_a (merge_a l a (do_a b o2)) o1))
          (ensures eq_a (merge_a l (do_a (do_a a o1') o1) (do_a b o2)) (do_a (merge_a l (do_a a o1') (do_a b o2)) o1))

val ind_left_2op_b (l a b:concrete_st_b) (o1 o2 o1':op_b)
  : Lemma (requires Fst_then_snd? (rc_b o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq_b (merge_b l (do_b a o1) (do_b b o2)) (do_b (merge_b l a (do_b b o2)) o1))
          (ensures eq_b (merge_b l (do_b (do_b a o1') o1) (do_b b o2)) (do_b (merge_b l (do_b a o1') (do_b b o2)) o1))

let ind_left_2op (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do a o1') (do b o2)) o1)) =
  let k = get_key o1' in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op o1' && Fst_then_snd? (rc_a (get_op_a o2) (get_op_a o1)) then
      ind_left_2op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a o2) (get_op_a o1')
  else if get_key o1 = k && get_key o2 = k && is_beta_op o1 && is_beta_op o2 && is_beta_op o1' && Fst_then_snd? (rc_b (get_op_b o2) (get_op_b o1)) then
      ind_left_2op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b o2) (get_op_b o1')
  else ()

