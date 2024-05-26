module Polymorphic_gmap

module S = Set_extended
module M = Map_extended
open FStar.Seq

#set-options "--query_stats"
//key type
type key_t =
  |Alpha_t
  |Beta_t

val concrete_st_a : Type0

val concrete_st_b : Type0

// concrete state of values
noeq type concrete_st_v = 
  |Alpha : concrete_st_a -> concrete_st_v
  |Beta : concrete_st_b -> concrete_st_v

let eq_key_t (s:M.t (string & key_t) concrete_st_v) =
  (forall sk. M.contains s sk ==> (let v = M.sel s sk in
         ((Alpha? v <==> snd sk == Alpha_t) /\ (Beta? v <==> snd sk = Beta_t))))

//concrete state
let concrete_st = s:M.t (string & key_t) concrete_st_v {eq_key_t s}

val init_st_a : concrete_st_a

val init_st_b : concrete_st_b

let init_st_v (t:key_t) =
  match t with
  |Alpha_t -> Alpha init_st_a
  |Beta_t -> Beta init_st_b

let init_st (t:key_t) : concrete_st = M.const_on S.empty (init_st_v t)

let geta (s:concrete_st_v{Alpha? s}) =
  let Alpha x = s in x

let getb (s:concrete_st_v{Beta? s}) =
  let Beta x = s in x

let sel_a (s:concrete_st) k  =
    if M.contains s (k,Alpha_t) then geta (M.sel s (k,Alpha_t)) else init_st_a

let sel_b (s:concrete_st) k  =
    if M.contains s (k,Beta_t) then getb (M.sel s (k,Beta_t)) else init_st_b

let eq_a (a b:concrete_st_a) : Type0 = a == b

let eq_b (a b:concrete_st_b) : Type0 = a == b

let eq_v (a:concrete_st_v) (b:concrete_st_v) : Type0 = //{(Ctr? a ==> Ctr? b) /\ (Gset? a ==> Gset? b)}) : Type0 =
  match a,b with
  |Alpha x,Alpha y -> eq_a x y
  |Beta x, Beta y -> eq_b x y
  |_ -> False

// equivalence relation
let eq (a b:concrete_st) =
  (forall k t. M.contains a (k,t) = M.contains b (k,t)) /\
  (forall k t. M.contains a (k,t) ==> (Alpha_t? t ==> eq_a (sel_a a k) (sel_a b k)) /\
                                 (Beta_t? t ==> eq_b (sel_b a k) (sel_b b k)))

val symmetric_a (a b:concrete_st_a)
  : Lemma (requires eq_a a b)
          (ensures eq_a b a) 
          [SMTPat (eq_a a b)]

val symmetric_b (a b:concrete_st_b)
  : Lemma (requires eq_b a b)
          (ensures eq_b b a) 
          [SMTPat (eq_b a b)]
          
let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

val transitive_a (a b c:concrete_st_a)
  : Lemma (requires eq_a a b /\ eq_a b c)
          (ensures eq_a a c)
          [SMTPat (eq_a a b /\ eq_a b c)]

val transitive_b (a b c:concrete_st_b)
  : Lemma (requires eq_b a b /\ eq_b b c)
          (ensures eq_b a c)
          [SMTPat (eq_b a b /\ eq_b b c)]
          
val transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) 

val eq_is_equiv_a (a b:concrete_st_a)
  : Lemma (requires a == b)
          (ensures eq_a a b) 
          [SMTPat (a == b)]

val eq_is_equiv_b (a b:concrete_st_b)
  : Lemma (requires a == b)
          (ensures eq_b a b)
          [SMTPat (a == b)]
          
val eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b)

val app_op_a : eqtype

val app_op_b : eqtype
  
type app_op_v : eqtype =
  |Alpha_op : app_op_a -> app_op_v
  |Beta_op : app_op_b -> app_op_v

//operation type
type app_op_t:eqtype =
  |Set : string (* key *) -> app_op_v (* value *) -> app_op_t
  
type op_t = pos (*timestamp*) & (nat (*replica ID*) & app_op_t)

type op_v = pos (*timestamp*) & (nat (*replica ID*) & app_op_v)

type op_a = pos (*timestamp*) & (nat (*replica ID*) & app_op_a)

type op_b = pos (*timestamp*) & (nat (*replica ID*) & app_op_b)

let is_alpha_op (o:op_t) =
  match snd (snd o) with
  |Set _ (Alpha_op _) -> true
  |_ -> false

let is_beta_op (o:op_t) = not (is_alpha_op o)
  
let get_op_a (o:op_t{is_alpha_op o}) : op_a =
  match o with
  |ts, (rid, Set _ (Alpha_op op)) -> (ts,(rid,op))

let get_op_b (o:op_t{~ (is_alpha_op o)}) : op_b =
  match o with
  |ts, (rid, Set _ (Beta_op op)) -> (ts,(rid,op))

val do_a (s:concrete_st_a) (o:op_a) : concrete_st_a

val do_b (s:concrete_st_b) (o:op_b) : concrete_st_b

let do_v (s:concrete_st_v) (o:op_t) : concrete_st_v =
  match snd (snd o) with
  |Set _ (Alpha_op _) -> begin match s with
                        |Alpha c -> Alpha (do_a c (get_op_a o))
                        |_ -> Alpha (do_a init_st_a (get_op_a o))
                        end
  |Set _ (Beta_op _) -> begin match s with
                       |Beta c -> Beta (do_b c (get_op_b o))
                       |_ -> Beta (do_b init_st_b (get_op_b o))
                       end

let get_rid (_,(rid,_)) = rid

let distinct_ops (ts1,_) (ts2,_) = ts1 =!= ts2

let get_op_v (o:op_t) : op_v =
  match o with
  |(ts,(rid,(Set k op))) -> (ts,(rid,op))

let do (s:concrete_st) (o:op_t(*{do_pre s o}*)) : concrete_st =
  match o with
    |_,(_,Set k (Alpha_op _)) -> M.upd s (k,Alpha_t) (do_v (Alpha (sel_a s k)) o)
    |_,(_,Set k (Beta_op _)) -> M.upd s (k,Beta_t) (do_v (Beta (sel_b s k)) o)

let get_key (_,(_,Set k _)) = k

type rc_res =
  |Fst_then_snd //o1 -> o2
  |Snd_then_fst //o2 -> o1
  |Either

val rc_a (o1 o2:op_a) : rc_res

val rc_b (o1 o2:op_b) : rc_res

//conflict resolution
let rc (o1:op_t) (o2:op_t(*{distinct_ops o1 o2}*)) : rc_res = 
  match snd (snd o1), snd (snd o2) with
  |Set k1 (Alpha_op _), Set k2 (Alpha_op _) -> if k1 = k2 then rc_a (get_op_a o1) (get_op_a o2) else Either
  |Set k1 (Beta_op _), Set k2 (Beta_op _) -> if k1 = k2 then rc_b (get_op_b o1) (get_op_b o2) else Either
  |_ -> Either

val merge_a (l a b:concrete_st_a) : concrete_st_a 

val merge_b (l a b:concrete_st_b) : concrete_st_b

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun (k,t) v -> if Alpha_t? t then Alpha (merge_a (sel_a l k) (sel_a a k) (sel_a b k))
                          else Beta (merge_b (sel_b l k) (sel_b a k) (sel_b b k))) u

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

(*Two OP RC*)
//////////////// 
val rc_ind_right_a (l a b:concrete_st_a) (o1 o2 o2':op_a) 
  : Lemma (requires Fst_then_snd? (rc_a o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    eq_a (merge_a l (do_a a o1) (do_a b o2)) (do_a (merge_a l (do_a a o1) b) o2))
          (ensures eq_a (merge_a l (do_a a o1) (do_a (do_a b o2') o2)) (do_a (merge_a l (do_a a o1) (do_a b o2')) o2))

val rc_ind_right_b (l a b:concrete_st_b) (o1 o2 o2':op_b) 
  : Lemma (requires Fst_then_snd? (rc_b o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    eq_b (merge_b l (do_b a o1) (do_b b o2)) (do_b (merge_b l (do_b a o1) b) o2))
          (ensures eq_b (merge_b l (do_b a o1) (do_b (do_b b o2') o2)) (do_b (merge_b l (do_b a o1) (do_b b o2')) o2))

val rc_ind_right_ne (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    ~ (get_key o2 = get_key o2' /\ 
                       (is_alpha_op o2' /\ is_alpha_op o1 /\ Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2))) /\
                       (is_beta_op o2' /\ is_beta_op o1 /\ Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)))) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2))  
          
let rc_ind_right (l a b:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\  
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l (do a o1) (do b o2')) o2)) =
  let k = get_key o2' in
  if is_alpha_op o2' && is_alpha_op o1 && get_key o2 = k && Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) then
    rc_ind_right_a (sel_a l k) (sel_a a k) (sel_a b k) (get_op_a o1) (get_op_a o2) (get_op_a o2')
  else if is_beta_op o2' && is_beta_op o1 && get_key o2 = k && Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) then 
    rc_ind_right_b (sel_b l k) (sel_b a k) (sel_b b k) (get_op_b o1) (get_op_b o2) (get_op_b o2')
  else rc_ind_right_ne l a b o1 o2 o2'

val rc_ind_left_a (l a b:concrete_st_a) (o1 o2 o1':op_a) 
  : Lemma (requires Fst_then_snd? (rc_a o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\  
                    eq_a (merge_a l (do_a a o1) (do_a b o2)) (do_a (merge_a l (do_a a o1) b) o2))
          (ensures eq_a (merge_a l (do_a (do_a a o1') o1) (do_a b o2)) (do_a (merge_a l (do_a (do_a a o1') o1) b) o2))

val rc_ind_left_b (l a b:concrete_st_b) (o1 o2 o1':op_b) 
  : Lemma (requires Fst_then_snd? (rc_b o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\  
                    eq_b (merge_b l (do_b a o1) (do_b b o2)) (do_b (merge_b l (do_b a o1) b) o2))
          (ensures eq_b (merge_b l (do_b (do_b a o1') o1) (do_b b o2)) (do_b (merge_b l (do_b (do_b a o1') o1) b) o2))

val rc_ind_left_ne (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\  
                    ~ (get_key o2 = get_key o1' /\ 
                       (is_alpha_op o1' /\ is_alpha_op o1 /\ Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2))) /\
                       (is_beta_op o1' /\ is_beta_op o1 /\ Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)))) /\
                   eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2))

let rc_ind_left (l a b:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l (do a o1) b) o2))
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do (do a o1') o1) b) o2)) =
  let k = get_key o1' in
  if is_alpha_op o1' && is_alpha_op o1 && get_key o2 = k && Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) then
    rc_ind_left_a (sel_a l k) (sel_a a k) (sel_a b k) (get_op_a o1) (get_op_a o2) (get_op_a o1')
  else if is_beta_op o1' && is_beta_op o1 && get_key o2 = k && Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) then 
    rc_ind_left_b (sel_b l k) (sel_b a k) (sel_b b k) (get_op_b o1) (get_op_b o2) (get_op_b o1')
  else rc_ind_left_ne l a b o1 o2 o1'

val rc_ind_lca_a (l:concrete_st_a) (o1 o2 o:op_a)
  : Lemma (requires Fst_then_snd? (rc_a o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq_a (merge_a l (do_a l o1) (do_a l o2)) (do_a (do_a l o1) o2))
          (ensures eq_a (merge_a (do_a l o) (do_a (do_a l o) o1) (do_a (do_a l o) o2)) (do_a (do_a (do_a l o) o1) o2))

val rc_ind_lca_b (l:concrete_st_b) (o1 o2 o:op_b)
  : Lemma (requires Fst_then_snd? (rc_b o1 o2) /\
                    distinct_ops o1 o2 /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq_b (merge_b l (do_b l o1) (do_b l o2)) (do_b (do_b l o1) o2))
          (ensures eq_b (merge_b (do_b l o) (do_b (do_b l o) o1) (do_b (do_b l o) o2)) (do_b (do_b (do_b l o) o1) o2))

//Special case of rc_intermediate_v1
let rc_ind_lca (l:concrete_st) (o1 o2 o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o o1 /\ distinct_ops o o2 /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o1) o2))
          (ensures eq (merge (do l o) (do (do l o) o1) (do (do l o) o2)) (do (do (do l o) o1) o2)) =
  let k = get_key o in
  if get_key o1 = k && is_alpha_op o1 && is_alpha_op o && Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) then 
    rc_ind_lca_a (sel_a l k) (get_op_a o1) (get_op_a o2) (get_op_a o)
  else if get_key o1 = k && is_beta_op o1 && is_beta_op o && Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) then 
    rc_ind_lca_b (sel_b l k) (get_op_b o1) (get_op_b o2) (get_op_b o)
  else ()

val rc_base (o1 o2:op_t) (t:key_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge (init_st t) (do (init_st t) o1) (do (init_st t) o2)) (do (do (init_st t) o1) o2))

val rc_inter_base_right_a (l a b c:concrete_st_a) (o1 o2 ob ol:op_a)
  : Lemma (requires Fst_then_snd? (rc_a o1 o2) /\ Fst_then_snd? (rc_a ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a b ol) o2)) (do_a (do_a (do_a c ol) o1) o2) /\
                    eq_a (merge_a l (do_a a o1) (do_a b o2)) (do_a (do_a c o1) o2) /\
                    eq_a (merge_a l (do_a a ol) (do_a b ob)) (do_a (do_a c ob) ol)) //***EXTRA***
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a (do_a b ob) ol) o2)) (do_a (do_a (do_a (do_a c ob) ol) o1) o2))

val rc_inter_base_right_b (l a b c:concrete_st_b) (o1 o2 ob ol:op_b)
  : Lemma (requires Fst_then_snd? (rc_b o1 o2) /\ Fst_then_snd? (rc_b ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b b ol) o2)) (do_b (do_b (do_b c ol) o1) o2) /\
                    eq_b (merge_b l (do_b a o1) (do_b b o2)) (do_b (do_b c o1) o2) /\
                    eq_b (merge_b l (do_b a ol) (do_b b ob)) (do_b (do_b c ob) ol)) //***EXTRA***
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b (do_b b ob) ol) o2)) (do_b (do_b (do_b (do_b c ob) ol) o1) o2))
          
val rc_inter_base_right_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (get_key o2 = get_key ob /\
                       (is_alpha_op o1 /\ is_alpha_op ob /\ Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) /\ Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol))) /\
                       (is_beta_op o1 /\ is_beta_op ob /\ Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) /\ Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          
let rc_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) =
  let k = get_key ob in
  if get_key o2 = k && is_alpha_op o1 && is_alpha_op ob && Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then 
    rc_inter_base_right_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o1) (get_op_a o2) (get_op_a ob) (get_op_a ol)
  else if get_key o2 = k && is_beta_op o1 && is_beta_op ob && Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then 
    rc_inter_base_right_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o1) (get_op_b o2) (get_op_b ob) (get_op_b ol)
  else rc_inter_base_right_ne l a b c o1 o2 ob ol

val rc_inter_base_left_a (l a b c:concrete_st_a) (o1 o2 ob ol:op_a)
  : Lemma (requires Fst_then_snd? (rc_a o1 o2) /\ Fst_then_snd? (rc_a ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a b ol) o2)) (do_a (do_a (do_a c ol) o1) o2) /\
                    eq_a (merge_a l (do_a a o1) (do_a b o2)) (do_a (do_a c o1) o2) /\
                    eq_a (merge_a l (do_a a ob) (do_a b ol)) (do_a (do_a c ob) ol)) //***EXTRA***
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a (do_a a ob) ol) o1) (do_a (do_a b ol) o2)) (do_a (do_a (do_a (do_a c ob) ol) o1) o2))

val rc_inter_base_left_b (l a b c:concrete_st_b) (o1 o2 ob ol:op_b)
  : Lemma (requires Fst_then_snd? (rc_b o1 o2) /\ Fst_then_snd? (rc_b ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b b ol) o2)) (do_b (do_b (do_b c ol) o1) o2) /\
                    eq_b (merge_b l (do_b a o1) (do_b b o2)) (do_b (do_b c o1) o2) /\
                    eq_b (merge_b l (do_b a ob) (do_b b ol)) (do_b (do_b c ob) ol)) //***EXTRA***
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b (do_b a ob) ol) o1) (do_b (do_b b ol) o2)) (do_b (do_b (do_b (do_b c ob) ol) o1) o2))
          
val rc_inter_base_left_ne (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    ~ (get_key o2 = get_key ob /\
                       (is_alpha_op o1 /\ is_alpha_op ob /\ Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) /\ Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol))) /\
                       (is_beta_op o1 /\ is_beta_op ob /\ Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) /\ Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          
let rc_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\ 
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) =
  let k = get_key ob in
  if get_key o2 = k && is_alpha_op o1 && is_alpha_op ob && Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then 
    rc_inter_base_left_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o1) (get_op_a o2) (get_op_a ob) (get_op_a ol)
  else if get_key o2 = k && is_beta_op o1 && is_beta_op ob && Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then 
    rc_inter_base_left_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o1) (get_op_b o2) (get_op_b ob) (get_op_b ol)
  else rc_inter_base_left_ne l a b c o1 o2 ob ol

val rc_inter_right_a (l a b c:concrete_st_a) (o1 o2 ob ol o:op_a)
  : Lemma (requires Fst_then_snd? (rc_a o1 o2) /\ Fst_then_snd? (rc_a ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc_a o ob)) \/ Fst_then_snd? (rc_a o ol)) /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a (do_a b ob) ol) o2)) (do_a (do_a (do_a (do_a c ob) ol) o1) o2))
      (ensures eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a (do_a (do_a b o) ob) ol) o2)) (do_a (do_a (do_a (do_a (do_a c o) ob) ol) o1) o2))

val rc_inter_right_b (l a b c:concrete_st_b) (o1 o2 ob ol o:op_b)
  : Lemma (requires Fst_then_snd? (rc_b o1 o2) /\ Fst_then_snd? (rc_b ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc_b o ob)) \/ Fst_then_snd? (rc_b o ol)) /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b (do_b b ob) ol) o2)) (do_b (do_b (do_b (do_b c ob) ol) o1) o2))
      (ensures eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b (do_b (do_b b o) ob) ol) o2)) (do_b (do_b (do_b (do_b (do_b c o) ob) ol) o1) o2))
      
val rc_inter_right_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (get_key o2 = get_key o /\ get_key o2 = get_key ob /\
                       (is_alpha_op o1 /\ is_alpha_op o2 /\ is_alpha_op ob /\ Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) /\ Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol))) /\
                       (is_beta_op o1 /\ is_beta_op ob /\ Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) /\ Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol))) /\
                       (~ (Either? (rc_a (get_op_a o) (get_op_a ob))) \/ Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol))) /\
                       (~ (Either? (rc_b (get_op_b o) (get_op_b ob))) \/ Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2))

let rc_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) =
  let k = get_key o in
  assert (get_key o1 = get_key o2); assert (get_key ob = get_key ol);
  if get_key o2 = k && get_key o2 = get_key ob && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob && is_alpha_op ol && is_alpha_op o && Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) && (Fst_then_snd? (rc_a (get_op_a o) (get_op_a ob)) || Snd_then_fst? (rc_a (get_op_a o) (get_op_a ob)) || Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol))) then 
    rc_inter_right_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o1) (get_op_a o2) (get_op_a ob) (get_op_a ol) (get_op_a o)
  else if get_key o2 = k && get_key o2 = get_key ob && is_beta_op o1 && is_beta_op ob && is_beta_op o && Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) && (Fst_then_snd? (rc_b (get_op_b o) (get_op_b ob)) || Snd_then_fst? (rc_b (get_op_b o) (get_op_b ob)) || Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol))) then
    rc_inter_right_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o1) (get_op_b o2) (get_op_b ob) (get_op_b ol) (get_op_b o)
  else rc_inter_right_ne l a b c o1 o2 ob ol o

val rc_inter_left_a (l a b c:concrete_st_a) (o1 o2 ob ol o:op_a)
  : Lemma (requires Fst_then_snd? (rc_a o1 o2) /\ Fst_then_snd? (rc_a ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc_a o ob)) \/ Fst_then_snd? (rc_a o ol)) /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a (do_a a ob) ol) o1) (do_a (do_a b ol) o2)) (do_a (do_a (do_a (do_a c ob) ol) o1) o2))
      (ensures eq_a (merge_a (do_a l ol) (do_a (do_a (do_a (do_a a o) ob) ol) o1) (do_a (do_a b ol) o2)) (do_a (do_a (do_a (do_a (do_a c o) ob) ol) o1) o2)) 

val rc_inter_left_b (l a b c:concrete_st_b) (o1 o2 ob ol o:op_b)
  : Lemma (requires Fst_then_snd? (rc_b o1 o2) /\ Fst_then_snd? (rc_b ob ol) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    (~ (Either? (rc_b o ob)) \/ Fst_then_snd? (rc_b o ol)) /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b (do_b a ob) ol) o1) (do_b (do_b b ol) o2)) (do_b (do_b (do_b (do_b c ob) ol) o1) o2))
      (ensures eq_b (merge_b (do_b l ol) (do_b (do_b (do_b (do_b a o) ob) ol) o1) (do_b (do_b b ol) o2)) (do_b (do_b (do_b (do_b (do_b c o) ob) ol) o1) o2)) 
      
val rc_inter_left_ne (l a b c:concrete_st) (o1 o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    ~ (get_key o2 = get_key o /\ get_key o2 = get_key ob /\
                       (is_alpha_op o1 /\ is_alpha_op o2 /\ is_alpha_op ob /\ Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) /\ Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol))) /\
                       (is_beta_op o1 /\ is_beta_op ob /\ Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) /\ Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol))) /\
                       (~ (Either? (rc_a (get_op_a o) (get_op_a ob))) \/ Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol))) /\
                       (~ (Either? (rc_b (get_op_b o) (get_op_b ob))) \/ Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol)))) /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2))
      
let rc_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
      (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) =
  let k = get_key o in
  assert (get_key o1 = get_key o2); assert (get_key ob = get_key ol);
  if get_key o1 = k && get_key o2 = get_key ob && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob && is_alpha_op ol && is_alpha_op o && Fst_then_snd? (rc_a (get_op_a o1) (get_op_a o2)) && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) && (Fst_then_snd? (rc_a (get_op_a o) (get_op_a ob)) || Snd_then_fst? (rc_a (get_op_a o) (get_op_a ob)) || Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol))) then 
    rc_inter_left_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o1) (get_op_a o2) (get_op_a ob) (get_op_a ol) (get_op_a o)
  else if get_key o2 = k && get_key o2 = get_key ob && is_beta_op o1 && is_beta_op ob && is_beta_op o && Fst_then_snd? (rc_b (get_op_b o1) (get_op_b o2)) && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) && (Fst_then_snd? (rc_b (get_op_b o) (get_op_b ob)) || Snd_then_fst? (rc_b (get_op_b o) (get_op_b ob)) || Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol))) then
    rc_inter_left_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o1) (get_op_b o2) (get_op_b ob) (get_op_b ol) (get_op_b o)
  else rc_inter_left_ne l a b c o1 o2 ob ol o

//CHECK!!
val rc_inter_lca_a (l a b c:concrete_st_a) (o1 o2 ol oi:op_a)
  : Lemma (requires Fst_then_snd? (rc_a o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    (exists o. Fst_then_snd? (rc_a o ol)) /\ 
                    (exists o. Fst_then_snd? (rc_a o oi)) /\
                    eq_a (merge_a (do_a l oi) (do_a (do_a a oi) o1) (do_a (do_a b oi) o2)) (do_a (do_a (do_a c oi) o1) o2) /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ol) o1) (do_a (do_a b ol) o2)) (do_a (do_a (do_a c ol) o1) o2))
    (ensures eq_a (merge_a (do_a (do_a l oi) ol) (do_a (do_a (do_a a oi) ol) o1) (do_a (do_a (do_a b oi) ol) o2)) (do_a (do_a (do_a (do_a c oi) ol) o1) o2))

val rc_inter_lca_b (l a b c:concrete_st_b) (o1 o2 ol oi:op_b)
  : Lemma (requires Fst_then_snd? (rc_b o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    (exists o. Fst_then_snd? (rc_b o ol)) /\ 
                    (exists o. Fst_then_snd? (rc_b o oi)) /\
                    eq_b (merge_b (do_b l oi) (do_b (do_b a oi) o1) (do_b (do_b b oi) o2)) (do_b (do_b (do_b c oi) o1) o2) /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ol) o1) (do_b (do_b b ol) o2)) (do_b (do_b (do_b c ol) o1) o2))
    (ensures eq_b (merge_b (do_b (do_b l oi) ol) (do_b (do_b (do_b a oi) ol) o1) (do_b (do_b (do_b b oi) ol) o2)) (do_b (do_b (do_b (do_b c oi) ol) o1) o2))
    
val rc_inter_lca_ne (l a b c:concrete_st) (o1 o2 ol oi:op_t) 
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    ~ ((get_key o1 = get_key o2 /\ get_key o1 = get_key oi /\ get_key o1 = get_key ol) /\
                       (is_alpha_op o1 /\ is_alpha_op ol /\ is_alpha_op oi) /\
                       (is_beta_op o1 && is_beta_op ol && is_beta_op oi)) /\
                    
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2))
      
// In general, the events ol,oi, below should be such that these exists o, (rc o ol), (rc o oi)
let rc_inter_lca (l a b c:concrete_st) (o1 o2 ol oi:op_t)
  : Lemma (requires Fst_then_snd? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o1 oi /\ distinct_ops o2 ol /\ distinct_ops o2 oi /\ distinct_ops ol oi /\
                    (exists o. Fst_then_snd? (rc o ol)) /\ 
                    (exists o. Fst_then_snd? (rc o oi)) /\ 
                    eq (merge (do l oi) (do (do a oi) o1) (do (do b oi) o2)) (do (do (do c oi) o1) o2) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2))
    (ensures eq (merge (do (do l oi) ol) (do (do (do a oi) ol) o1) (do (do (do b oi) ol) o2)) (do (do (do (do c oi) ol) o1) o2)) =
  let k = get_key oi in
  if get_key o2 = get_key o1 && get_key o1 = k && get_key o1 = get_key ol && is_alpha_op o1 && is_alpha_op ol && is_alpha_op oi then 
    rc_inter_lca_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o1) (get_op_a o2) (get_op_a ol) (get_op_a oi)
  else if get_key o2 = get_key o1 && get_key o1 = k && get_key o1 = get_key ol && is_beta_op o1 && is_beta_op ol && is_beta_op oi then 
    rc_inter_lca_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o1) (get_op_b o2) (get_op_b ol) (get_op_b oi)
  else rc_inter_lca_ne l a b c o1 o2 ol oi

(*One op*)
///////////////
val one_op_ind_right_a (l a b:concrete_st_a) (o2 o2':op_a) 
  : Lemma (requires distinct_ops o2 o2' /\ 
                    eq_a (merge_a l a (do_a b o2)) (do_a (merge_a l a b) o2))
           (ensures eq_a (merge_a l a (do_a (do_a b o2') o2)) (do_a (merge_a l a (do_a b o2')) o2))

val one_op_ind_right_b (l a b:concrete_st_b) (o2 o2':op_b) 
  : Lemma (requires distinct_ops o2 o2' /\ 
                    eq_b (merge_b l a (do_b b o2)) (do_b (merge_b l a b) o2))
           (ensures eq_b (merge_b l a (do_b (do_b b o2') o2)) (do_b (merge_b l a (do_b b o2')) o2))
           
val one_op_ind_right_ne (l a b:concrete_st) (o2 o2':op_t)
  : Lemma (requires distinct_ops o2 o2' /\ 
                    ~ (get_key o2 = get_key o2' /\
                       (is_alpha_op o2 /\ is_alpha_op o2') /\ (is_beta_op o2 /\ is_beta_op o2')) /\
                    eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2))
          
let one_op_ind_right (l a b:concrete_st) (o2 o2':op_t)
   : Lemma (requires distinct_ops o2 o2' /\ eq (merge l a (do b o2)) (do (merge l a b) o2))
           (ensures eq (merge l a (do (do b o2') o2)) (do (merge l a (do b o2')) o2)) =
  let k = get_key o2' in
  if get_key o2 = k && is_alpha_op o2 && is_alpha_op o2' then
    one_op_ind_right_a (sel_a l k) (sel_a a k) (sel_a b k) (get_op_a o2) (get_op_a o2')
  else if get_key o2 = k && is_beta_op o2 && is_beta_op o2' then
    one_op_ind_right_b (sel_b l k) (sel_b a k) (sel_b b k) (get_op_b o2) (get_op_b o2')
  else one_op_ind_right_ne l a b o2 o2'

val one_op_ind_left_a (l a b:concrete_st_a) (o1 o1':op_a) 
  : Lemma (requires distinct_ops o1 o1' /\ 
                    eq_a (merge_a l (do_a a o1) b) (do_a (merge_a l a b) o1))
           (ensures eq_a (merge_a l (do_a (do_a a o1') o1) b) (do_a (merge_a l (do_a a o1') b) o1))

val one_op_ind_left_b (l a b:concrete_st_b) (o1 o1':op_b) 
  : Lemma (requires distinct_ops o1 o1' /\ 
                    eq_b (merge_b l (do_b a o1) b) (do_b (merge_b l a b) o1))
           (ensures eq_b (merge_b l (do_b (do_b a o1') o1) b) (do_b (merge_b l (do_b a o1') b) o1))
           
val one_op_ind_left_ne (l a b:concrete_st) (o1 o1':op_t)
  : Lemma (requires distinct_ops o1 o1' /\ 
                    ~ (get_key o1 = get_key o1' /\
                       (is_alpha_op o1 /\ is_alpha_op o1') /\ (is_beta_op o1 /\ is_beta_op o1')) /\
                    eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1))
          
let one_op_ind_left (l a b:concrete_st) (o1 o1':op_t)
   : Lemma (requires distinct_ops o1 o1' /\ 
                     eq (merge l (do a o1) b) (do (merge l a b) o1))
           (ensures eq (merge l (do (do a o1') o1) b) (do (merge l (do a o1') b) o1)) =
  let k = get_key o1' in
  if get_key o1 = k && is_alpha_op o1 && is_alpha_op o1' then
    one_op_ind_left_a (sel_a l k) (sel_a a k) (sel_a b k) (get_op_a o1) (get_op_a o1')
  else if get_key o1 = k && is_beta_op o1 && is_beta_op o1' then
    one_op_ind_left_b (sel_b l k) (sel_b a k) (sel_b b k) (get_op_b o1) (get_op_b o1')
  else one_op_ind_left_ne l a b o1 o1'

val one_op_ind_lca_a (l:concrete_st_a) (o2 o:op_a) 
  : Lemma (requires distinct_ops o2 o /\ 
                    eq_a (merge_a l l (do_a l o2)) (do_a l o2))
          (ensures eq_a (merge_a (do_a l o) (do_a l o) (do_a (do_a l o) o2)) (do_a (do_a l o) o2)) 

val one_op_ind_lca_b (l:concrete_st_b) (o2 o:op_b) 
  : Lemma (requires distinct_ops o2 o /\ 
                    eq_b (merge_b l l (do_b l o2)) (do_b l o2))
          (ensures eq_b (merge_b (do_b l o) (do_b l o) (do_b (do_b l o) o2)) (do_b (do_b l o) o2)) 
           
val one_op_ind_lca_ne (l:concrete_st) (o2 o:op_t)
  : Lemma (requires distinct_ops o2 o /\ 
                    ~ (get_key o2 = get_key o /\
                       (is_alpha_op o2 /\ is_alpha_op o) /\ (is_beta_op o2 /\ is_beta_op o)) /\
                    eq (merge l l (do l o2)) (do l o2))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o2)) (do (do l o) o2)) 
          
let one_op_ind_lca (l:concrete_st) (o2 o:op_t)
   : Lemma (requires distinct_ops o2 o /\ 
                     eq (merge l l (do l o2)) (do l o2))
          (ensures eq (merge (do l o) (do l o) (do (do l o) o2)) (do (do l o) o2)) =
  let k = get_key o in
  if get_key o2 = k && is_alpha_op o2 && is_alpha_op o then
    one_op_ind_lca_a (sel_a l k) (get_op_a o2) (get_op_a o)
  else if get_key o2 = k && is_beta_op o2 && is_beta_op o then
    one_op_ind_lca_b (sel_b l k) (get_op_b o2) (get_op_b o)
  else one_op_ind_lca_ne l o2 o

val one_op_base_a (o2:op_a)
  : Lemma (ensures eq_a (merge_a init_st_a init_st_a (do_a init_st_a o2)) (do_a init_st_a o2))

val one_op_base_b (o2:op_b)
  : Lemma (ensures eq_b (merge_b init_st_b init_st_b (do_b init_st_b o2)) (do_b init_st_b o2))

let one_op_base (o2:op_t) (t:key_t)
  : Lemma (ensures eq (merge (init_st t) (init_st t) (do (init_st t) o2)) (do (init_st t) o2)) =
  if is_alpha_op o2 then one_op_base_a (get_op_a o2)
  else one_op_base_b (get_op_b o2)

val one_op_inter_base_right_a (l a b c:concrete_st_a) (o2 ob ol:op_a) 
  : Lemma (requires Fst_then_snd? (rc_a ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a b ol) o2)) (do_a (do_a c ol) o2) /\
                    eq_a (merge_a l a (do_a b o2)) (do_a c o2) /\
                    eq_a (merge_a l (do_a a ol) (do_a b ob)) (do_a (do_a c ob) ol)) //***EXTRA***
          (ensures eq_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a (do_a b ob) ol) o2)) (do_a (do_a (do_a c ob) ol) o2)) 

val one_op_inter_base_right_b (l a b c:concrete_st_b) (o2 ob ol:op_b) 
  : Lemma (requires Fst_then_snd? (rc_b ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b b ol) o2)) (do_b (do_b c ol) o2) /\
                    eq_b (merge_b l a (do_b b o2)) (do_b c o2) /\
                    eq_b (merge_b l (do_b a ol) (do_b b ob)) (do_b (do_b c ob) ol)) //***EXTRA***
          (ensures eq_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b (do_b b ob) ol) o2)) (do_b (do_b (do_b c ob) ol) o2)) 

val one_op_inter_base_right_ne (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (get_key ol = get_key ob && get_key o2 = get_key ob /\
                       (is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol))) /\
                       (is_beta_op ob && is_beta_op ol && is_beta_op o2 && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)))) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          
let one_op_inter_base_right (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) =
  let k = get_key ob in
  if get_key ol = k && get_key o2 = k && is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then
    one_op_inter_base_right_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o2) (get_op_a ob) (get_op_a ol)
  else if get_key ol = k && get_key o2 = k && is_beta_op ob && is_beta_op ol && is_beta_op o2 && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then
    one_op_inter_base_right_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o2) (get_op_b ob) (get_op_b ol)
  else one_op_inter_base_right_ne l a b c o2 ob ol

val one_op_inter_base_left_a (l a b c:concrete_st_a) (o2 ob ol:op_a) 
  : Lemma (requires Fst_then_snd? (rc_a ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a b ol) o2)) (do_a (do_a c ol) o2) /\
                    //(Fst_then_snd? (rc_a ob o2) ==> eq_a (merge_a l (do_a a o2) (do_a b ob)) (do_a (merge_a l a (do_a b ob)) o2)) /\ //***EXTRA***
                    eq_a (merge_a l a (do_a b o2)) (do_a c o2) /\
                    eq_a(merge_a l (do_a a ob) (do_a b o2)) (do_a (do_a c ob) o2) /\ //EXTRA!! 
                    eq_a (merge_a l (do_a a ob) (do_a b ol)) (do_a (do_a c ob) ol)) //***EXTRA***
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a a ob) ol) (do_a (do_a b ol) o2)) (do_a (do_a (do_a c ob) ol) o2))

val one_op_inter_base_left_b (l a b c:concrete_st_b) (o2 ob ol:op_b) 
  : Lemma (requires Fst_then_snd? (rc_b ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b b ol) o2)) (do_b (do_b c ol) o2) /\
                    //(Fst_then_snd? (rc_b ob o2) ==> eq_b (merge_b l (do_b a o2) (do_b b ob)) (do_b (merge_b l a (do_b b ob)) o2)) /\ //***EXTRA***
                    eq_b (merge_b l a (do_b b o2)) (do_b c o2) /\
                    eq_b(merge_b l (do_b a ob) (do_b b o2)) (do_b (do_b c ob) o2) /\ //EXTRA!! 
                    eq_b (merge_b l (do_b a ob) (do_b b ol)) (do_b (do_b c ob) ol)) //***EXTRA***
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b a ob) ol) (do_b (do_b b ol) o2)) (do_b (do_b (do_b c ob) ol) o2))

val one_op_inter_base_left_ne (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (get_key ol = get_key ob && get_key o2 = get_key ob /\
                       (is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol))) /\
                       (is_beta_op ob && is_beta_op ol && is_beta_op o2 && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)))) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //***EXTRA***
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ //EXTRA!! 
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) 
          
let one_op_inter_base_left (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    (Fst_then_snd? (rc ob o2) ==> eq (merge l (do a o2) (do b ob)) (do (merge l a (do b ob)) o2)) /\ //***EXTRA***
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ob) (do b o2)) (do (do c ob) o2) /\ //EXTRA!! 
                    eq (merge l (do a ob) (do b ol)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2)) = 
  let k = get_key ob in
  if get_key ol = k && get_key o2 = k && is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then
    one_op_inter_base_left_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o2) (get_op_a ob) (get_op_a ol)
  else if get_key ol = k && get_key o2 = k && is_beta_op ob && is_beta_op ol && is_beta_op o2 && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then
    one_op_inter_base_left_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o2) (get_op_b ob) (get_op_b ol)
  else one_op_inter_base_left_ne l a b c o2 ob ol

val one_op_inter_right_a (l a b c:concrete_st_a) (o2 ob ol o:op_a) 
  : Lemma (requires Fst_then_snd? (rc_a ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc_a o ob)) \/ Fst_then_snd? (rc_a o ol)) /\
                    eq_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a (do_a b ob) ol) o2)) (do_a (do_a (do_a c ob) ol) o2))
          (ensures eq_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a (do_a (do_a b o) ob) ol) o2)) (do_a (do_a (do_a (do_a c o) ob) ol) o2))

val one_op_inter_right_b (l a b c:concrete_st_b) (o2 ob ol o:op_b) 
  : Lemma (requires Fst_then_snd? (rc_b ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc_b o ob)) \/ Fst_then_snd? (rc_b o ol)) /\
                    eq_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b (do_b b ob) ol) o2)) (do_b (do_b (do_b c ob) ol) o2))
          (ensures eq_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b (do_b (do_b b o) ob) ol) o2)) (do_b (do_b (do_b (do_b c o) ob) ol) o2))

val one_op_inter_right_ne (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ~ (get_key o = get_key ob && get_key o = get_key ol /\ get_key o = get_key o2 /\
                       (is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && is_alpha_op o && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol))) /\
                       (is_beta_op ob && is_beta_op ol && is_beta_op o2 && is_alpha_op o && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)))) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2))
          
let one_op_inter_right (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do a ol) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do c o) ob) ol) o2)) =
  let k = get_key o in
  if get_key ob = k && get_key ol = k && get_key o2 = k && is_alpha_op o && is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then
    one_op_inter_right_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o2) (get_op_a ob) (get_op_a ol) (get_op_a o)
  else if get_key ol = k && get_key o2 = k && is_beta_op ob && is_beta_op ol && is_beta_op o2 && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then
    one_op_inter_right_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o2) (get_op_b ob) (get_op_b ol) (get_op_b o)
  else one_op_inter_right_ne l a b c o2 ob ol o

val one_op_inter_left_a (l a b c:concrete_st_a) (o2 ob ol o:op_a) 
  : Lemma (requires Fst_then_snd? (rc_a ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc_a o ob)) \/ Fst_then_snd? (rc_a o ol)) /\
                    eq_a (merge_a (do_a l ol) (do_a (do_a a ob) ol) (do_a (do_a b ol) o2)) (do_a (do_a (do_a c ob) ol) o2))
          (ensures eq_a (merge_a (do_a l ol) (do_a (do_a (do_a a o) ob) ol) (do_a (do_a b ol) o2)) (do_a (do_a (do_a (do_a c o) ob) ol) o2))

val one_op_inter_left_b (l a b c:concrete_st_b) (o2 ob ol o:op_b) 
  : Lemma (requires Fst_then_snd? (rc_b ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc_b o ob)) \/ Fst_then_snd? (rc_b o ol)) /\
                    eq_b (merge_b (do_b l ol) (do_b (do_b a ob) ol) (do_b (do_b b ol) o2)) (do_b (do_b (do_b c ob) ol) o2))
          (ensures eq_b (merge_b (do_b l ol) (do_b (do_b (do_b a o) ob) ol) (do_b (do_b b ol) o2)) (do_b (do_b (do_b (do_b c o) ob) ol) o2))

val one_op_inter_left_ne (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    ~ (get_key o = get_key ob && get_key o = get_key ol /\ get_key o = get_key o2 /\
                       (is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && is_alpha_op o && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol))) /\
                       (is_beta_op ob && is_beta_op ol && is_beta_op o2 && is_alpha_op o && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)))) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2))
          
let one_op_inter_left (l a b c:concrete_st) (o2 ob ol o:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o ob /\ distinct_ops o ol /\ distinct_ops o ol /\ distinct_ops ob ol /\ distinct_ops ob o2 /\ distinct_ops o2 ol /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    (~ (Either? (rc o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ob) ol) (do (do b ol) o2)) (do (do (do c ob) ol) o2))
          (ensures eq (merge (do l ol) (do (do (do a o) ob) ol) (do (do b ol) o2)) (do (do (do (do c o) ob) ol) o2)) =
  let k = get_key o in
  if get_key ob = k && get_key ol = k && get_key o2 = k && is_alpha_op o && is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then
    one_op_inter_left_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o2) (get_op_a ob) (get_op_a ol) (get_op_a o)
  else if get_key ol = k && get_key o2 = k && is_beta_op ob && is_beta_op ol && is_beta_op o2 && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then
    one_op_inter_left_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o2) (get_op_b ob) (get_op_b ol) (get_op_b o)
  else one_op_inter_left_ne l a b c o2 ob ol o

val one_op_inter_lca_a (l a b c:concrete_st_a) (o2 ol oi o:op_a)
  : Lemma (requires Fst_then_snd? (rc_a o ol) /\ 
                    Fst_then_snd? (rc_a o oi) /\ 
                    eq_a (merge_a (do_a l oi) (do_a a oi) (do_a (do_a b oi) o2)) (do_a (do_a c oi) o2) /\
                    eq_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a b ol) o2)) (do_a (do_a c ol) o2))
          (ensures eq_a (merge_a (do_a (do_a l oi) ol) (do_a (do_a a oi) ol) (do_a (do_a (do_a b oi) ol) o2)) (do_a (do_a (do_a c oi) ol) o2))

val one_op_inter_lca_b (l a b c:concrete_st_b) (o2 ol oi o:op_b)
  : Lemma (requires Fst_then_snd? (rc_b o ol) /\ 
                    Fst_then_snd? (rc_b o oi) /\ 
                    eq_b (merge_b (do_b l oi) (do_b a oi) (do_b (do_b b oi) o2)) (do_b (do_b c oi) o2) /\
                    eq_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b b ol) o2)) (do_b (do_b c ol) o2))
          (ensures eq_b (merge_b (do_b (do_b l oi) ol) (do_b (do_b a oi) ol) (do_b (do_b (do_b b oi) ol) o2)) (do_b (do_b (do_b c oi) ol) o2))

val one_op_inter_lca_ne (l a b c:concrete_st) (o2 ol oi o:op_t)
  : Lemma (requires Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\ 
                    ~ (get_key ol = get_key oi /\ get_key o2 = get_key oi /\
                       (is_alpha_op oi /\ is_alpha_op ol /\ is_alpha_op o2 /\ is_alpha_op o /\ Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol)) /\ Fst_then_snd? (rc_a (get_op_a o) (get_op_a oi))) /\
                       (is_beta_op oi /\ is_beta_op ol /\ is_beta_op o2 /\ is_beta_op o /\ Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol)) /\ Fst_then_snd? (rc_b (get_op_a o) (get_op_a oi)))) /\
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) 
          
let one_op_inter_lca (l a b c:concrete_st) (o2 ol oi o:op_t)
  : Lemma (requires Fst_then_snd? (rc o ol) /\ 
                    Fst_then_snd? (rc o oi) /\ 
                    eq (merge (do l oi) (do a oi) (do (do b oi) o2)) (do (do c oi) o2) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2))
          (ensures eq (merge (do (do l oi) ol) (do (do a oi) ol) (do (do (do b oi) ol) o2)) (do (do (do c oi) ol) o2)) =
  let k = get_key oi in
  if get_key ol = k && get_key o2 = k && is_alpha_op oi && is_alpha_op ol && is_alpha_op o2 && is_alpha_op o && Fst_then_snd? (rc_a (get_op_a o) (get_op_a ol)) && Fst_then_snd? (rc_a (get_op_a o) (get_op_a oi)) then
    one_op_inter_lca_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o2) (get_op_a ol) (get_op_a oi) (get_op_a o)
  else if get_key ol = k && get_key o2 = k && is_beta_op oi && is_beta_op ol && is_beta_op o2 && is_beta_op o && Fst_then_snd? (rc_b (get_op_b o) (get_op_b ol)) && Fst_then_snd? (rc_b (get_op_b o) (get_op_b oi)) then
    one_op_inter_lca_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o2) (get_op_b ol) (get_op_b oi) (get_op_b o)
  else one_op_inter_lca_ne l a b c o2 ol oi o

(*Zero op *)
///////////////
// because we proved that e_i^l rcp eb is not possible.
//e_i^l vis eb is not possible
// so either eb rcp e_i^l or eb rct e_i^l is possible
val one_op_inter_right_a (l a b c:concrete_st_a) (o2 ob ol:op_a) 
  : Lemma (requires Fst_then_snd? (rc_a ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a b ol) o2)) (do_a (do_a c ol) o2) /\
                    eq_a (merge_a l a (do_a b o2)) (do_a c o2) /\
                    eq_a (merge_a l (do_a a ol) (do_a b ob)) (do_a (do_a c ob) ol)) //***EXTRA***
          (ensures eq_a (merge_a (do_a l ol) (do_a a ol) (do_a (do_a (do_a b ob) ol) o2)) (do_a (do_a (do_a c ob) ol) o2)) 

val one_op_inter_right_b (l a b c:concrete_st_b) (o2 ob ol:op_b) 
  : Lemma (requires Fst_then_snd? (rc_b ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b b ol) o2)) (do_b (do_b c ol) o2) /\
                    eq_b (merge_b l a (do_b b o2)) (do_b c o2) /\
                    eq_b (merge_b l (do_b a ol) (do_b b ob)) (do_b (do_b c ob) ol)) //***EXTRA***
          (ensures eq_b (merge_b (do_b l ol) (do_b a ol) (do_b (do_b (do_b b ob) ol) o2)) (do_b (do_b (do_b c ob) ol) o2)) 

val one_op_inter_right_ne (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    ~ (get_key ol = get_key ob && get_key o2 = get_key ob /\
                       (is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol))) /\
                       (is_beta_op ob && is_beta_op ol && is_beta_op o2 && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)))) /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2))
          
let one_op_inter_right (l a b c:concrete_st) (o2 ob ol:op_t) 
  : Lemma (requires Fst_then_snd? (rc ob ol) /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do a ol) (do (do b ol) o2)) (do (do c ol) o2) /\
                    eq (merge l a (do b o2)) (do c o2) /\
                    eq (merge l (do a ol) (do b ob)) (do (do c ob) ol)) //***EXTRA***
          (ensures eq (merge (do l ol) (do a ol) (do (do (do b ob) ol) o2)) (do (do (do c ob) ol) o2)) =
  let k = get_key ob in
  if get_key ol = k && get_key o2 = k && is_alpha_op ob && is_alpha_op ol && is_alpha_op o2 && Fst_then_snd? (rc_a (get_op_a ob) (get_op_a ol)) then
    one_op_inter_base_right_a (sel_a l k) (sel_a a k) (sel_a b k) (sel_a c k) (get_op_a o2) (get_op_a ob) (get_op_a ol)
  else if get_key ol = k && get_key o2 = k && is_beta_op ob && is_beta_op ol && is_beta_op o2 && Fst_then_snd? (rc_b (get_op_b ob) (get_op_b ol)) then
    one_op_inter_base_right_b (sel_b l k) (sel_b a k) (sel_b b k) (sel_b c k) (get_op_b o2) (get_op_b ob) (get_op_b ol)
  else one_op_inter_base_right_ne l a b c o2 ob ol
  












(*module Polymorphic_gmap

module S = Set_extended
module M = Map_extended
open FStar.Seq

#set-options "--query_stats"
//key type
type key_t =
  |Ctr_t
  |Gset_t

// concrete state of values
noeq type concrete_st_v = 
  |Ctr : int -> concrete_st_v
  |Gset : S.t nat -> concrete_st_v

let eq_key_t (s:M.t (string & key_t) concrete_st_v) =
  (forall sk. M.contains s sk ==> (let v = M.sel s sk in
         ((Ctr? v ==> snd sk == Ctr_t) /\ (Gset? v ==> snd sk = Gset_t))))

//concrete state
let concrete_st = s:M.t (string & key_t) concrete_st_v {eq_key_t s}

let init_st_v (t:key_t) : (s:concrete_st_v{(t == Ctr_t <==> Ctr? s) /\ (t == Gset_t <==> Gset? s)}) =
  match t with
  |Ctr_t -> Ctr 0
  |Gset_t -> Gset S.empty

let init_st (t:key_t) : concrete_st = M.const_on S.empty (init_st_v t)

let sel (s:concrete_st) (t:key_t) k  =
    if M.contains s (k,t) then M.sel s (k,t) else (init_st_v t)

let eq_ctr (a:concrete_st_v{Ctr? a}) (b:concrete_st_v{Ctr? b}) = 
  let Ctr c1 = a in 
  let Ctr c2 = b in
  c1 = c2

let eq_gset (a:concrete_st_v{Gset? a}) (b:concrete_st_v{Gset? b}) = 
  let Gset s1 = a in 
  let Gset s2 = b in
  S.equal s1 s2

let eq_v (a:concrete_st_v) (b:concrete_st_v) : Type0 = //{(Ctr? a ==> Ctr? b) /\ (Gset? a ==> Gset? b)}) : Type0 =
  match a,b with
  |Ctr x,Ctr y -> x = y
  |Gset x, Gset y -> S.equal x y
  |_ -> False

// equivalence relation
let eq (a b:concrete_st) =
  (forall k t. M.contains a (k,t) = M.contains b (k,t)) /\
  (forall k t. M.contains a (k,t) ==> eq_v (sel a t k) (sel b t k))

let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b) = ()

type app_op_v : eqtype =
  |Inc 
  |Add : nat -> app_op_v

type op_v = pos (*timestamp*) & (nat (*replica ID*) & app_op_v)

//operation type
type app_op_t:eqtype =
  |Set : string (* key *) -> app_op_v (* value *) -> app_op_t

let do_v (s:concrete_st_v) (o:op_v) : concrete_st_v =
  match snd (snd o) with
  |Inc -> begin match s with
         |Ctr c -> Ctr (c+1)
         |_ -> s
         end
  |Add v -> begin match s with
           |Gset s -> Gset (S.add v s)
           |_ -> s
           end

type op_t = pos (*timestamp*) & (nat (*replica ID*) & app_op_t)

let get_rid (_,(rid,_)) = rid

let distinct_ops (op1 op2:op_t) = fst op1 =!= fst op2

let get_op_v (o:op_t) : op_v =
  match o with
  |(ts,(rid,(Set k op))) -> (ts,(rid,op))

let do_pre (s:concrete_st) (o:op_t) =
  match o with
  |(_,(_,Set k opv)) -> begin match opv with
                       |Inc -> (forall t. M.contains s (k,t) ==> t == Ctr_t)
                       |Add _ -> (forall t. M.contains s (k,t) ==> t == Gset_t)
                       end

let do (s:concrete_st) (o:op_t(*{do_pre s o}*)) : concrete_st =
  match o with
    |_,(_,Set k Inc) -> (*if M.contains s (k,Ctr_t) then*) M.upd s (k,Ctr_t) (do_v (sel s Ctr_t k) (get_op_v o))
                       //else M.upd s (k,Ctr_t) (Ctr 1)
    |_,(_,Set k (Add e)) -> (*if M.contains s (k,Gset_t) then*) M.upd s (k,Gset_t) (do_v (sel s Gset_t k) (get_op_v o))
                           //else M.upd s (k,Gset_t) (Gset (S.add e S.empty))

type rc_res =
  |Fst_then_snd //o1 -> o2
  |Snd_then_fst //o2 -> o1
  |Either
  
//conflict resolution
let rc (o1:op_t) (o2:op_t(*{distinct_ops o1 o2}*)) : rc_res = Either

let merge_ctr (l a:concrete_st_v) (b:concrete_st_v{Ctr? l /\ Ctr? a /\ Ctr? b}) : concrete_st_v =
  let Ctr c1 = l in let Ctr c2 = a in let Ctr c3 = b in
  Ctr (c2 + c3 - c1)

let merge_gset (l a:concrete_st_v) (b:concrete_st_v{Gset? l /\ Gset? a /\ Gset? b}) : concrete_st_v =
  let Gset s1 = l in let Gset s2 = a in let Gset s3 = b in
  Gset (S.union s1 (S.union s2 s3))

// concrete merge operation
let merge (l a b:concrete_st) : concrete_st =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (0, false) in
  M.iter_upd (fun (k,t) v -> if Ctr_t? t then merge_ctr (sel l t k) (sel a t k) (sel b t k) 
                          else merge_gset (sel l t k) (sel a t k) (sel b t k)) u

let commutes_with (o1 o2:op_t) =
  forall s. eq (do (do s o1) o2) (do (do s o2) o1)

type log = seq op_t

// applying a log of operations to a concrete state
let rec apply_log (x:concrete_st) (l:log) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |_ -> apply_log (do x (head l)) (tail l)  


/////////////////////////////////////////////////////////////////////////////

#set-options "--z3rlimit 300 --ifuel 3"
let rc_non_comm1 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures commutes_with o1 o2 ==> Either? (rc o1 o2)) = ()

let rc_non_comm2 (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) ==> commutes_with o1 o2) = ()

let rc_non_comm (o1 o2:op_t)
  : Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc o1 o2) <==> commutes_with o1 o2) = 
  rc_non_comm1 o1 o2;
  rc_non_comm2 o1 o2

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

////////////////////////////////////////////////////////////////////////////

let merge_comm (l a b:concrete_st)
  : Lemma (ensures (eq (merge l a b) (merge l b a))) = ()
                       
let merge_idem (s:concrete_st)
  : Lemma (ensures eq (merge s s s) s) = ()

(* 2 op Comm  *)
///////////////////

#set-options "--z3rlimit 300 --ifuel 3"
let comm_ind_right (l a b c:concrete_st) (o1 o2 o2':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o2' o1) ==> (eq (merge l (do a o1) (do b o2')) (do (merge l a (do b o2')) o1))) /\
                   // ~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o1 o2')) )
                    //~ (exists o3 b'. eq (do (do b o2') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (do (merge l a (do b o2')) o2) o1)) =   ()

#set-options "--z3rlimit 400 --ifuel 4"
let comm_ind_left (l a b c:concrete_st) (o1 o2 o1':op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    eq (merge l (do a o1) (do b o2)) (do (do (merge l a b) o2) o1) /\
                    (Fst_then_snd? (rc o1' o2) ==> (eq (merge l (do a o1') (do b o2)) (do (merge l (do a o1') b) o2))) /\
                    //~ (exists o3 a'. eq (do a o1) (do a' o3) /\ distinct_ops o2 o3 /\ Fst_then_snd? (rc o2 o3)) /\
                    ~ (Fst_then_snd? (rc o2 o1')) )
                    //~ (exists o3 b'. eq (do (do b o1') o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)) /\
                    //~ (exists o3 b'. eq (do b o2) (do b' o3) /\ distinct_ops o1 o3 /\ Fst_then_snd? (rc o1 o3)))                    
          (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (do (merge l (do a o1') b) o2) o1)) = ()

let comm_ind_lca (l:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    eq (merge l (do l o1) (do l o2)) (do (do l o2) o1))
          (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (do (do l ol) o2) o1)) = ()

let comm_base (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge (init_st Ctr_t) (do (init_st Ctr_t) o1) (do (init_st Ctr_t) o2)) (do (do (init_st Ctr_t) o1) o2)) = ()

let comm_base1 (o1 o2:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ distinct_ops o1 o2)
          (ensures eq (merge (init_st Gset_t) (do (init_st Gset_t) o1) (do (init_st Gset_t) o2)) (do (do (init_st Gset_t) o1) o2)) = ()
          
let comm_inter_base_right (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do a o1) (do (do b ob) o2)) (do (do (merge l a (do b ob)) o1) o2) /\ //comes from comm_ind_right
                    eq (merge (do l ol) (do a ol) (do (do b ob) ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_base_left (l a b c:concrete_st) (o1 o2 ob ol:op_t) 
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2) /\ 
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2) /\
                    eq (merge l (do (do a ob) o1) (do b o2)) (do (do (merge l (do a ob) b) o1) o2) /\ //comes from comm_ind_left
                    eq (merge (do l ol) (do (do a ob) ol) (do b ol)) (do (do c ob) ol)) //comes from intermediate_base_zero_op
          (ensures eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2)) = ()

let comm_inter_right (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob) ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob) ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let comm_inter_left (l a b c:concrete_st) (o1 o2 ob ol o:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ Fst_then_snd? (rc ob ol) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol (*o,ol must be concurrent*) /\
                    //Either? (rc o ol) /\ 
                    ((~ (commutes_with o ob)) \/ Fst_then_snd? (rc o ol)) /\
                    eq (merge (do l ol) (do (do (do a ob) ol) o1) (do (do b ol) o2)) (do (do (do (do c ob) ol) o1) o2))
          (ensures eq (merge (do l ol) (do (do (do (do a o) ob) ol) o1) (do (do b ol) o2)) (do (do (do (do (do c o) ob) ol) o1) o2)) = ()

let comm_inter_lca (l a b c:concrete_st) (o1 o2 ol:op_t)
  : Lemma (requires Either? (rc o1 o2) /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops ol o2 /\
                    (exists o'. Fst_then_snd? (rc o' ol)) /\
                    eq (merge l (do a o1) (do b o2)) (do (do c o1) o2))
          (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (do (do c ol) o1) o2)) = ()
*)
