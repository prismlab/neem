module Json1

open FStar.Seq
module M = Dependent_map
module S = Set_extended
open Library

type kt : eqtype =
  |Alpha_t : string -> kt
  |Beta_t : string -> kt

type log = seq (pos & (nat & eqtype))

class json (st_a st_b:Type0) (app_op_a app_op_b:eqtype) = {   
  init_st_a : st_a;
  init_st_b : st_b;
  
  eq_a : st_a -> st_a -> Type0;
  eq_b : st_b -> st_b -> Type0;

  lem_eq_a : a:st_a -> b:st_a ->
    Lemma (ensures eq_a a b <==> a == b);
          //[SMTPat (eq_a a b)];

  lem_eq_b : a:st_b -> b:st_b ->
    Lemma (ensures eq_b a b <==> a == b);
          //[SMTPat (eq_b a b)];
          
  rc_a : (pos & (nat & app_op_a)) -> (pos & (nat & app_op_a)) -> rc_res;
  rc_b : (pos & (nat & app_op_b)) -> (pos & (nat & app_op_b)) -> rc_res;
  
  do_a : st_a -> (pos & (nat & app_op_a)) -> st_a;
  do_b : st_b -> (pos & (nat & app_op_b)) -> st_b;
  
  merge_a : st_a -> st_a -> st_a -> st_a;
  merge_b : st_b -> st_b -> st_b -> st_b
}

val vt : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> {|json st_a st_b o_a o_b|} -> (c:kt) -> Type0
let vt #st_a #st_b #o_a #o_b (c:kt) =
  match c with
  |Alpha_t _ -> st_a
  |Beta_t _ -> st_b

type st #st_a #st_b #o_a #o_b #m = M.t kt (vt #st_a #st_b #o_a #o_b #m)

val init_st_v : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> {|json st_a st_b o_a o_b|} -> k:kt -> vt #st_a #st_b #o_a #o_b k
let init_st_v #st_a #st_b #o_a #o_b #m (k:kt) : vt k =
  match k with
  |Alpha_t _ -> m.init_st_a
  |Beta_t _ -> m.init_st_b

val init_st : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> k:kt -> st #st_a #st_b #o_a #o_b #m
let init_st (k:kt) : st = M.const_on S.empty (fun k -> init_st_v k)

val sel : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> s:st #st_a #st_b #o_a #o_b #m -> k:kt -> vt #st_a #st_b #o_a #o_b k
let sel #st_a #st_b #o_a #o_b #m (s:st) (k:kt) =
  match k with
  |Alpha_t _ -> if M.contains s k then M.sel s k else m.init_st_a
  |Beta_t _ -> if M.contains s k then M.sel s k else m.init_st_b

val eq : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> a:st #st_a #st_b #o_a #o_b #m -> b:st #st_a #st_b #o_a #o_b #m -> Type0
let eq #st_a #st_b #o_a #o_b #m (a b:st) =
  //M.equal a b
  //(forall k. M.contains a k = M.contains b k /\ sel a k == sel b k)
  (forall k. M.contains a (Alpha_t k) = M.contains b (Alpha_t k) /\ 
        M.contains a (Beta_t k) = M.contains b (Beta_t k) /\
        m.eq_a (sel a (Alpha_t k)) (sel b (Alpha_t k)) /\
        m.eq_b (sel a (Beta_t k)) (sel b (Beta_t k)))

type app_op_v (#app_op_a:eqtype) (#app_op_b:eqtype) : eqtype =
  |Alpha_op : app_op_a -> app_op_v #app_op_a #app_op_b
  |Beta_op : app_op_b -> app_op_v #app_op_a #app_op_b

type app_op (#o_a:eqtype) (#o_b:eqtype) : eqtype =
  |Set : string (* key *) -> app_op_v #o_a #o_b(* value op *) -> app_op #o_a #o_b
  
type op (#o_a #o_b:eqtype) = pos (*timestamp*) & (nat (*replica ID*) & app_op #o_a #o_b)
type op_a (#o_a:eqtype) = pos (*timestamp*) & (nat (*replica ID*) & o_a)
type op_b (#o_b:eqtype) = pos (*timestamp*) & (nat (*replica ID*) & o_b)

let distinct_ops (#o:eqtype) (op1 op2:(pos & (nat & o))) = fst op1 =!= fst op2

//val get_rid : #o:eqtype -> pos -> nat -> o -> nat
//let get_rid (_,(rid,_)) = rid

let is_alpha_op (o:op) =
  match snd (snd o) with
  |Set _ (Alpha_op _) -> true
  |_ -> false

let is_beta_op (o:op) =
  match snd (snd o) with
  |Set _ (Beta_op _) -> true
  |_ -> false

let get_key (_,(_,Set k _)) = k

let get_op_a (o:op{is_alpha_op o}) : op_a =
  match o with
  |ts, (rid, Set _ (Alpha_op op)) -> (ts,(rid,op))

let get_op_b (o:op{is_beta_op o}) : op_b =
  match o with
  |ts, (rid, Set _ (Beta_op op)) -> (ts,(rid,op))
  
val do : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> s:st #st_a #st_b #o_a #o_b #m -> o:op #o_a #o_b -> st #st_a #st_b #o_a #o_b #m

let do #st_a #st_b #o_a #o_b #m (s:st) (o:op) 
  : (r:st{(is_alpha_op o ==> (forall k. M.contains r k <==> M.contains s k \/ k = Alpha_t (get_key o))) /\
                   (is_beta_op o ==> (forall k. M.contains r k <==> M.contains s k \/ k = Beta_t (get_key o)))}) =
  match snd (snd o) with
  |Set k (Alpha_op _) -> let v = sel s (Alpha_t k) in M.upd s (Alpha_t k) (m.do_a v (get_op_a o))
  |Set k (Beta_op _) -> let v = sel s (Beta_t k) in M.upd s (Beta_t k) (m.do_b v (get_op_b o))

val rc : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> o1:op #o_a #o_b -> o2:op #o_a #o_b -> rc_res
let rc #st_a #st_b #o_a #o_b #m (o1 o2:op) : rc_res = 
  match snd (snd o1), snd (snd o2) with
  |Set k1 (Alpha_op _), Set k2 (Alpha_op _) -> if k1 = k2 then m.rc_a (get_op_a o1) (get_op_a o2) else Either
  |Set k1 (Beta_op _), Set k2 (Beta_op _) -> if k1 = k2 then m.rc_b (get_op_b o1) (get_op_b o2) else Either
  |_ -> Either

val compose_values : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> k:kt -> l:st #st_a #st_b #o_a #o_b #m -> a:st #st_a #st_b #o_a #o_b #m -> b:st #st_a #st_b #o_a #o_b #m -> vt #st_a #st_b #o_a #o_b k
let compose_values #st_a #st_b #o_a #o_b #m (k:kt) (l a b:st) : vt #st_a #st_b #o_a #o_b k =
  if Alpha_t? k then 
    m.merge_a (sel l k) (sel a k) (sel b k)
  else m.merge_b (sel l k) (sel a k) (sel b k)

val merge : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> l:st #st_a #st_b #o_a #o_b #m -> a:st #st_a #st_b #o_a #o_b #m -> b:st #st_a #st_b #o_a #o_b #m -> st #st_a #st_b #o_a #o_b #m
let merge #st_a #st_b #o_a #o_b #m (l a b:st) =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (fun k -> init_st #st_a #st_b #o_a #o_b #m k) in
  M.map (fun k _ -> compose_values k l a b) u
  
val apply_log_a : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> {|json st_a st_b o_a o_b|} -> s:st_a -> l:seq (pos & (nat & o_a)) -> Tot st_a
let rec apply_log_a #st_a #st_b #o_a #o_b #m (s:st_a) (l:seq (pos & (nat & o_a))) : Tot st_a (decreases length l) =
  match length l with
  |0 -> s
  |_ -> apply_log_a #st_a #st_b #o_a #o_b #m (m.do_a s (head l)) (tail l) 

val apply_log_b : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> {|json st_a st_b o_a o_b|} -> s:st_b -> l:seq (pos & (nat & o_b)) -> Tot st_b
let rec apply_log_b #st_a #st_b #o_a #o_b #m (s:st_b) (l:seq (pos & (nat & o_b))) : Tot st_b (decreases length l) =
  match length l with
  |0 -> s
  |_ -> apply_log_b #st_a #st_b #o_a #o_b #m (m.do_b s (head l)) (tail l) 

val apply_log : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> s:st #st_a #st_b #o_a #o_b #m -> l:seq (op #o_a #o_b) -> Tot (st #st_a #st_b #o_a #o_b #m)

let rec apply_log #st_a #st_b #o_a #o_b #m s l : Tot st (decreases length l) =
  match length l with
  |0 -> s
  |_ -> apply_log (do s (head l)) (tail l) 

class cond (st_a st_b:Type0) (o_a o_b:eqtype) (m:json st_a st_b o_a o_b) = {
  rc_non_comm : o1:op -> o2:op ->
    Lemma (requires distinct_ops o1 o2)
          (ensures Either? (rc #st_a #st_b #o_a #o_b #m o1 o2) <==> (forall s. eq (do #st_a #st_b #o_a #o_b #m (do s o1) o2) (do (do s o2) o1)));

  no_rc_chain : o1:op -> o2:op -> o3:op ->
    Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (rc #st_a #st_b #o_a #o_b #m o1 o2) /\ Fst_then_snd? (rc #st_a #st_b #o_a #o_b #m o2 o3)));

  cond_comm_base : s:st -> o1:op -> o2:op -> o3:op ->
    Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ distinct_ops o1 o3 /\
                    Fst_then_snd? (rc #st_a #st_b #o_a #o_b #m o1 o2) /\ ~ (Either? (rc #st_a #st_b #o_a #o_b #m o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do #st_a #st_b #o_a #o_b #m (do s o2) o1) o3));

  cond_comm_ind : s:st -> o1:op -> o2:op -> o3:op -> o:op -> l:seq op ->
    Lemma (requires distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3 /\ 
                    Fst_then_snd? (rc #st_a #st_b #o_a #o_b #m o1 o2) /\ ~ (Either? (rc #st_a #st_b #o_a #o_b #m o2 o3)) /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do #st_a #st_b #o_a #o_b #m (apply_log (do (do s o2) o1) l) o) o3))        
}

val testa : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> a:st_a -> b:st_a ->
  Lemma (ensures (m.eq_a a b <==> a == b)) 
        [SMTPat (m.eq_a a b)]
let testa #st_a #st_b #o_a #o_b #m a b = 
  m.lem_eq_a a b

val testb : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> a:st_b -> b:st_b ->
  Lemma (ensures (m.eq_b a b <==> a == b)) 
        [SMTPat (m.eq_b a b)]
let testb #st_a #st_b #o_a #o_b #m a b = 
  m.lem_eq_b a b
  
class vc (st_a st_b:Type0) (o_a o_b:eqtype) (m:json st_a st_b o_a o_b) = {
 merge_comm_a : l:st_a -> a:st_a -> b:st_a ->
  Lemma (ensures m.eq_a (m.merge_a l a b) (m.merge_a l b a));
        //[SMTPat (m.merge_a l a b)];

 merge_comm_b : l:st_b -> a:st_b -> b:st_b ->
  Lemma (ensures m.eq_b (m.merge_b l a b) (m.merge_b l b a));
        //[SMTPat (m.merge_b l a b)]

 merge_idem_a : s:st_a ->
  Lemma (ensures m.eq_a (m.merge_a s s s) s);
        //[SMTPat (m.merge_a l a b)];

 merge_idem_b : s:st_b ->
  Lemma (ensures m.eq_b (m.merge_b s s s) s);
        //[SMTPat (m.merge_b l a b)]

 base_2op_a : o1:op_a -> o2:op_a ->
  Lemma (requires (Fst_then_snd? (rc_a #st_a #st_b #o_a #o_b #m o2 o1) \/ Either? (rc_a #st_a #st_b #o_a #o_b #m o2 o1)) /\ get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2)
        (ensures m.eq_a (m.merge_a m.init_st_a (m.do_a m.init_st_a o1) (m.do_a m.init_st_a o2)) 
                      (m.do_a (m.merge_a m.init_st_a m.init_st_a (m.do_a m.init_st_a o2)) o1));

 base_2op_b : o1:op_b -> o2:op_b ->
  Lemma (requires (Fst_then_snd? (rc_b #st_a #st_b #o_a #o_b #m o2 o1) \/ Either? (rc_b #st_a #st_b #o_a #o_b #m o2 o1)) /\ get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2)
        (ensures m.eq_b (m.merge_b m.init_st_b (m.do_b m.init_st_b o1) (m.do_b m.init_st_b o2)) 
                      (m.do_b (m.merge_b m.init_st_b m.init_st_b (m.do_b m.init_st_b o2)) o1));

 base_2op' : o1:op -> o2:op -> t:kt ->
   Lemma (requires Either? (rc #st_a #st_b #o_a #o_b #m o2 o1) /\ get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2 /\
                    ~ (get_key o1 = get_key o2 /\ 
                       is_alpha_op o1 /\ is_alpha_op o2 /\ (Fst_then_snd? (m.rc_a (get_op_a o2) (get_op_a o1)) || Either? (m.rc_a (get_op_a o2) (get_op_a o1))) /\
                       is_beta_op o1 /\ is_beta_op o2 /\ (Fst_then_snd? (m.rc_b (get_op_b o2) (get_op_b o1)) || Either? (m.rc_b (get_op_b o2) (get_op_b o1)))))                
          (ensures eq (merge (init_st t) (do (init_st t) o1) (do (init_st t) o2)) 
                      (do #st_a #st_b #o_a #o_b #m (merge (init_st t) (init_st t) (do (init_st t) o2)) o1));

 ind_right_2op_a : l:st_a -> a:st_a -> b:st_a -> o1:op_a -> o2:op_a -> o2':op_a ->
  Lemma (requires Fst_then_snd? (m.rc_a o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    m.eq_a (m.merge_a l (m.do_a a o1) (m.do_a b o2)) (m.do_a (m.merge_a l a (m.do_a b o2)) o1))
         (ensures m.eq_a (m.merge_a l (m.do_a a o1) (m.do_a (m.do_a b o2') o2)) (m.do_a (m.merge_a l a (m.do_a (m.do_a b o2') o2)) o1));

 ind_right_2op_b : l:st_b -> a:st_b -> b:st_b -> o1:op_b -> o2:op_b -> o2':op_b ->
   Lemma (requires Fst_then_snd? (m.rc_b o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    m.eq_b (m.merge_b l (m.do_b a o1) (m.do_b b o2)) (m.do_b (m.merge_b l a (m.do_b b o2)) o1))
         (ensures m.eq_b (m.merge_b l (m.do_b a o1) (m.do_b (m.do_b b o2') o2)) (m.do_b (m.merge_b l a (m.do_b (m.do_b b o2') o2)) o1))
}

#set-options "--z3rlimit 100 --ifuel 3"
val comma : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> #v:(vc st_a st_b o_a o_b m) -> l:st_a -> a:st_a -> b:st_a ->
  Lemma (ensures (m.eq_a (m.merge_a l a b) (m.merge_a l b a))) 
        [SMTPat (m.merge_a l a b)]        
let comma #st_a #st_b #o_a #o_b #m #v l a b = 
  v.merge_comm_a l a b

val commb : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> #v:(vc st_a st_b o_a o_b m) -> l:st_b -> a:st_b -> b:st_b ->
  Lemma (ensures (m.eq_b (m.merge_b l a b) (m.merge_b l b a))) 
        [SMTPat (m.merge_b l a b)]       
let commb #st_a #st_b #o_a #o_b #m #v l a b = 
  v.merge_comm_b l a b

val idema : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> #v:(vc st_a st_b o_a o_b m) -> s:st_a ->
  Lemma (ensures (m.eq_a (m.merge_a s s s) s)) 
        [SMTPat (m.merge_a s s s)]        
let idema #st_a #st_b #o_a #o_b #m #v s = 
  v.merge_idem_a s

val idemb : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> #v:(vc st_a st_b o_a o_b m) -> s:st_b ->
  Lemma (ensures (m.eq_b (m.merge_b s s s) s)) 
        [SMTPat (m.merge_b s s s)]        
let idemb #st_a #st_b #o_a #o_b #m #v s = 
  v.merge_idem_b s
  
val merge_comm : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> #v:(vc st_a st_b o_a o_b m) -> l:st #st_a #st_b #o_a #o_b #m -> a:st #st_a #st_b #o_a #o_b #m -> b:st #st_a #st_b #o_a #o_b #m ->
  Lemma (ensures (eq (merge l a b) (merge l b a)))
let merge_comm #st_a #st_b #o_a #o_b #m #v l a b 
  :  Lemma (ensures (eq (merge l a b) (merge l b a))) = ()

val merge_idem : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> #v:(vc st_a st_b o_a o_b m) -> s:st #st_a #st_b #o_a #o_b #m -> 
  Lemma (ensures (eq (merge s s s) s))
let merge_idem #st_a #st_b #o_a #o_b #m #v s
  :  Lemma (ensures (eq (merge s s s) s)) = ()

val base_2op : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> #v:(vc st_a st_b o_a o_b m) -> o1:op -> o2:op -> t:kt -> 
  Lemma (requires (Fst_then_snd? (rc #st_a #st_b #o_a #o_b #m o2 o1) \/ Either? (rc #st_a #st_b #o_a #o_b #m o2 o1)) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2)
          (ensures eq (merge (init_st t) (do (init_st t) o1) (do (init_st t) o2)) 
                      (do #st_a #st_b #o_a #o_b #m (merge (init_st t) (init_st t) (do (init_st t) o2)) o1))                     
let base_2op #st_a #st_b #o_a #o_b #m #v o1 o2 t =
  if get_key o1 = get_key o2 && is_alpha_op o1 && is_alpha_op o2 then
    v.base_2op_a (get_op_a o1) (get_op_a o2) 
  else if get_key o1 = get_key o2 && is_beta_op o1 && is_beta_op o2 then
    v.base_2op_b (get_op_b o1) (get_op_b o2) 
  else if Either? (rc #st_a #st_b #o_a #o_b #m o2 o1) then v.base_2op' o1 o2 t
  else ()

val ind_right_2op : #st_a:Type0 -> #st_b:Type0 -> #o_a:eqtype -> #o_b:eqtype -> #m:(json st_a st_b o_a o_b) -> #v:(vc st_a st_b o_a o_b m) -> l:st #st_a #st_b #o_a #o_b #m -> a:st #st_a #st_b #o_a #o_b #m -> b:st #st_a #st_b #o_a #o_b #m -> o1:op -> o2:op -> o2':op -> 
  Lemma (requires Fst_then_snd? (rc #st_a #st_b #o_a #o_b #m o2 o1) /\ get_rid o1 <> get_rid o2 /\
                    distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1))
          (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l a (do (do b o2') o2)) o1))
          
let ind_right_2op #st_a #st_b #o_a #o_b #m #v l a b o1 o2 o2' =
  let k = get_key o2' in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op o2' && Fst_then_snd? (m.rc_a (get_op_a o2) (get_op_a o1)) then
      v.ind_right_2op_a (sel l ka) (sel a ka) (sel b ka) (get_op_a o1) (get_op_a o2) (get_op_a o2')
  else if get_key o1 = k && get_key o2 = k && is_beta_op o1 && is_beta_op o2 && is_beta_op o2' && Fst_then_snd? (m.rc_b (get_op_b o2) (get_op_b o1)) then
      v.ind_right_2op_b (sel l kb) (sel a kb) (sel b kb) (get_op_b o1) (get_op_b o2) (get_op_b o2')
  else ()
  
(*class vc (st:Type0) (app_op:eqtype) (m:mrdt st app_op) = {
  merge_comm : l:st -> a:st -> b:st ->
    Lemma (ensures (m.eq (m.merge l a b) (m.merge l b a)));

  merge_idem : s:st ->
    Lemma (ensures (m.eq (m.merge s s s) s));

  base_2op : o1:op -> o2:op ->
    Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2)
          (ensures m.eq (m.merge m.init_st (m.do m.init_st o1) (m.do m.init_st o2)) (m.do (m.merge m.init_st m.init_st (m.do m.init_st o2)) o1));

  ind_lca_2op : l:st -> o1:op -> o2:op -> ol:op ->
  Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\
                  get_rid o1 <> get_rid o2 /\
                  distinct_ops o1 o2 /\
                  distinct_ops o1 ol /\
                  distinct_ops o2 ol /\
                  m.eq (m.merge l (m.do l o1) (m.do l o2)) (m.do (m.merge l l (m.do l o2)) o1))
        (ensures m.eq (m.merge (m.do l ol) (m.do (m.do l ol) o1) (m.do (m.do l ol) o2)) (m.do (m.merge (m.do l ol) (m.do l ol) (m.do (m.do l ol) o2)) o1));

  inter_right_base_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> ob:op -> ol:op ->
  Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\
                  get_rid o1 <> get_rid o2 /\
                  Fst_then_snd? (m.rc ob ol) /\
                  get_rid ob <> get_rid ol /\
                  distinct_ops o1 o2 /\
                  distinct_ops o1 ob /\
                  distinct_ops o1 ol /\
                  distinct_ops o2 ob /\
                  distinct_ops o2 ol /\
                  distinct_ops ob ol /\
                  m.eq (m.merge l (m.do a o1) (m.do b o2)) (m.do (m.merge l a (m.do b o2)) o1) /\
                  m.eq (m.merge l (m.do a o1) (m.do (m.do b ob) o2)) (m.do (m.merge l a (m.do (m.do b ob) o2)) o1) /\
                  m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do b ol) o2)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b ol) o2)) o1))
        (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do (m.do b ob) ol) o2)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do (m.do b ob) ol) o2)) o1));

inter_left_base_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> ob:op -> ol:op ->
  Lemma (requires Fst_then_snd? (m.rc o2 o1) /\
                  Fst_then_snd? (m.rc ob ol) /\
                  get_rid o2 <> get_rid o1 /\
                  get_rid ob <> get_rid ol /\
                  distinct_ops o1 o2 /\
                  distinct_ops o1 ob /\
                  distinct_ops o1 ol /\
                  distinct_ops o2 ob /\
                  distinct_ops o2 ol /\
                  distinct_ops ob ol /\
                  m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do b ol) o2)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b ol) o2)) o1))
        (ensures m.eq (m.merge (m.do l ol) (m.do (m.do (m.do a ob) ol) o1) (m.do (m.do b ol) o2)) (m.do (m.merge (m.do l ol) (m.do (m.do a ob) ol) (m.do (m.do b ol) o2)) o1));

inter_right_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> ob:op -> ol:op -> o:op ->
  Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\
                  get_rid o1 <> get_rid o2 /\
                  Fst_then_snd? (m.rc ob ol) /\
                  get_rid ob <> get_rid ol /\
                  (~ (Either? (m.rc o ob)) \/ Fst_then_snd? (m.rc o ol)) /\
                  distinct_ops o1 o2 /\
                  distinct_ops o1 ob /\
                  distinct_ops o1 ol /\
                  distinct_ops o1 o /\
                  distinct_ops o2 ob /\
                  distinct_ops o2 ol /\
                  distinct_ops o2 o /\
                  distinct_ops ob ol /\
                  distinct_ops ob o /\
                  distinct_ops ol o /\
                  get_rid o <> get_rid ol /\
                  m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do (m.do b ob) ol) o2)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do (m.do b ob) ol) o2)) o1))
        (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do (m.do (m.do b o) ob) ol) o2)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do (m.do (m.do b o) ob) ol) o2)) o1));

inter_left_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> ob:op -> ol:op -> o:op ->
  Lemma (requires Fst_then_snd? (m.rc o2 o1) /\
                  Fst_then_snd? (m.rc ob ol) /\
                  get_rid o2 <> get_rid o1 /\
                  get_rid ob <> get_rid ol /\
                  (~ (Either? (m.rc o ob)) \/ Fst_then_snd? (m.rc o ol)) /\
                  distinct_ops o1 o2 /\
                  distinct_ops o1 ob /\
                  distinct_ops o1 ol /\
                  distinct_ops o1 o /\
                  distinct_ops o2 ob /\
                  distinct_ops o2 ol /\
                  distinct_ops o2 o /\
                  distinct_ops ob ol /\
                  distinct_ops ob o /\
                  distinct_ops ol o /\
                  get_rid o <> get_rid ol /\
                  m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do (m.do b ob) ol) o2)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do (m.do b ob) ol) o2)) o1))
        (ensures m.eq (m.merge (m.do l ol) (m.do (m.do (m.do a o) ol) o1) (m.do (m.do (m.do b ob) ol) o2)) (m.do (m.merge (m.do l ol) (m.do (m.do a o) ol) (m.do (m.do (m.do b ob) ol) o2)) o1));

ind_right_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> o2':op ->
  Lemma (requires Fst_then_snd? (m.rc o2 o1) /\
                  get_rid o1 <> get_rid o2 /\
                  distinct_ops o1 o2 /\
                  distinct_ops o1 o2' /\
                  distinct_ops o2 o2' /\
                  m.eq (m.merge l (m.do a o1) (m.do b o2)) (m.do (m.merge l a (m.do b o2)) o1))
        (ensures m.eq (m.merge l (m.do a o1) (m.do (m.do b o2') o2)) (m.do (m.merge l a (m.do (m.do b o2') o2)) o1));

ind_left_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> o1':op ->
  Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\
                  get_rid o1 <> get_rid o2 /\
                  distinct_ops o1 o2 /\
                  distinct_ops o1 o1' /\
                  distinct_ops o2 o1' /\
                  m.eq (m.merge l (m.do a o1) (m.do b o2)) (m.do (m.merge l a (m.do b o2)) o1))
        (ensures m.eq (m.merge l (m.do (m.do a o1') o1) (m.do b o2)) (m.do (m.merge l (m.do a o1') (m.do b o2)) o1));

  base_1op : o1:op ->
  Lemma (ensures m.eq (m.merge m.init_st (m.do m.init_st o1) m.init_st) (m.do (m.merge m.init_st m.init_st m.init_st) o1));

ind_lca_1op : l:st -> o1:op -> ol:op ->
  Lemma (requires distinct_ops o1 ol /\
                  m.eq (m.merge l (m.do l o1) l) (m.do (m.merge l l l) o1))
        (ensures m.eq (m.merge (m.do l ol) (m.do (m.do l ol) o1) (m.do l ol)) (m.do (m.merge (m.do l ol) (m.do l ol) (m.do l ol)) o1));

inter_right_base_1op : l:st -> a:st -> b:st -> o1:op -> ob:op -> ol:op ->
  Lemma (requires Fst_then_snd? (m.rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    (Fst_then_snd? (m.rc ob o1) ==> m.eq (m.merge l (m.do a o1) (m.do b ob)) (m.do (m.merge l a (m.do b ob)) o1)) /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do b ol)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do b ol)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do b ob) ol)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b ob) ol)) o1));

inter_left_base_1op : l:st -> a:st -> b:st -> o1:op -> ob:op -> ol:op ->
  Lemma (requires Fst_then_snd? (m.rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do b ol)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do b ol)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do (m.do a ob) ol) o1) (m.do b ol)) (m.do (m.merge (m.do l ol) (m.do (m.do a ob) ol) (m.do b ol)) o1));
          
inter_right_1op : l:st -> a:st -> b:st -> o1:op -> ob:op -> ol:op -> o:op ->
  Lemma (requires Fst_then_snd? (m.rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (m.rc o ob)) \/ Fst_then_snd? (m.rc o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do b ob) ol)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b ob) ol)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do (m.do b o) ob) ol)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do (m.do b o) ob) ol)) o1));

inter_left_1op : l:st -> a:st -> b:st -> o1:op -> ob:op -> ol:op -> o:op ->
  Lemma (requires Fst_then_snd? (m.rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (m.rc o ob)) \/ Fst_then_snd? (m.rc o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do (m.do a ob) ol) o1) (m.do b ol)) (m.do (m.merge (m.do l ol) (m.do (m.do a ob) ol) (m.do b ol)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do (m.do (m.do a o) ob) ol) o1) (m.do b ol)) (m.do (m.merge (m.do l ol) (m.do (m.do (m.do a o) ob) ol) (m.do b ol)) o1));

ind_left_1op : l:st -> a:st -> b:st -> o1:op -> o1':op -> ol:op ->
  Lemma (requires distinct_ops o1 o1' /\ distinct_ops o1 ol /\ distinct_ops o1' ol /\
                    m.eq (m.merge (m.do l ol) (m.do a o1) (m.do b ol)) (m.do (m.merge (m.do l ol) a (m.do b ol)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a o1') o1) (m.do b ol)) (m.do (m.merge (m.do l ol) (m.do a o1') (m.do b ol)) o1));

ind_right_1op : l:st -> a:st -> b:st -> o2:op -> o2':op -> ol:op ->
  Lemma (requires distinct_ops o2 o2' /\ distinct_ops o2 ol /\ distinct_ops o2' ol /\
                    m.eq (m.merge (m.do l ol) (m.do a ol) (m.do b o2)) (m.do (m.merge (m.do l ol) (m.do a ol) b) o2))
          (ensures m.eq (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b o2') o2)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do b o2')) o2));

lem_0op : l:st -> a:st -> b:st -> ol:op ->
  Lemma (ensures m.eq (m.merge (m.do l ol) (m.do a ol) (m.do b ol)) (m.do (m.merge l a b) ol))
}
*)
