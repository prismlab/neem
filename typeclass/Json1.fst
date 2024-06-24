module Json1

open FStar.Seq
module M = Dependent_map
module S = Set_extended
module L = Library

type kt : eqtype =
  |Alpha_t : string -> kt
  |Beta_t : string -> kt

class json (sta stb:Type0) (app_opa app_opb:eqtype) = {   
  init_sta : sta;
  init_stb : stb;
  
  eqa : sta -> sta -> Type0;
  eqb : stb -> stb -> Type0;
  
  rca : (pos & (nat & app_opa)) -> (pos & (nat & app_opa)) -> L.rc_res;
  rcb : (pos & (nat & app_opb)) -> (pos & (nat & app_opb)) -> L.rc_res;
  
  doa : sta -> (pos & (nat & app_opa)) -> sta;
  dob : stb -> (pos & (nat & app_opb)) -> stb;
  
  mergea : sta -> sta -> sta -> sta;
  mergeb : stb -> stb -> stb -> stb;

  lem_eqa : a:sta -> b:sta ->
    Lemma (ensures eqa a b <==> a == b);

  lem_eqb : a:stb -> b:stb ->
    Lemma (ensures eqb a b <==> a == b);
}

val vt : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> (c:kt) -> Type0
let vt #sta #stb #oa #ob #m (c:kt) =
  match c with
  |Alpha_t _ -> sta
  |Beta_t _ -> stb

type st #sta #stb #oa #ob #m = M.t kt (vt #sta #stb #oa #ob #m)

val init_st_v : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> k:kt -> vt #sta #stb #oa #ob #m k
let init_st_v #sta #stb #oa #ob #m (k:kt) : vt k =
  match k with
  |Alpha_t _ -> m.init_sta
  |Beta_t _ -> m.init_stb

val init_st : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> k:kt -> st #sta #stb #oa #ob #m
let init_st (k:kt) : st = M.const_on S.empty (fun k -> init_st_v k)

val sel : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> 
          s:st #sta #stb #oa #ob #m -> k:kt -> vt #sta #stb #oa #ob #m k
let sel #sta #stb #oa #ob #m (s:st) (k:kt) =
  match k with
  |Alpha_t _ -> if M.contains s k then M.sel s k else m.init_sta
  |Beta_t _ -> if M.contains s k then M.sel s k else m.init_stb

val eq : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> 
         a:st #sta #stb #oa #ob #m -> b:st #sta #stb #oa #ob #m -> Type0
let eq #sta #stb #oa #ob #m (a b:st) =
  (forall k. M.contains a (Alpha_t k) = M.contains b (Alpha_t k) /\ 
        M.contains a (Beta_t k) = M.contains b (Beta_t k) /\
        m.eqa (sel a (Alpha_t k)) (sel b (Alpha_t k)) /\
        m.eqb (sel a (Beta_t k)) (sel b (Beta_t k)))

type app_op_v (#app_opa:eqtype) (#app_opb:eqtype) : eqtype =
  |Alpha_op : app_opa -> app_op_v #app_opa #app_opb
  |Beta_op : app_opb -> app_op_v #app_opa #app_opb

type app_op (#app_opa:eqtype) (#app_opb:eqtype) : eqtype =
  |Set : string (* key *) -> app_op_v #app_opa #app_opb(* value op *) -> app_op #app_opa #app_opb
  
type jop (#app_opa #app_opb:eqtype) = pos (*timestamp*) & (nat (*replica ID*) & app_op #app_opa #app_opb)

let is_alpha_op (o:jop) =
  match snd (snd o) with
  |Set _ (Alpha_op _) -> true
  |_ -> false

let is_beta_op (o:jop) =
  match snd (snd o) with
  |Set _ (Beta_op _) -> true
  |_ -> false

let get_key (_,(_,Set k _)) = k

let get_opa #oa #ob (o:jop #oa #ob{is_alpha_op o}) : (pos & (nat & oa)) =
  match o with
  |ts, (rid, Set _ (Alpha_op op)) -> (ts,(rid,op))

let get_opb #oa #ob (o:jop #oa #ob{is_beta_op o}) : (pos & (nat & ob)) =
  match o with
  |ts, (rid, Set _ (Beta_op op)) -> (ts,(rid,op))
  
val do : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> 
         s:st #sta #stb #oa #ob #m -> o:jop #oa #ob -> st #sta #stb #oa #ob #m         
let do #sta #stb #oa #ob #m (s:st) (o:jop) 
  : (r:st{(is_alpha_op o ==> (forall k. M.contains r k <==> M.contains s k \/ k = Alpha_t (get_key o))) /\
                   (is_beta_op o ==> (forall k. M.contains r k <==> M.contains s k \/ k = Beta_t (get_key o)))}) =
  match snd (snd o) with
  |Set k (Alpha_op _) -> let v = sel s (Alpha_t k) in M.upd s (Alpha_t k) (m.doa v (get_opa o))
  |Set k (Beta_op _) -> let v = sel s (Beta_t k) in M.upd s (Beta_t k) (m.dob v (get_opb o))

val rc : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> o1:jop #oa #ob -> o2:jop #oa #ob -> L.rc_res
let rc #sta #stb #oa #ob #m (o1 o2:jop #oa #ob) : L.rc_res = 
  match snd (snd o1), snd (snd o2) with
  |Set k1 (Alpha_op _), Set k2 (Alpha_op _) -> if k1 = k2 then m.rca (get_opa o1) (get_opa o2) else L.Either
  |Set k1 (Beta_op _), Set k2 (Beta_op _) -> if k1 = k2 then m.rcb (get_opb o1) (get_opb o2) else L.Either
  |_ -> L.Either

val compose_values : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> 
                   k:kt -> l:st #sta #stb #oa #ob #m -> a:st #sta #stb #oa #ob #m -> b:st #sta #stb #oa #ob #m -> vt #sta #stb #oa #ob #m k
let compose_values #sta #stb #oa #ob #m (k:kt) (l a b:st) : vt k =
  if Alpha_t? k then 
    m.mergea (sel l k) (sel a k) (sel b k)
  else m.mergeb (sel l k) (sel a k) (sel b k)

val merge : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> 
            l:st #sta #stb #oa #ob #m -> a:st #sta #stb #oa #ob #m -> b:st #sta #stb #oa #ob #m -> st #sta #stb #oa #ob #m
let merge #sta #stb #oa #ob #m (l a b:st) =
  let keys = S.union (M.domain l) (S.union (M.domain a) (M.domain b)) in
  let u = M.const_on keys (fun k -> init_st #sta #stb #oa #ob #m k) in
  M.map (fun k _ -> compose_values k l a b) u
  
val apply_log_a : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> 
                  s:sta -> l:seq (pos & (nat & oa)) -> Tot sta
let rec apply_log_a #sta #stb #oa #ob #m (s:sta) (l:seq (pos & (nat & oa))) : Tot sta (decreases length l) =
  match length l with
  |0 -> s
  |_ -> apply_log_a #sta #stb #oa #ob #m (m.doa s (head l)) (tail l) 

val apply_log_b : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> 
                  s:stb -> l:seq (pos & (nat & ob)) -> Tot stb
let rec apply_log_b #sta #stb #oa #ob #m (s:stb) (l:seq (pos & (nat & ob))) : Tot stb (decreases length l) =
  match length l with
  |0 -> s
  |_ -> apply_log_b #sta #stb #oa #ob #m (m.dob s (head l)) (tail l) 

val apply_log : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> 
                s:st #sta #stb #oa #ob #m -> l:seq (jop #oa #ob) -> Tot (st #sta #stb #oa #ob #m)
let rec apply_log #sta #stb #oa #ob #m s l : Tot st (decreases length l) =
  match length l with
  |0 -> s
  |_ -> apply_log (do s (head l)) (tail l) 

class cond (sta stb:Type0) (oa ob:eqtype) (m:json sta stb oa ob) = {
  rc_non_comm : o1:jop #oa #ob -> o2:jop #oa #ob ->
    Lemma (requires L.distinct_ops o1 o2)
          (ensures L.Either? (rc #sta #stb #oa #ob #m o1 o2) <==> (forall s. eq (do #sta #stb #oa #ob #m (do s o1) o2) (do (do s o2) o1)));

  no_rc_chain : o1:jop -> o2:jop -> o3:jop ->
    Lemma (requires L.distinct_ops o1 o2 /\ L.distinct_ops o2 o3)
          (ensures ~ (L.Fst_then_snd? (rc #sta #stb #oa #ob #m o1 o2) /\ L.Fst_then_snd? (rc #sta #stb #oa #ob #m o2 o3)));

  cond_comm_base : s:st -> o1:jop -> o2:jop -> o3:jop ->
    Lemma (requires L.distinct_ops o1 o2 /\ L.distinct_ops o2 o3 /\ L.distinct_ops o1 o3 /\
                    L.Fst_then_snd? (rc #sta #stb #oa #ob #m o1 o2) /\ ~ (L.Either? (rc #sta #stb #oa #ob #m o2 o3)))
          (ensures eq (do (do (do s o1) o2) o3) (do (do #sta #stb #oa #ob #m (do s o2) o1) o3));

  cond_comm_ind : s:st -> o1:jop -> o2:jop -> o3:jop -> o:jop -> l:seq jop ->
    Lemma (requires L.distinct_ops o1 o2 /\ L.distinct_ops o1 o3 /\ L.distinct_ops o2 o3 /\ 
                    L.Fst_then_snd? (rc #sta #stb #oa #ob #m o1 o2) /\ ~ (L.Either? (rc #sta #stb #oa #ob #m o2 o3)) /\
                    eq (do (apply_log (do (do s o1) o2) l) o3) (do (apply_log (do (do s o2) o1) l) o3))
          (ensures eq (do (do (apply_log (do (do s o1) o2) l) o) o3) (do (do #sta #stb #oa #ob #m (apply_log (do (do s o2) o1) l) o) o3))        
}

val lem_eq_a : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> a:sta -> b:sta ->
  Lemma (ensures (m.eqa a b <==> a == b)) 
        [SMTPat (m.eqa a b)]
let lem_eq_a #sta #stb #oa #ob #m a b = 
  m.lem_eqa a b

val lem_eq_b : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> a:stb -> b:stb ->
  Lemma (ensures (m.eqb a b <==> a == b)) 
        [SMTPat (m.eqb a b)]
let lem_eq_b #sta #stb #oa #ob #m a b = 
  m.lem_eqb a b

#set-options "--z3rlimit 300 --ifuel 3"
class vc (sta stb:Type0) (oa ob:eqtype) (m:json sta stb oa ob) = {
 merge_comm_a : l:sta -> a:sta -> b:sta ->
  Lemma (ensures m.eqa (m.mergea l a b) (m.mergea l b a));

 merge_comm_b : l:stb -> a:stb -> b:stb ->
  Lemma (ensures m.eqb (m.mergeb l a b) (m.mergeb l b a));

 merge_idem_a : s:sta ->
  Lemma (ensures m.eqa (m.mergea s s s) s);

 merge_idem_b : s:stb ->
  Lemma (ensures m.eqb (m.mergeb s s s) s);

 base_2opa : o1:L.op #oa -> o2:L.op #oa ->
  Lemma (requires (L.Fst_then_snd? (rca #sta #stb #oa #ob #m o2 o1) \/ L.Either? (rca #sta #stb #oa #ob #m o2 o1)) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.distinct_ops o1 o2)
        (ensures m.eqa (m.mergea m.init_sta (m.doa m.init_sta o1) (m.doa m.init_sta o2)) 
                       (m.doa (m.mergea m.init_sta m.init_sta (m.doa m.init_sta o2)) o1));

 base_2opb : o1:L.op #ob -> o2:L.op #ob ->
  Lemma (requires (L.Fst_then_snd? (rcb #sta #stb #oa #ob #m o2 o1) \/ L.Either? (rcb #sta #stb #oa #ob #m o2 o1)) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.distinct_ops o1 o2)
        (ensures m.eqb (m.mergeb m.init_stb (m.dob m.init_stb o1) (m.dob m.init_stb o2)) 
                       (m.dob (m.mergeb m.init_stb m.init_stb (m.dob m.init_stb o2)) o1));

 base_2op' : o1:jop -> o2:jop -> t:kt ->
   Lemma (requires L.Either? (rc #sta #stb #oa #ob #m o2 o1) /\ L.get_rid o1 <> L.get_rid o2 /\ L.distinct_ops o1 o2 /\
                   ~ (get_key o1 = get_key o2 /\ 
                      is_alpha_op o1 /\ is_alpha_op o2 /\ (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) || L.Either? (m.rca (get_opa o2) (get_opa o1))) /\
                      is_beta_op o1 /\ is_beta_op o2 /\ (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) || L.Either? (m.rcb (get_opb o2) (get_opb o1)))))                
          (ensures eq (merge (init_st t) (do (init_st t) o1) (do (init_st t) o2)) 
                      (do #sta #stb #oa #ob #m (merge (init_st t) (init_st t) (do (init_st t) o2)) o1));

 ind_lca_2opa : l:sta -> o1:L.op #oa -> o2:L.op #oa -> ol:L.op #oa ->
   Lemma (requires (L.Fst_then_snd? (rca #sta #stb #oa #ob #m o2 o1) \/ L.Either? (rca #sta #stb #oa #ob #m o2 o1)) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.distinct_ops o1 o2 /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ol /\
                    m.eqa (m.mergea l (m.doa l o1) (m.doa l o2)) (m.doa (m.mergea l l (m.doa l o2)) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa l ol) o1) (m.doa (m.doa l ol) o2)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa l ol) (m.doa (m.doa l ol) o2)) o1));

 ind_lca_2opb : l:stb -> o1:L.op #ob -> o2:L.op #ob -> ol:L.op #ob ->
   Lemma (requires (L.Fst_then_snd? (m.rcb o2 o1) \/ L.Either? (m.rcb o2 o1)) /\ L.get_rid o1 <> L.get_rid o2 /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ol /\
                    m.eqb (m.mergeb l (m.dob l o1) (m.dob l o2)) (m.dob (m.mergeb l l (m.dob l o2)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob l ol) o1) (m.dob (m.dob l ol) o2)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob l ol) (m.dob (m.dob l ol) o2)) o1));

 ind_lca_2op' : l:st -> o1:jop -> o2:jop -> ol:jop ->
   Lemma (requires L.Either? (rc #sta #stb #oa #ob #m o2 o1) /\ L.get_rid o1 <> L.get_rid o2 /\
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ol /\
                   ~ (get_key o1 = get_key ol && get_key o2 = get_key ol /\
                      is_alpha_op o1 /\ is_alpha_op o2 /\ is_alpha_op ol /\ (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) || L.Either? (m.rca (get_opa o2) (get_opa o1))) /\
                      is_beta_op o1 /\ is_beta_op o2 /\ is_beta_op ol /\ (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) || L.Either? (m.rcb (get_opb o2) (get_opb o1)))) /\
                    eq (merge l (do l o1) (do l o2)) (do (merge l l (do l o2)) o1))
          (ensures eq (merge (do #sta #stb #oa #ob #m l ol) (do (do l ol) o1) (do (do l ol) o2)) 
                      (do (merge (do l ol) (do l ol) (do (do l ol) o2)) o1));

 inter_right_base_2opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> o2:L.op #oa -> ob:L.op #oa -> ol:L.op #oa ->
   Lemma (requires (L.Fst_then_snd? (m.rca o2 o1) \/ L.Either? (m.rca o2 o1)) /\ L.Fst_then_snd? (m.rca ob ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob <> L.get_rid ol /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ob /\ L.distinct_ops o2 ol /\ L.distinct_ops ob ol /\
                    m.eqa (m.mergea l (m.doa a o1) (m.doa b o2)) (m.doa (m.mergea l a (m.doa b o2)) o1) /\ //from pre-cond of ind_right_2op
                    m.eqa (m.mergea l (m.doa a o1) (m.doa (m.doa b ob) o2)) (m.doa (m.mergea l a (m.doa (m.doa b ob) o2)) o1) /\ //from ind_right_2op
                    m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa (m.doa b ol) o2)) 
                          (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa b ol) o2)) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa (m.doa (m.doa b ob) ol) o2)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa (m.doa b ob) ol) o2)) o1));

 inter_right_base_2opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> o2:L.op #ob -> ob':L.op #ob -> ol:L.op #ob ->
   Lemma (requires (L.Fst_then_snd? (m.rcb o2 o1) \/ L.Either? (m.rcb o2 o1)) /\ L.Fst_then_snd? (m.rcb ob' ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob' <> L.get_rid ol /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ob' /\ L.distinct_ops o2 ol /\ L.distinct_ops ob' ol /\
                    m.eqb (m.mergeb l (m.dob a o1) (m.dob b o2)) (m.dob (m.mergeb l a (m.dob b o2)) o1) /\ //from pre-cond of ind_right_2op
                    m.eqb (m.mergeb l (m.dob a o1) (m.dob (m.dob b ob') o2)) (m.dob (m.mergeb l a (m.dob (m.dob b ob') o2)) o1) /\ //from ind_right_2op
                    m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob (m.dob b ol) o2)) 
                          (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob b ol) o2)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob (m.dob (m.dob b ob') ol) o2)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob (m.dob b ob') ol) o2)) o1));
          
 inter_right_base_2op' : l:st -> a:st -> b:st -> o1:jop -> o2:jop -> ob':jop -> ol:jop ->
   Lemma (requires L.Either? (rc #sta #stb #oa #ob #m o2 o1) /\ L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob' <> L.get_rid ol /\
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ob' /\ L.distinct_ops o2 ol /\ L.distinct_ops ob' ol /\
                   ~ (get_key o1 = get_key ol && get_key o2 = get_key ol /\ get_key ob' = get_key ol /\
                      is_alpha_op o1 /\ is_alpha_op o2 /\ is_alpha_op ob' /\ is_alpha_op ol /\ (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) || L.Either? (m.rca (get_opa o2) (get_opa o1))) /\ L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) /\
                      is_beta_op o1 /\ is_beta_op o2 /\ is_beta_op ob' /\ is_beta_op ol /\ (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) || L.Either? (m.rcb (get_opb o2) (get_opb o1))) /\ L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol))) /\
                    eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) /\ //from pre-cond of ind_right_2op
                    eq (merge l (do a o1) (do (do b ob') o2)) (do (merge l a (do (do b ob') o2)) o1) /\ //from ind_right_2op
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do a ol) (do (do b ol) o2)) o1))
         (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob') ol) o2)) 
                     (do (merge (do #sta #stb #oa #ob #m l ol) (do a ol) (do (do (do b ob') ol) o2)) o1));

  inter_left_base_2opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> o2:L.op #oa -> ob:L.op #oa -> ol:L.op #oa ->
   Lemma (requires (L.Fst_then_snd? (m.rca o2 o1) \/ L.Either? (m.rca o2 o1)) /\ L.Fst_then_snd? (m.rca ob ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob <> L.get_rid ol /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ob /\ L.distinct_ops o2 ol /\ L.distinct_ops ob ol /\
                    m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa (m.doa b ol) o2)) 
                          (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa b ol) o2)) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa (m.doa a ob) ol) o1) (m.doa (m.doa b ol) o2)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa (m.doa a ob) ol) (m.doa (m.doa b ol) o2)) o1));

 inter_left_base_2opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> o2:L.op #ob -> ob':L.op #ob -> ol:L.op #ob ->
   Lemma (requires (L.Fst_then_snd? (m.rcb o2 o1) \/ L.Either? (m.rcb o2 o1)) /\ L.Fst_then_snd? (m.rcb ob' ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob' <> L.get_rid ol /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ob' /\ L.distinct_ops o2 ol /\ L.distinct_ops ob' ol /\
                    m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob (m.dob b ol) o2)) 
                          (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob b ol) o2)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob (m.dob a ob') ol) o1) (m.dob (m.dob b ol) o2)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob (m.dob a ob') ol) (m.dob (m.dob b ol) o2)) o1));
          
 inter_left_base_2op' : l:st -> a:st -> b:st -> o1:jop -> o2:jop -> ob':jop -> ol:jop ->
   Lemma (requires L.Either? (rc #sta #stb #oa #ob #m o2 o1) /\ L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob' <> L.get_rid ol /\
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ob' /\ L.distinct_ops o2 ol /\ L.distinct_ops ob' ol /\
                   ~ (get_key o1 = get_key ol && get_key o2 = get_key ol /\ get_key ob' = get_key ol /\
                      is_alpha_op o1 /\ is_alpha_op o2 /\ is_alpha_op ob' /\ is_alpha_op ol /\ (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) || L.Either? (m.rca (get_opa o2) (get_opa o1))) /\ L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) /\
                      is_beta_op o1 /\ is_beta_op o2 /\ is_beta_op ob' /\ is_beta_op ol /\ (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) || L.Either? (m.rcb (get_opb o2) (get_opb o1))) /\ L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do a ol) (do (do b ol) o2)) o1))
         (ensures eq (merge (do l ol) (do (do (do a ob') ol) o1) (do (do b ol) o2)) 
                     (do (merge (do #sta #stb #oa #ob #m l ol) (do (do a ob') ol) (do (do b ol) o2)) o1));

 inter_right_2opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> o2:L.op #oa -> ob:L.op #oa -> ol:L.op #oa -> o:L.op #oa ->
   Lemma (requires (L.Fst_then_snd? (m.rca o2 o1) \/ L.Either? (m.rca o2 o1)) /\ L.Fst_then_snd? (m.rca ob ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob <> L.get_rid ol /\
                    (~ (L.Either? (m.rca o ob)) \/ L.Fst_then_snd? (m.rca o ol)) /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ L.distinct_ops o2 ob /\
                    L.distinct_ops o2 ol /\ L.distinct_ops o2 o /\ L.distinct_ops ob ol /\ L.distinct_ops ob o /\ L.distinct_ops ol o /\
                    L.get_rid o <> L.get_rid ol /\
                    m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa (m.doa (m.doa b ob) ol) o2)) 
                          (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa (m.doa b ob) ol) o2)) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa (m.doa (m.doa (m.doa b o) ob) ol) o2)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa (m.doa (m.doa b o) ob) ol) o2)) o1));

 inter_right_2opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> o2:L.op #ob -> ob':L.op #ob -> ol:L.op #ob -> o:L.op #ob ->
   Lemma (requires (L.Fst_then_snd? (m.rcb o2 o1) \/ L.Either? (m.rcb o2 o1)) /\ L.Fst_then_snd? (m.rcb ob' ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob' <> L.get_rid ol /\
                    (~ (L.Either? (m.rcb o ob')) \/ L.Fst_then_snd? (m.rcb o ol)) /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ L.distinct_ops o2 ob' /\
                    L.distinct_ops o2 ol /\ L.distinct_ops o2 o /\ L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                    L.get_rid o <> L.get_rid ol /\
                    m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob (m.dob (m.dob b ob') ol) o2)) 
                          (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob (m.dob b ob') ol) o2)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob (m.dob (m.dob (m.dob b o) ob') ol) o2)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob (m.dob (m.dob b o) ob') ol) o2)) o1));
          
  inter_right_2op' : l:st -> a:st -> b:st -> o1:jop -> o2:jop -> ob':jop -> ol:jop -> o:jop ->
    Lemma (requires L.Either? (rc #sta #stb #oa #ob #m o2 o1) /\ L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob' <> L.get_rid ol /\
                    (~ (L.Either? (rc #sta #stb #oa #ob #m o ob')) \/ L.Fst_then_snd? (rc #sta #stb #oa #ob #m o ol)) /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ L.distinct_ops o2 ob' /\
                    L.distinct_ops o2 ol /\ L.distinct_ops o2 o /\ L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                    L.get_rid o <> L.get_rid ol /\
                    ~ (get_key o1 = get_key o && get_key o2 = get_key o /\ get_key ob' = get_key o /\ get_key ol = get_key o /\
                       is_alpha_op o1 /\ is_alpha_op o2 /\ is_alpha_op ob' /\ is_alpha_op ol /\ is_alpha_op o /\ (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) \/ L.Either? (m.rca (get_opa o2) (get_opa o1))) /\ L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) /\ (L.Fst_then_snd? (m.rca (get_opa o) (get_opa ob')) \/ L.Snd_then_fst? (m.rca (get_opa o) (get_opa ob')) \/ L.Fst_then_snd? (m.rca (get_opa o) (get_opa ol))) /\
                       is_beta_op o1 /\ is_beta_op o2 /\ is_beta_op ob' /\ is_beta_op ol /\ is_beta_op o /\ (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) \/ L.Either? (m.rcb (get_opb o2) (get_opb o1))) /\ L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) /\ (L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ob')) \/ L.Snd_then_fst? (m.rcb (get_opb o) (get_opb ob')) \/ L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ol)))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob') ol) o2)) 
                       (do (merge (do l ol) (do a ol) (do (do (do b ob') ol) o2)) o1))
         (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob') ol) o2)) 
                     (do (merge (do #sta #stb #oa #ob #m l ol) (do a ol) (do (do (do (do b o) ob') ol) o2)) o1));

 inter_left_2opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> o2:L.op #oa -> ob:L.op #oa -> ol:L.op #oa -> o:L.op #oa ->
   Lemma (requires (L.Fst_then_snd? (m.rca o2 o1) \/ L.Either? (m.rca o2 o1)) /\ L.Fst_then_snd? (m.rca ob ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob <> L.get_rid ol /\
                    (~ (L.Either? (m.rca o ob)) \/ L.Fst_then_snd? (m.rca o ol)) /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ L.distinct_ops o2 ob /\
                    L.distinct_ops o2 ol /\ L.distinct_ops o2 o /\ L.distinct_ops ob ol /\ L.distinct_ops ob o /\ L.distinct_ops ol o /\
                    L.get_rid o <> L.get_rid ol /\
                    m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa (m.doa (m.doa b ob) ol) o2)) 
                          (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa (m.doa b ob) ol) o2)) o1))
          (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa (m.doa a o) ol) o1) (m.doa (m.doa (m.doa b ob) ol) o2)) 
                         (m.doa (m.mergea (m.doa l ol) (m.doa (m.doa a o) ol) (m.doa (m.doa (m.doa b ob) ol) o2)) o1));

 inter_left_2opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> o2:L.op #ob -> ob':L.op #ob -> ol:L.op #ob -> o:L.op #ob ->
   Lemma (requires (L.Fst_then_snd? (m.rcb o2 o1) \/ L.Either? (m.rcb o2 o1)) /\ L.Fst_then_snd? (m.rcb ob' ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob' <> L.get_rid ol /\
                    (~ (L.Either? (m.rcb o ob')) \/ L.Fst_then_snd? (m.rcb o ol)) /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ L.distinct_ops o2 ob' /\
                    L.distinct_ops o2 ol /\ L.distinct_ops o2 o /\ L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                    L.get_rid o <> L.get_rid ol /\
                    m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob (m.dob (m.dob b ob') ol) o2)) 
                          (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob (m.dob b ob') ol) o2)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob (m.dob a o) ol) o1) (m.dob (m.dob (m.dob b ob') ol) o2)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob (m.dob a o) ol) (m.dob (m.dob (m.dob b ob') ol) o2)) o1));
          
 inter_left_2op' : l:st -> a:st -> b:st -> o1:jop -> o2:jop -> ob':jop -> ol:jop -> o:jop ->
   Lemma (requires L.Either? (rc #sta #stb #oa #ob #m o2 o1) /\ L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ 
                    L.get_rid o1 <> L.get_rid o2 /\ L.get_rid ob' <> L.get_rid ol /\
                    L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ L.distinct_ops o2 ob' /\
                    L.distinct_ops o2 ol /\ L.distinct_ops o2 o /\ L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                    L.get_rid o <> L.get_rid ol /\
                    ~ (get_key o1 = get_key o && get_key o2 = get_key o /\ get_key ob' = get_key o /\ get_key ol = get_key o /\
                       is_alpha_op o1 /\ is_alpha_op o2 /\ is_alpha_op ob' /\ is_alpha_op ol /\ is_alpha_op o /\ (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) \/ L.Either? (m.rca (get_opa o2) (get_opa o1))) /\ L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) /\ (L.Fst_then_snd? (m.rca (get_opa o) (get_opa ob')) \/ L.Snd_then_fst? (m.rca (get_opa o) (get_opa ob')) \/ L.Fst_then_snd? (m.rca (get_opa o) (get_opa ol))) /\
                       is_beta_op o1 /\ is_beta_op o2 /\ is_beta_op ob' /\ is_beta_op ol /\ is_beta_op o /\ (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) \/ L.Either? (m.rcb (get_opb o2) (get_opb o1))) /\ L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) /\ (L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ob')) \/ L.Snd_then_fst? (m.rcb (get_opb o) (get_opb ob')) \/ L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ol)))) /\
                    eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob') ol) o2)) 
                       (do (merge (do l ol) (do a ol) (do (do (do b ob') ol) o2)) o1))
         (ensures eq (merge (do l ol) (do (do (do a o) ol) o1) (do (do (do b ob') ol) o2)) 
                     (do (merge (do #sta #stb #oa #ob #m l ol) (do (do a o) ol) (do (do (do b ob') ol) o2)) o1));
          
 ind_right_2opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> o2:L.op #oa -> o2':L.op #oa ->
  Lemma (requires L.Fst_then_snd? (m.rca o2 o1) /\ L.get_rid o1 <> L.get_rid o2 /\
                  L.distinct_ops o1 o2 /\ L.distinct_ops o1 o2' /\ L.distinct_ops o2 o2' /\
                  m.eqa (m.mergea l (m.doa a o1) (m.doa b o2)) (m.doa (m.mergea l a (m.doa b o2)) o1))
        (ensures m.eqa (m.mergea l (m.doa a o1) (m.doa (m.doa b o2') o2)) (m.doa (m.mergea l a (m.doa (m.doa b o2') o2)) o1));

 ind_right_2opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> o2:L.op #ob -> o2':L.op #ob ->
   Lemma (requires L.Fst_then_snd? (m.rcb o2 o1) /\ L.get_rid o1 <> L.get_rid o2 /\
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 o2' /\ L.distinct_ops o2 o2' /\
                   m.eqb (m.mergeb l (m.dob a o1) (m.dob b o2)) (m.dob (m.mergeb l a (m.dob b o2)) o1))
         (ensures m.eqb (m.mergeb l (m.dob a o1) (m.dob (m.dob b o2') o2)) (m.dob (m.mergeb l a (m.dob (m.dob b o2') o2)) o1));

 ind_left_2opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> o2:L.op #oa -> o1':L.op #oa ->
   Lemma (requires L.Fst_then_snd? (m.rca o2 o1) /\ L.get_rid o1 <> L.get_rid o2 /\
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 o1' /\ L.distinct_ops o2 o1' /\
                   m.eqa (m.mergea l (m.doa a o1) (m.doa b o2)) (m.doa (m.mergea l a (m.doa b o2)) o1))
         (ensures m.eqa (m.mergea l (m.doa (m.doa a o1') o1) (m.doa b o2)) (m.doa (m.mergea l (m.doa a o1') (m.doa b o2)) o1));

 ind_left_2opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> o2:L.op #ob -> o1':L.op #ob ->
   Lemma (requires L.Fst_then_snd? (m.rcb o2 o1) /\ L.get_rid o1 <> L.get_rid o2 /\
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 o1' /\ L.distinct_ops o2 o1' /\
                   m.eqb (m.mergeb l (m.dob a o1) (m.dob b o2)) (m.dob (m.mergeb l a (m.dob b o2)) o1))
         (ensures m.eqb (m.mergeb l (m.dob (m.dob a o1') o1) (m.dob b o2)) (m.dob (m.mergeb l (m.dob a o1') (m.dob b o2)) o1));

 base_1opa : o1:L.op #oa -> 
  Lemma (ensures m.eqa (m.mergea m.init_sta (m.doa m.init_sta o1) m.init_sta) (m.doa (m.mergea m.init_sta m.init_sta m.init_sta) o1));

 base_1opb : o1:L.op #ob -> 
  Lemma (ensures m.eqb (m.mergeb m.init_stb (m.dob m.init_stb o1) m.init_stb) (m.dob (m.mergeb m.init_stb m.init_stb m.init_stb) o1));

 ind_lca_1opa : l:sta -> o1:L.op #oa -> ol:L.op #oa ->
   Lemma (requires L.distinct_ops o1 ol /\ 
                    m.eqa (m.mergea l (m.doa l o1) l) (m.doa (m.mergea l l l) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa l ol) o1) (m.doa l ol)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa l ol) (m.doa l ol)) o1));

 ind_lca_1opb : l:stb -> o1:L.op #ob -> ol:L.op #ob ->
   Lemma (requires L.distinct_ops o1 ol /\
                    m.eqb (m.mergeb l (m.dob l o1) l) (m.dob (m.mergeb l l l) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob l ol) o1) (m.dob l ol)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob l ol) (m.dob l ol)) o1));

 inter_right_base_1opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> ob:L.op #oa -> ol:L.op #oa ->
   Lemma (requires L.Fst_then_snd? (m.rca ob ol) /\ L.get_rid ob <> L.get_rid ol /\
                   L.distinct_ops o1 ob /\ L.distinct_ops o1 ol /\ L.distinct_ops ob ol /\
                   m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa b ol)) 
                         (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa b ol)) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa (m.doa b ob) ol)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa b ob) ol)) o1));

 inter_right_base_1opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> ob':L.op #ob -> ol:L.op #ob ->
   Lemma (requires L.Fst_then_snd? (m.rcb ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                   L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops ob' ol /\
                   m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob b ol)) 
                         (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob b ol)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob (m.dob b ob') ol)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob b ob') ol)) o1));

 inter_left_base_1opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> ob:L.op #oa -> ol:L.op #oa ->
   Lemma (requires L.Fst_then_snd? (m.rca ob ol) /\ L.get_rid ob <> L.get_rid ol /\
                   L.distinct_ops o1 ob /\ L.distinct_ops o1 ol /\ L.distinct_ops ob ol /\
                   m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa b ol)) 
                         (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa b ol)) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa (m.doa a ob) ol) o1) (m.doa b ol)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa (m.doa a ob) ol) (m.doa b ol)) o1));

 inter_left_base_1opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> ob':L.op #ob -> ol:L.op #ob ->
   Lemma (requires L.Fst_then_snd? (m.rcb ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                   L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops ob' ol /\
                   m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob b ol)) 
                         (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob b ol)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob (m.dob a ob') ol) o1) (m.dob b ol)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob (m.dob a ob') ol) (m.dob b ol)) o1));

 inter_right_1opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> ob:L.op #oa -> ol:L.op #oa -> o:L.op #oa ->
   Lemma (requires L.Fst_then_snd? (m.rca ob ol) /\ L.get_rid ob <> L.get_rid ol /\
                   (~ (L.Either? (m.rca o ob)) \/ L.Fst_then_snd? (m.rca o ol)) /\
                   L.distinct_ops o1 ob /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ 
                   L.distinct_ops ob ol /\ L.distinct_ops ob o /\ L.distinct_ops ol o /\
                   L.get_rid o <> L.get_rid ol /\
                   m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa (m.doa b ob) ol)) 
                         (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa b ob) ol)) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a ol) o1) (m.doa (m.doa (m.doa b o) ob) ol)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa (m.doa b o) ob) ol)) o1));

 inter_right_1opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> ob':L.op #ob -> ol:L.op #ob -> o:L.op #ob ->
   Lemma (requires L.Fst_then_snd? (m.rcb ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                   (~ (L.Either? (m.rcb o ob')) \/ L.Fst_then_snd? (m.rcb o ol)) /\
                   L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ 
                   L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                   L.get_rid o <> L.get_rid ol /\
                   m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob (m.dob b ob') ol)) 
                         (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob b ob') ol)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a ol) o1) (m.dob (m.dob (m.dob b o) ob') ol)) 
                  (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob (m.dob b o) ob') ol)) o1));

 inter_left_1opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> ob:L.op #oa -> ol:L.op #oa -> o:L.op #oa ->
   Lemma (requires L.Fst_then_snd? (m.rca ob ol) /\ L.get_rid ob <> L.get_rid ol /\
                   (~ (L.Either? (m.rca o ob)) \/ L.Fst_then_snd? (m.rca o ol)) /\
                   L.distinct_ops o1 ob /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ 
                   L.distinct_ops ob ol /\ L.distinct_ops ob o /\ L.distinct_ops ol o /\
                   L.get_rid o <> L.get_rid ol /\
                   m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa (m.doa a ob) ol) o1) (m.doa b ol)) 
                         (m.doa (m.mergea (m.doa l ol) (m.doa (m.doa a ob) ol) (m.doa b ol)) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa (m.doa (m.doa a o) ob) ol) o1) (m.doa b ol)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa (m.doa (m.doa a o) ob) ol) (m.doa b ol)) o1));

 inter_left_1opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> ob':L.op #ob -> ol:L.op #ob -> o:L.op #ob ->
   Lemma (requires L.Fst_then_snd? (m.rcb ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                   (~ (L.Either? (m.rcb o ob')) \/ L.Fst_then_snd? (m.rcb o ol)) /\
                   L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ 
                   L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                   L.get_rid o <> L.get_rid ol /\
                   m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob (m.dob a ob') ol) o1) (m.dob b ol)) 
                         (m.dob (m.mergeb (m.dob l ol) (m.dob (m.dob a ob') ol) (m.dob b ol)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob (m.dob (m.dob a o) ob') ol) o1) (m.dob b ol)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob (m.dob (m.dob a o) ob') ol) (m.dob b ol)) o1));

 ind_right_1opa : l:sta -> a:sta -> b:sta -> o2:L.op #oa -> o2':L.op #oa -> ol:L.op #oa ->
   Lemma (requires L.distinct_ops o2 o2' /\ L.distinct_ops o2 ol /\ L.distinct_ops o2' ol /\
                   m.eqa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa b o2)) (m.doa (m.mergea (m.doa l ol) (m.doa a ol) b) o2))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa (m.doa b o2') o2)) 
                        (m.doa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa b o2')) o2));

 ind_right_1opb : l:stb -> a:stb -> b:stb -> o2:L.op #ob -> o2':L.op #ob -> ol:L.op #ob -> 
   Lemma (requires L.distinct_ops o2 o2' /\ L.distinct_ops o2 ol /\ L.distinct_ops o2' ol /\
                   m.eqb (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob b o2)) (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) b) o2))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob (m.dob b o2') o2)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob b o2')) o2));

 ind_right_1op' : l:st -> a:st -> b:st -> o2:jop -> o2':jop -> ol:jop ->
   Lemma (requires L.distinct_ops o2 o2' /\ L.distinct_ops o2 ol /\ L.distinct_ops o2' ol /\
                   ~ (get_key o2 = get_key o2' /\ get_key o2 = get_key ol /\
                   is_alpha_op o2 /\ is_alpha_op o2' /\ is_alpha_op ol /\
                   is_beta_op o2 /\ is_beta_op o2' /\ is_beta_op ol) /\
                   eq (merge (do l ol) (do a ol) (do b o2)) (do (merge (do l ol) (do a ol) b) o2))
         (ensures eq (merge (do l ol) (do a ol) (do (do b o2') o2)) 
                     (do #sta #stb #oa #ob #m (merge (do l ol) (do a ol) (do b o2')) o2));
          
 ind_left_1opa : l:sta -> a:sta -> b:sta -> o1:L.op #oa -> o1':L.op #oa -> ol:L.op #oa ->
   Lemma (requires L.distinct_ops o1 o1' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1' ol /\
                   m.eqa (m.mergea (m.doa l ol) (m.doa a o1) (m.doa b ol)) (m.doa (m.mergea (m.doa l ol) a (m.doa b ol)) o1))
         (ensures m.eqa (m.mergea (m.doa l ol) (m.doa (m.doa a o1') o1) (m.doa b ol)) (m.doa (m.mergea (m.doa l ol) (m.doa a o1') (m.doa b ol)) o1));

 ind_left_1opb : l:stb -> a:stb -> b:stb -> o1:L.op #ob -> o1':L.op #ob -> ol:L.op #ob -> 
   Lemma (requires L.distinct_ops o1 o1' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1' ol /\
                   m.eqb (m.mergeb (m.dob l ol) (m.dob a o1) (m.dob b ol)) (m.dob (m.mergeb (m.dob l ol) a (m.dob b ol)) o1))
         (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob (m.dob a o1') o1) (m.dob b ol)) 
                        (m.dob (m.mergeb (m.dob l ol) (m.dob a o1') (m.dob b ol)) o1));

 ind_left_1op' : l:st -> a:st -> b:st -> o1:jop -> o1':jop -> ol:jop ->
   Lemma (requires L.distinct_ops o1 o1' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1' ol /\
                   ~ (get_key o1 = get_key o1' /\ get_key o1 = get_key ol /\
                   is_alpha_op o1 /\ is_alpha_op o1' /\ is_alpha_op ol /\
                   is_beta_op o1 /\ is_beta_op o1' /\ is_beta_op ol) /\
                   eq (merge (do l ol) (do a o1) (do b ol)) (do (merge (do l ol) a (do b ol)) o1))
         (ensures eq (merge (do l ol) (do (do a o1') o1) (do b ol)) 
                     (do #sta #stb #oa #ob #m (merge (do l ol) (do a o1') (do b ol)) o1));
          
 lem_0opa : l:sta -> a:sta -> b:sta -> ol:L.op #oa  ->
   Lemma (ensures m.eqa (m.mergea (m.doa l ol) (m.doa a ol) (m.doa b ol)) (m.doa (m.mergea l a b) ol));

 lem_0opb : l:stb -> a:stb -> b:stb -> ol:L.op #ob ->
   Lemma (ensures m.eqb (m.mergeb (m.dob l ol) (m.dob a ol) (m.dob b ol)) (m.dob (m.mergeb l a b) ol))
}

val comma : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
            l:sta -> a:sta -> b:sta ->
  Lemma (ensures (m.eqa (m.mergea l a b) (m.mergea l b a))) 
        [SMTPat (m.mergea l a b)]        
let comma #sta #stb #oa #ob #m #v l a b = v.merge_comm_a l a b

val commb : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
            l:stb -> a:stb -> b:stb ->
  Lemma (ensures (m.eqb (m.mergeb l a b) (m.mergeb l b a))) 
        [SMTPat (m.mergeb l a b)]       
let commb #sta #stb #oa #ob #m #v l a b = v.merge_comm_b l a b

val idema : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> s:sta ->
  Lemma (ensures (m.eqa (m.mergea s s s) s)) 
        [SMTPat (m.mergea s s s)]        
let idema #sta #stb #oa #ob #m #v s = v.merge_idem_a s

val idemb : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> s:stb ->
  Lemma (ensures (m.eqb (m.mergeb s s s) s)) 
        [SMTPat (m.mergeb s s s)]        
let idemb #sta #stb #oa #ob #m #v s = v.merge_idem_b s
  
val merge_comm : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> l:st #sta #stb #oa #ob #m -> a:st #sta #stb #oa #ob #m -> b:st #sta #stb #oa #ob #m ->
  Lemma (ensures (eq (merge l a b) (merge l b a)))
let merge_comm #sta #stb #oa #ob #m #v l a b = ()

val merge_idem : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> s:st #sta #stb #oa #ob #m -> 
  Lemma (ensures (eq (merge s s s) s))
let merge_idem #sta #stb #oa #ob #m #v s = ()

val base_2op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
               o1:jop -> o2:jop -> t:kt -> 
  Lemma (requires (L.Fst_then_snd? (rc #sta #stb #oa #ob #m o2 o1) \/ L.Either? (rc #sta #stb #oa #ob #m o2 o1)) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.distinct_ops o1 o2)
        (ensures eq (merge (init_st t) (do (init_st t) o1) (do (init_st t) o2)) 
                    (do #sta #stb #oa #ob #m (merge (init_st t) (init_st t) (do (init_st t) o2)) o1))                     
let base_2op #sta #stb #oa #ob #m #v o1 o2 t =
  if get_key o1 = get_key o2 && is_alpha_op o1 && is_alpha_op o2 then
    v.base_2opa (get_opa o1) (get_opa o2) 
  else if get_key o1 = get_key o2 && is_beta_op o1 && is_beta_op o2 then
    v.base_2opb (get_opb o1) (get_opb o2) 
  else if L.Either? (rc #sta #stb #oa #ob #m o2 o1) then v.base_2op' o1 o2 t
  else ()

val ind_lca_2op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                  l:st #sta #stb #oa #ob #m -> o1:jop -> o2:jop -> ol:jop ->
  Lemma (requires (L.Fst_then_snd? (rc #sta #stb #oa #ob #m o2 o1) \/ L.Either? (rc #sta #stb #oa #ob #m o2 o1)) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.distinct_ops o1 o2 /\ L.distinct_ops o1 ol /\ L.distinct_ops o2 ol /\
                   eq (merge l (do l o1) (do l o2)) (do (merge l l (do l o2)) o1))
        (ensures eq (merge (do l ol) (do (do l ol) o1) (do (do l ol) o2)) (do (merge (do l ol) (do l ol) (do (do l ol) o2)) o1))
let ind_lca_2op #sta #stb #oa #ob #m #v l o1 o2 ol =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ol && (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) || L.Either? (m.rca (get_opa o2) (get_opa o1))) then
      v.ind_lca_2opa (sel l ka) (get_opa o1) (get_opa o2) (get_opa ol)
  else if get_key o1 = k && get_key o2 = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ol && (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) || L.Either? (m.rcb (get_opb o2) (get_opb o1))) then
      v.ind_lca_2opb (sel l kb) (get_opb o1) (get_opb o2) (get_opb ol)
  else if L.Either? (rc #sta #stb #oa #ob #m o2 o1) then v.ind_lca_2op' l o1 o2 ol
  else ()

val inter_right_base_2op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) ->
                           l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o1:jop -> o2:jop -> ob':jop -> ol:jop ->
  Lemma (requires (L.Fst_then_snd? (rc #sta #stb #oa #ob #m o2 o1) \/ L.Either? (rc #sta #stb #oa #ob #m o2 o1)) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ 
                   L.distinct_ops o2 ob' /\ L.distinct_ops o2 ol /\ L.distinct_ops ob' ol /\
                   eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1) /\ //from pre-cond of ind_right_2op
                   eq (merge l (do a o1) (do (do b ob') o2)) (do (merge l a (do (do b ob') o2)) o1) /\ //from ind_right_2op
                   eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do a ol) (do (do b ol) o2)) o1))
        (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob') ol) o2)) (do (merge (do l ol) (do a ol) (do (do (do b ob') ol) o2)) o1))         
let inter_right_base_2op #sta #stb #oa #ob #m #v l a b o1 o2 ob' ol =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && get_key ob' = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob' && is_alpha_op ol && (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) || L.Either? (m.rca (get_opa o2) (get_opa o1))) && L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) then
      v.inter_right_base_2opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa o2) (get_opa ob') (get_opa ol)
  else if get_key o1 = k && get_key o2 = k && get_key ob' = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ob' && is_beta_op ol && (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) || L.Either? (m.rcb (get_opb o2) (get_opb o1))) && L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) then
      v.inter_right_base_2opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb o2) (get_opb ob') (get_opb ol)
  else if L.Either? (rc #sta #stb #oa #ob #m o2 o1) then v.inter_right_base_2op' l a b o1 o2 ob' ol
  else ()

val inter_left_base_2op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) ->
                          l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o1:jop -> o2:jop -> ob':jop -> ol:jop ->
  Lemma (requires (L.Fst_then_snd? (rc #sta #stb #oa #ob #m o2 o1) \/ L.Either? (rc #sta #stb #oa #ob #m o2 o1)) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ 
                   L.distinct_ops o2 ob' /\ L.distinct_ops o2 ol /\ L.distinct_ops ob' ol /\
                   eq (merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)) (do (merge (do l ol) (do a ol) (do (do b ol) o2)) o1))
        (ensures eq (merge (do l ol) (do (do (do a ob') ol) o1) (do (do b ol) o2)) 
                    (do (merge (do l ol) (do (do a ob') ol) (do (do b ol) o2)) o1))         
let inter_left_base_2op #sta #stb #oa #ob #m #v l a b o1 o2 ob' ol =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && get_key ob' = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob' && is_alpha_op ol && (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) || L.Either? (m.rca (get_opa o2) (get_opa o1))) && L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) then
      v.inter_left_base_2opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa o2) (get_opa ob') (get_opa ol)
  else if get_key o1 = k && get_key o2 = k && get_key ob' = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ob' && is_beta_op ol && (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) || L.Either? (m.rcb (get_opb o2) (get_opb o1))) && L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) then
      v.inter_left_base_2opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb o2) (get_opb ob') (get_opb ol)
  else if L.Either? (rc #sta #stb #oa #ob #m o2 o1) then v.inter_left_base_2op' l a b o1 o2 ob' ol
  else ()

val inter_right_2op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                      l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o1:jop -> o2:jop -> ob':jop -> ol:jop -> o:jop ->
  Lemma (requires (L.Fst_then_snd? (rc #sta #stb #oa #ob #m o2 o1) \/ L.Either? (rc #sta #stb #oa #ob #m o2 o1)) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                   (~ (L.Either? (rc #sta #stb #oa #ob #m o ob')) \/ L.Fst_then_snd? (rc #sta #stb #oa #ob #m o ol)) /\               
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ L.distinct_ops o2 ob' /\
                   L.distinct_ops o2 ol /\ L.distinct_ops o2 o /\ L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                   L.get_rid o <> L.get_rid ol /\ //from app.L.Fsti
                   eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob') ol) o2)) 
                      (do (merge (do l ol) (do a ol) (do (do (do b ob') ol) o2)) o1))
        (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do (do b o) ob') ol) o2)) 
                    (do (merge (do l ol) (do a ol) (do (do (do (do b o) ob') ol) o2)) o1))          
let inter_right_2op #sta #stb #oa #ob #m #v l a b o1 o2 ob' ol o =
  let k = get_key o in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && get_key ob' = k && get_key ol = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob' && is_alpha_op ol && is_alpha_op o && (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) || L.Either? (m.rca (get_opa o2) (get_opa o1))) && L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) && (L.Fst_then_snd? (m.rca (get_opa o) (get_opa ob')) || L.Snd_then_fst? (m.rca (get_opa o) (get_opa ob')) || L.Fst_then_snd? (m.rca (get_opa o) (get_opa ol))) then 
    v.inter_right_2opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa o2) (get_opa ob') (get_opa ol) (get_opa o)
  else if get_key o1 = k && get_key o2 = k && get_key ob' = k && get_key ol = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ob' && is_beta_op ol && is_beta_op o && (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) || L.Either? (m.rcb (get_opb o2) (get_opb o1))) && L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) && (L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ob')) || L.Snd_then_fst? (m.rcb (get_opb o) (get_opb ob')) || L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ol))) then
    v.inter_right_2opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb o2) (get_opb ob') (get_opb ol) (get_opb o)
  else if L.Either? (rc #sta #stb #oa #ob #m o2 o1) then v.inter_right_2op' l a b o1 o2 ob' ol o
  else ()

val inter_left_2op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                     l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o1:jop -> o2:jop -> ob':jop -> ol:jop -> o:jop ->
  Lemma (requires (L.Fst_then_snd? (rc #sta #stb #oa #ob #m o2 o1) \/ L.Either? (rc #sta #stb #oa #ob #m o2 o1)) /\ 
                   L.get_rid o1 <> L.get_rid o2 /\ L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                   (~ (L.Either? (rc #sta #stb #oa #ob #m o ob')) \/ L.Fst_then_snd? (rc #sta #stb #oa #ob #m o ol)) /\               
                   L.distinct_ops o1 o2 /\ L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ L.distinct_ops o2 ob' /\
                   L.distinct_ops o2 ol /\ L.distinct_ops o2 o /\ L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                   L.get_rid o <> L.get_rid ol /\ //from app.L.Fsti
                   eq (merge (do l ol) (do (do a ol) o1) (do (do (do b ob') ol) o2)) 
                      (do (merge (do l ol) (do a ol) (do (do (do b ob') ol) o2)) o1))
        (ensures eq (merge (do l ol) (do (do (do a o) ol) o1) (do (do (do b ob') ol) o2)) 
                    (do (merge (do l ol) (do (do a o) ol) (do (do (do b ob') ol) o2)) o1)) 
let inter_left_2op #sta #stb #oa #ob #m #v l a b o1 o2 ob' ol o =
  let k = get_key o in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && get_key ob' = k && get_key ol = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op ob' && is_alpha_op ol && is_alpha_op o && (L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) || L.Either? (m.rca (get_opa o2) (get_opa o1))) && L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) && (L.Fst_then_snd? (m.rca (get_opa o) (get_opa ob')) || L.Snd_then_fst? (m.rca (get_opa o) (get_opa ob')) || L.Fst_then_snd? (m.rca (get_opa o) (get_opa ol))) then 
    v.inter_left_2opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa o2) (get_opa ob') (get_opa ol) (get_opa o)
  else if get_key o1 = k && get_key o2 = k && get_key ob' = k && get_key ol = k && is_beta_op o1 && is_beta_op o2 && is_beta_op ob' && is_beta_op ol && is_beta_op o && (L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) || L.Either? (m.rcb (get_opb o2) (get_opb o1))) && L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) && (L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ob')) || L.Snd_then_fst? (m.rcb (get_opb o) (get_opb ob')) || L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ol))) then
    v.inter_left_2opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb o2) (get_opb ob') (get_opb ol) (get_opb o)
  else if L.Either? (rc #sta #stb #oa #ob #m o2 o1) then v.inter_left_2op' l a b o1 o2 ob' ol o
  else ()

val ind_right_2op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                    l:st #sta #stb #oa #ob #m -> a:st #sta #stb #oa #ob #m -> b:st #sta #stb #oa #ob #m -> o1:jop -> o2:jop -> o2':jop -> 
  Lemma (requires L.Fst_then_snd? (rc #sta #stb #oa #ob #m o2 o1) /\ L.get_rid o1 <> L.get_rid o2 /\
                  L.distinct_ops o1 o2 /\ L.distinct_ops o1 o2' /\ L.distinct_ops o2 o2' /\
                  eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1))
        (ensures eq (merge l (do a o1) (do (do b o2') o2)) (do (merge l a (do (do b o2') o2)) o1))          
let ind_right_2op #sta #stb #oa #ob #m #v l a b o1 o2 o2' =
  let k = get_key o2' in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op o2' && L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) then
      v.ind_right_2opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa o2) (get_opa o2')
  else if get_key o1 = k && get_key o2 = k && is_beta_op o1 && is_beta_op o2 && is_beta_op o2' && L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) then
      v.ind_right_2opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb o2) (get_opb o2')
  else ()

val ind_left_2op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                   l:st #sta #stb #oa #ob #m -> a:st #sta #stb #oa #ob #m -> b:st #sta #stb #oa #ob #m -> o1:jop -> o2:jop -> o1':jop -> 
  Lemma (requires L.Fst_then_snd? (rc #sta #stb #oa #ob #m o2 o1) /\ L.get_rid o1 <> L.get_rid o2 /\
                  L.distinct_ops o1 o2 /\ L.distinct_ops o1 o1' /\ L.distinct_ops o2 o1' /\
                  eq (merge l (do a o1) (do b o2)) (do (merge l a (do b o2)) o1))
        (ensures eq (merge l (do (do a o1') o1) (do b o2)) (do (merge l (do a o1') (do b o2)) o1))
let ind_left_2op #sta #stb #oa #ob #m #v l a b o1 o2 o1' =
  let k = get_key o1' in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o2 = k && is_alpha_op o1 && is_alpha_op o2 && is_alpha_op o1' && L.Fst_then_snd? (m.rca (get_opa o2) (get_opa o1)) then
      v.ind_left_2opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa o2) (get_opa o1')
  else if get_key o1 = k && get_key o2 = k && is_beta_op o1 && is_beta_op o2 && is_beta_op o1' && L.Fst_then_snd? (m.rcb (get_opb o2) (get_opb o1)) then
      v.ind_left_2opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb o2) (get_opb o1')
  else ()

val base_1op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
               o1:jop -> t:kt ->
  Lemma (ensures eq (merge (init_st t) (do (init_st t) o1) (init_st t)) 
                    (do #sta #stb #oa #ob #m (merge (init_st t) (init_st t) (init_st t)) o1))
let base_1op #sta #stb #oa #ob #m #v o1 t =
  if is_alpha_op o1 then v.base_1opa (get_opa o1)
  else if is_beta_op o1 then v.base_1opb (get_opb o1)
  else ()

val ind_lca_1op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                  l:st -> o1:jop -> ol:jop ->
  Lemma (requires L.distinct_ops o1 ol /\ eq (merge l (do l o1) l) (do (merge l l l) o1))
        (ensures eq (merge (do l ol) (do (do l ol) o1) (do l ol)) (do #sta #stb #oa #ob #m (merge (do l ol) (do l ol) (do l ol)) o1))
let ind_lca_1op #sta #stb #oa #ob #m #v l o1 ol =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && is_alpha_op o1 && is_alpha_op ol then
      v.ind_lca_1opa (sel l ka) (get_opa o1) (get_opa ol)
  else if get_key o1 = k && is_beta_op o1 && is_beta_op ol then
      v.ind_lca_1opb (sel l kb) (get_opb o1) (get_opb ol)
  else ()

val inter_right_base_1op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) ->
                           l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o1:jop -> ob':jop -> ol:jop ->
  Lemma (requires L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                  L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops ob' ol /\
                  eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1))
        (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do b ob') ol)) (do (merge (do l ol) (do a ol) (do (do b ob') ol)) o1))
let inter_right_base_1op #sta #stb #oa #ob #m #v l a b o1 ob' ol =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key ob' = k && is_alpha_op o1 && is_alpha_op ob' && is_alpha_op ol && L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) then
      v.inter_right_base_1opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa ob') (get_opa ol)
  else if get_key o1 = k && get_key ob' = k && is_beta_op o1 && is_beta_op ob' && is_beta_op ol && L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) then
      v.inter_right_base_1opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb ob') (get_opb ol)
  else ()

val inter_left_base_1op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) ->
                          l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o1:jop -> ob':jop -> ol:jop ->
  Lemma (requires L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                  L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops ob' ol /\
                  eq (merge (do l ol) (do (do a ol) o1) (do b ol)) (do (merge (do l ol) (do a ol) (do b ol)) o1))
        (ensures eq (merge (do l ol) (do (do (do a ob') ol) o1) (do b ol)) (do (merge (do l ol) (do (do a ob') ol) (do b ol)) o1))
let inter_left_base_1op #sta #stb #oa #ob #m #v l a b o1 ob' ol =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key ob' = k && is_alpha_op o1 && is_alpha_op ob' && is_alpha_op ol && L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) then
      v.inter_left_base_1opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa ob') (get_opa ol)
  else if get_key o1 = k && get_key ob' = k && is_beta_op o1 && is_beta_op ob' && is_beta_op ol && L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) then
      v.inter_left_base_1opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb ob') (get_opb ol)
  else ()

val inter_right_1op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                      l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o1:jop -> ob':jop -> ol:jop -> o:jop ->
  Lemma (requires L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                  (~ (L.Either? (rc #sta #stb #oa #ob #m o ob')) \/ L.Fst_then_snd? (rc #sta #stb #oa #ob #m o ol)) /\
                  L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ 
                  L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                  L.get_rid o <> L.get_rid ol /\ //from app.L.Fsti
                  eq (merge (do l ol) (do (do a ol) o1) (do (do b ob') ol)) (do (merge (do l ol) (do a ol) (do (do b ob') ol)) o1))
        (ensures eq (merge (do l ol) (do (do a ol) o1) (do (do (do b o) ob') ol)) 
                    (do (merge (do l ol) (do a ol) (do (do (do b o) ob') ol)) o1))
let inter_right_1op #sta #stb #oa #ob #m #v l a b o1 ob' ol o =
  let k = get_key o in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key ob' = k && get_key ol = k && is_alpha_op o1 && is_alpha_op ob' && is_alpha_op ol && is_alpha_op o && L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) && (L.Fst_then_snd? (m.rca (get_opa o) (get_opa ob')) || L.Snd_then_fst? (m.rca (get_opa o) (get_opa ob')) || L.Fst_then_snd? (m.rca (get_opa o) (get_opa ol))) then 
    v.inter_right_1opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa ob') (get_opa ol) (get_opa o)
  else if get_key o1 = k && get_key ob' = k && get_key ol = k && is_beta_op o1 && is_beta_op ob' && is_beta_op ol && is_beta_op o && L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) && (L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ob')) || L.Snd_then_fst? (m.rcb (get_opb o) (get_opb ob')) || L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ol))) then
    v.inter_right_1opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb ob') (get_opb ol) (get_opb o)
  else ()

val inter_left_1op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                     l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o1:jop -> ob':jop -> ol:jop -> o:jop ->
  Lemma (requires L.Fst_then_snd? (rc #sta #stb #oa #ob #m ob' ol) /\ L.get_rid ob' <> L.get_rid ol /\
                  (~ (L.Either? (rc #sta #stb #oa #ob #m o ob')) \/ L.Fst_then_snd? (rc #sta #stb #oa #ob #m o ol)) /\               
                  L.distinct_ops o1 ob' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1 o /\ 
                  L.distinct_ops ob' ol /\ L.distinct_ops ob' o /\ L.distinct_ops ol o /\
                  L.get_rid o <> L.get_rid ol /\ //from app.L.Fsti
                  eq (merge (do l ol) (do (do (do a ob') ol) o1) (do b ol)) (do (merge (do l ol) (do (do a ob') ol) (do b ol)) o1))
        (ensures eq (merge (do l ol) (do (do (do (do a o) ob') ol) o1) (do b ol)) 
                 (do (merge (do l ol) (do (do (do a o) ob') ol) (do b ol)) o1))
let inter_left_1op #sta #stb #oa #ob #m #v l a b o1 ob' ol o =
  let k = get_key o in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key ob' = k && get_key ol = k && is_alpha_op o1 && is_alpha_op ob' && is_alpha_op ol && is_alpha_op o && L.Fst_then_snd? (m.rca (get_opa ob') (get_opa ol)) && (L.Fst_then_snd? (m.rca (get_opa o) (get_opa ob')) || L.Snd_then_fst? (m.rca (get_opa o) (get_opa ob')) || L.Fst_then_snd? (m.rca (get_opa o) (get_opa ol))) then 
    v.inter_left_1opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa ob') (get_opa ol) (get_opa o)
  else if get_key o1 = k && get_key ob' = k && get_key ol = k && is_beta_op o1 && is_beta_op ob' && is_beta_op ol && is_beta_op o && L.Fst_then_snd? (m.rcb (get_opb ob') (get_opb ol)) && (L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ob')) || L.Snd_then_fst? (m.rcb (get_opb o) (get_opb ob')) || L.Fst_then_snd? (m.rcb (get_opb o) (get_opb ol))) then
    v.inter_left_1opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb ob') (get_opb ol) (get_opb o)
  else ()

val ind_right_1op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                    l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o2:jop -> o2':jop -> ol:jop ->
  Lemma (requires L.distinct_ops o2 o2' /\ L.distinct_ops o2 ol /\ L.distinct_ops o2' ol /\
                  eq (merge (do l ol) (do a ol) (do b o2)) (do (merge (do l ol) (do a ol) b) o2))
        (ensures eq (merge (do l ol) (do a ol) (do (do b o2') o2)) (do (merge (do l ol) (do a ol) (do b o2')) o2))
let ind_right_1op #sta #stb #oa #ob #m #v l a b o2 o2' ol =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o2 = k && get_key o2' = k && is_alpha_op o2 && is_alpha_op o2' && is_alpha_op ol then
      v.ind_right_1opa (sel l ka) (sel a ka) (sel b ka) (get_opa o2) (get_opa o2') (get_opa ol)
  else if get_key o2 = k && get_key o2' = k && is_beta_op o2 && is_beta_op o2' && is_beta_op ol then
      v.ind_right_1opb (sel l kb) (sel a kb) (sel b kb) (get_opb o2) (get_opb o2') (get_opb ol)
  else v.ind_right_1op' l a b o2 o2' ol

val ind_left_1op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
                   l:st #sta #stb #oa #ob #m -> a:st -> b:st -> o1:jop -> o1':jop -> ol:jop ->
  Lemma (requires L.distinct_ops o1 o1' /\ L.distinct_ops o1 ol /\ L.distinct_ops o1' ol /\
                  eq (merge (do l ol) (do a o1) (do b ol)) (do (merge (do l ol) a (do b ol)) o1))
        (ensures eq (merge (do l ol) (do (do a o1') o1) (do b ol)) (do (merge (do l ol) (do a o1') (do b ol)) o1)) 
let ind_left_1op #sta #stb #oa #ob #m #v l a b o1 o1' ol =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if get_key o1 = k && get_key o1' = k && is_alpha_op o1 && is_alpha_op o1' && is_alpha_op ol then
      v.ind_left_1opa (sel l ka) (sel a ka) (sel b ka) (get_opa o1) (get_opa o1') (get_opa ol)
  else if get_key o1 = k && get_key o1' = k && is_beta_op o1 && is_beta_op o1' && is_beta_op ol then
      v.ind_left_1opb (sel l kb) (sel a kb) (sel b kb) (get_opb o1) (get_opb o1') (get_opb ol)
  else v.ind_left_1op' l a b o1 o1' ol

val lem_0op : #sta:Type0 -> #stb:Type0 -> #oa:eqtype -> #ob:eqtype -> #m:(json sta stb oa ob) -> #v:(vc sta stb oa ob m) -> 
              l:st #sta #stb #oa #ob #m -> a:st -> b:st -> ol:jop ->
  Lemma (ensures eq (merge (do l ol) (do a ol) (do b ol)) (do (merge l a b) ol))
let lem_0op #sta #stb #oa #ob #m #v l a b ol =
  let k = get_key ol in
  let ka = Alpha_t k in let kb = Beta_t k in
  if is_alpha_op ol then v.lem_0opa (sel l ka) (sel a ka) (sel b ka) (get_opa ol)
  else if is_beta_op ol then v.lem_0opb (sel l kb) (sel a kb) (sel b kb) (get_opb ol)
  else ()

