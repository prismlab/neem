module Library

open FStar.Seq

let get_rid (_,(rid,_)) = rid

//conflict resolution type
type rc_res =
  |Fst_then_snd //o1 -> o2
  |Snd_then_fst //o2 -> o1
  |Either

class mrdt (st:Type0) (app_op:eqtype) = {
   
  init_st : st;
  
  eq : st -> st -> Type0;
 
  rc : (pos & (nat & app_op)) -> (pos & (nat & app_op)) -> rc_res;
  
  do : st -> (pos & (nat & app_op)) -> st;
  
  merge : st -> st -> st -> st
}

type op (#o:eqtype) = pos (*timestamp*) & (nat (*replica ID*) & o)
let distinct_ops (op1 op2:op) = fst op1 =!= fst op2

val apply_log : #st:Type0 -> #o:eqtype -> {|mrdt st o|} -> s:st -> l:seq (pos & (nat & o)) -> Tot st
let rec apply_log #st #o #m (s:st) (l:seq (pos & (nat & o))) : Tot st (decreases length l) =
  match length l with
  |0 -> s
  |_ -> apply_log #st #o #m (m.do s (head l)) (tail l) 

class cond (st:Type0) (app_op:eqtype) (m:mrdt st app_op) = {
  rc_non_comm : o1:op -> o2:op ->
    Lemma (requires distinct_ops o1 o2)
          (ensures Either? (m.rc o1 o2) <==> (forall s. m.eq (m.do (m.do s o1) o2) (m.do (m.do s o2) o1)));

  no_rc_chain : o1:op -> o2:op -> o3:op ->
    Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3)
          (ensures ~ (Fst_then_snd? (m.rc o1 o2) /\ Fst_then_snd? (m.rc o2 o3)));

  cond_comm_base : s:st -> o1:op -> o2:op -> o3:op ->
    Lemma (requires distinct_ops o1 o2 /\ distinct_ops o2 o3 /\ distinct_ops o1 o3 /\
                    Fst_then_snd? (m.rc o1 o2) /\ ~ (Either? (m.rc o2 o3)))
          (ensures m.eq (m.do (m.do (m.do s o1) o2) o3) (m.do (m.do (m.do s o2) o1) o3));

  cond_comm_ind : s:st -> o1:op -> o2:op -> o3:op -> o:op -> l:seq op ->
    Lemma (requires distinct_ops o1 o2 /\ distinct_ops o1 o3 /\ distinct_ops o2 o3 /\ 
                    Fst_then_snd? (m.rc o1 o2) /\ ~ (Either? (m.rc o2 o3)) /\
                    m.eq (m.do ((apply_log #st #app_op #m) (m.do (m.do s o1) o2) l) o3) (m.do (apply_log (m.do (m.do s o2) o1) l) o3))
          (ensures m.eq (m.do (m.do (apply_log (m.do (m.do s o1) o2) l) o) o3) (m.do (m.do (apply_log (m.do (m.do s o2) o1) l) o) o3))         
}


class vc (st:Type0) (app_op:eqtype) (m:mrdt st app_op) = {
  merge_comm : l:st -> a:st -> b:st ->
    Lemma (ensures (m.eq (m.merge l a b) (m.merge l b a)));

  merge_idem : s:st ->
    Lemma (ensures (m.eq (m.merge s s s) s));

  lem_0op : l:st -> a:st -> b:st -> ol:op ->
    Lemma (ensures m.eq (m.merge (m.do l ol) (m.do a ol) (m.do b ol)) (m.do (m.merge l a b) ol));

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
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do b ob) ol)) 
                        (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b ob) ol)) o1));

  inter_left_base_1op : l:st -> a:st -> b:st -> o1:op -> ob:op -> ol:op ->
    Lemma (requires Fst_then_snd? (m.rc ob ol) /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops ob ol /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do b ol)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do b ol)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do (m.do a ob) ol) o1) (m.do b ol)) 
                        (m.do (m.merge (m.do l ol) (m.do (m.do a ob) ol) (m.do b ol)) o1));
          
  inter_right_1op : l:st -> a:st -> b:st -> o1:op -> ob:op -> ol:op -> o:op ->
    Lemma (requires Fst_then_snd? (m.rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (m.rc o ob)) \/ Fst_then_snd? (m.rc o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do b ob) ol)) 
                         (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b ob) ol)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do (m.do b o) ob) ol)) 
                        (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do (m.do b o) ob) ol)) o1));

  inter_left_1op : l:st -> a:st -> b:st -> o1:op -> ob:op -> ol:op -> o:op ->
    Lemma (requires Fst_then_snd? (m.rc ob ol) /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (m.rc o ob)) \/ Fst_then_snd? (m.rc o ol)) /\
                    distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do (m.do a ob) ol) o1) (m.do b ol)) 
                         (m.do (m.merge (m.do l ol) (m.do (m.do a ob) ol) (m.do b ol)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do (m.do (m.do a o) ob) ol) o1) (m.do b ol)) 
                        (m.do (m.merge (m.do l ol) (m.do (m.do (m.do a o) ob) ol) (m.do b ol)) o1));

  ind_left_1op : l:st -> a:st -> b:st -> o1:op -> o1':op -> ol:op ->
    Lemma (requires distinct_ops o1 o1' /\ distinct_ops o1 ol /\ distinct_ops o1' ol /\
                    m.eq (m.merge (m.do l ol) (m.do a o1) (m.do b ol)) (m.do (m.merge (m.do l ol) a (m.do b ol)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a o1') o1) (m.do b ol)) (m.do (m.merge (m.do l ol) (m.do a o1') (m.do b ol)) o1));

  ind_right_1op : l:st -> a:st -> b:st -> o2:op -> o2':op -> ol:op ->
    Lemma (requires distinct_ops o2 o2' /\ distinct_ops o2 ol /\ distinct_ops o2' ol /\
                    m.eq (m.merge (m.do l ol) (m.do a ol) (m.do b o2)) (m.do (m.merge (m.do l ol) (m.do a ol) b) o2))
          (ensures m.eq (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b o2') o2)) (m.do (m.merge (m.do l ol) (m.do a ol) (m.do b o2')) o2));
  
  base_2op : o1:op -> o2:op ->
    Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\ get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2)
          (ensures m.eq (m.merge m.init_st (m.do m.init_st o1) (m.do m.init_st o2)) 
                        (m.do (m.merge m.init_st m.init_st (m.do m.init_st o2)) o1));

  ind_lca_2op : l:st -> o1:op -> o2:op -> ol:op ->
    Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\
                    get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2 /\ distinct_ops o1 ol /\ distinct_ops o2 ol /\
                    m.eq (m.merge l (m.do l o1) (m.do l o2)) (m.do (m.merge l l (m.do l o2)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do l ol) o1) (m.do (m.do l ol) o2)) 
                        (m.do (m.merge (m.do l ol) (m.do l ol) (m.do (m.do l ol) o2)) o1));

  inter_right_base_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> ob:op -> ol:op ->
    Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\ Fst_then_snd? (m.rc ob ol) /\
                    get_rid o1 <> get_rid o2 /\ get_rid ob <> get_rid ol /\ 
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    m.eq (m.merge l (m.do a o1) (m.do b o2)) (m.do (m.merge l a (m.do b o2)) o1) /\ //from pre-cond of ind_right_2op
                    m.eq (m.merge l (m.do a o1) (m.do (m.do b ob) o2)) (m.do (m.merge l a (m.do (m.do b ob) o2)) o1) /\ //from ind_right_2op
                    m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do b ol) o2)) 
                         (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b ol) o2)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do (m.do b ob) ol) o2)) 
                        (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do (m.do b ob) ol) o2)) o1));

  inter_left_base_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> ob:op -> ol:op ->
    Lemma (requires Fst_then_snd? (m.rc o2 o1) /\ Fst_then_snd? (m.rc ob ol) /\
                    get_rid o2 <> get_rid o1 /\ get_rid ob <> get_rid ol /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\
                    distinct_ops o2 ob /\ distinct_ops o2 ol /\ distinct_ops ob ol /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do b ol) o2)) 
                         (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do b ol) o2)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do (m.do a ob) ol) o1) (m.do (m.do b ol) o2)) 
                        (m.do (m.merge (m.do l ol) (m.do (m.do a ob) ol) (m.do (m.do b ol) o2)) o1));

  inter_right_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> ob:op -> ol:op -> o:op ->
    Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\ Fst_then_snd? (m.rc ob ol) /\
                    get_rid o1 <> get_rid o2 /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (m.rc o ob)) \/ Fst_then_snd? (m.rc o ol)) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do (m.do b ob) ol) o2)) 
                         (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do (m.do b ob) ol) o2)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do a ol) o1) (m.do (m.do (m.do (m.do b o) ob) ol) o2)) 
                        (m.do (m.merge (m.do l ol) (m.do a ol) (m.do (m.do (m.do (m.do b o) ob) ol) o2)) o1));

  inter_left_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> ob:op -> ol:op -> o:op ->
    Lemma (requires Fst_then_snd? (m.rc o2 o1) /\ Fst_then_snd? (m.rc ob ol) /\
                    get_rid o2 <> get_rid o1 /\ get_rid ob <> get_rid ol /\
                    (~ (Either? (m.rc o ob)) \/ Fst_then_snd? (m.rc o ol)) /\
                    distinct_ops o1 o2 /\ distinct_ops o1 ob /\ distinct_ops o1 ol /\ distinct_ops o1 o /\ distinct_ops o2 ob /\ 
                    distinct_ops o2 ol /\ distinct_ops o2 o /\ distinct_ops ob ol /\ distinct_ops ob o /\ distinct_ops ol o /\
                    get_rid o <> get_rid ol /\
                    m.eq (m.merge (m.do l ol) (m.do (m.do (m.do a ob) ol) o1) (m.do (m.do b ol) o2)) 
                         (m.do (m.merge (m.do l ol) (m.do (m.do a ob) ol) (m.do (m.do b ol) o2)) o1))
          (ensures m.eq (m.merge (m.do l ol) (m.do (m.do (m.do (m.do a o) ob) ol) o1) (m.do (m.do b ol) o2)) 
                        (m.do (m.merge (m.do l ol) (m.do (m.do (m.do a o) ob) ol) (m.do (m.do b ol) o2)) o1));

  ind_right_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> o2':op ->
    Lemma (requires Fst_then_snd? (m.rc o2 o1) /\
                    get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2 /\ distinct_ops o1 o2' /\ distinct_ops o2 o2' /\
                    m.eq (m.merge l (m.do a o1) (m.do b o2)) (m.do (m.merge l a (m.do b o2)) o1))
          (ensures m.eq (m.merge l (m.do a o1) (m.do (m.do b o2') o2)) (m.do (m.merge l a (m.do (m.do b o2') o2)) o1));

  ind_left_2op : l:st -> a:st -> b:st -> o1:op -> o2:op -> o1':op ->
    Lemma (requires (Fst_then_snd? (m.rc o2 o1) \/ Either? (m.rc o2 o1)) /\
                    get_rid o1 <> get_rid o2 /\ distinct_ops o1 o2 /\ distinct_ops o1 o1' /\ distinct_ops o2 o1' /\
                    m.eq (m.merge l (m.do a o1) (m.do b o2)) (m.do (m.merge l a (m.do b o2)) o1))
          (ensures m.eq (m.merge l (m.do (m.do a o1') o1) (m.do b o2)) (m.do (m.merge l (m.do a o1') (m.do b o2)) o1))
}
