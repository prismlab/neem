module App_comm

open FStar.Seq
open FStar.Ghost
module S = Set_extended

let mem_ele (ele:nat) (s:S.set (nat * nat))
  = S.exists_s s (fun e -> snd e = ele)

let mem_id_s (id:nat) (s:S.set (nat * nat))
  = S.exists_s s (fun e -> fst e = id)

let unique_ele (s:S.set (nat * nat)) =
  (forall e. S.mem e s ==> 
        not (S.exists_s s (fun e1 -> snd e = snd e1 && fst e <> fst e1)))

#set-options "--query_stats"
// the concrete state type
type concrete_st = s:S.set (nat * nat){unique_ele s}

let init_st = S.empty

let eq (a b:concrete_st) =
  S.equal a b

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
type app_op_t:eqtype =
  |Add : nat -> app_op_t
  |Rem : nat -> app_op_t

let get_ele (o:op_t) : nat =
  match snd o with
  |Add e -> e
  |Rem e -> e

// apply an operation to a state
let do (s:concrete_st) (o:op_t) : concrete_st =
  match o with
  |(id, Add e) -> let r = S.remove_if s (fun ele -> snd ele = e) in
                 S.union (S.singleton (id, e)) r
  |(_, Rem e) -> S.remove_if s (fun ele -> snd ele = e)

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : (l:log{(forall e. mem e l <==> (e == x \/ e == y))}) =
 
  if (get_ele x = get_ele y && Add? (snd x) && Rem? (snd y)) ||
    
     (get_ele x = get_ele y && Add? (snd x) && Add? (snd y) && (fst y < fst x)) then 
 
    cons y (cons x empty) else
      cons x (cons y empty)

let resolve_conflict_prop (x y:op_t) 
  : Lemma (requires fst x <> fst y)
          (ensures Seq.length (resolve_conflict x y) = 2 /\
                   (last (resolve_conflict x y) = x <==> (Add? (snd x) /\ Rem? (snd y) /\ get_ele x = get_ele y) \/
                                          (Add? (snd x) /\ Add? (snd y) /\ get_ele x = get_ele y /\ (fst y) < (fst x))) /\
                   (last (resolve_conflict x y) <> x <==> last (resolve_conflict x y) = y) /\
                  
                   (last (resolve_conflict x y) = y <==> ((Add? (snd x) /\ Rem? (snd y) /\ get_ele x <> get_ele y) \/
                                                        (Add? (snd x) /\ Add? (snd y) /\ get_ele x <> get_ele y) \/
                                                        (Rem? (snd x) /\ Rem? (snd y)) \/
                                                        (Rem? (snd x) /\ Add? (snd y)) \/
                                          (Add? (snd x) /\ Add? (snd y) /\ get_ele x = get_ele y /\ (fst y > fst x)))))
          [SMTPat (resolve_conflict x y)]
  = ()

let concrete_merge_pre (l a b:concrete_st) : prop = True

let concrete_merge (l a:concrete_st) (b:concrete_st{concrete_merge_pre l a b}) : concrete_st =
  let i_la = S.intersect l a in
  let i_lab = S.intersect i_la b in
  let da = S.remove_if a (fun e -> S.mem e l) in
  let db = S.remove_if b (fun e -> S.mem e l) in
  let da1 = S.filter_s da (fun e -> mem_ele (snd e) db && not (S.exists_s db (fun e1 -> snd e = snd e1 && fst e1 >= fst e))) in
  let db1 = S.filter_s db (fun e -> mem_ele (snd e) da && not (S.exists_s da (fun e1 -> snd e = snd e1 && fst e1 > fst e))) in
  let da_not_in_db = S.filter_s da (fun e -> not (mem_ele (snd e) db)) in 
  let db_not_in_da = S.filter_s db (fun e -> not (mem_ele (snd e) da)) in 
  let u1 = S.union i_lab (S.union da1 db1) in
  let u2 = S.union da_not_in_db db_not_in_da in
  S.union u1 u2

//operations x and y are commutative
let commutative (x y:op_t) =
  not (((Add? (snd x) && Rem? (snd y) && get_ele x = get_ele y) ||
        (Add? (snd y) && Rem? (snd x) && get_ele x = get_ele y) ||
        (Add? (snd x) && Add? (snd y) && get_ele x = get_ele y && fst x <> fst y)))

let comm_symmetric (x y:op_t) 
  : Lemma (requires commutative x y)
          (ensures commutative y x) = ()

// if x and y are commutative ops, applying them in any order should give equivalent results
let commutative_prop (x y:op_t) 
  : Lemma (requires commutative x y)
          (ensures (forall s. eq (apply_log s (cons x (cons y empty))) (apply_log s (cons y (cons x empty))))) = ()
  
let lem_trans_merge_s1' (lca s1 s2 s1':concrete_st)
  : Lemma (requires eq s1 s1')
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1' s2)) = ()
                      
let lem_trans_merge_s2' (lca s1 s2 s2':concrete_st)
  : Lemma (requires eq s2 s2')
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1 s2')) = ()
                      
let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 == ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 == ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

///////////////////////////////////////////

let common_pre_s2_gt0 (lca s1 s2:st) =
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))

let common_pre_s1_gt0 (lca s1 s2:st) =
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))

let common_pre_nc (lca s1 s2:st) =
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))

///////////////////////////////////////////

let rec lem_mem_ele_mem_id_single (a:op_t) (b:log)
  : Lemma (requires mem a b)
          (ensures mem_id (fst a) b) 
          (decreases length b) =
 match length b with
 |_ -> if head b = a then () else lem_mem_ele_mem_id_single a (tail b)

let lem_lca_eq''_base_pre (lca s1 s2:st) (last1 last2:op_t)
    : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                      not (mem_id (fst last1) (ops_of lca)) /\
                      not (mem_id (fst last2) (ops_of lca)) /\
                      length (ops_of lca) > 0)
            (ensures (let l' = inverse_st lca in
                      let s1' = inverse_st s1 in
                      let s2' = inverse_st s2 in
                      not (mem_id (fst last1) (ops_of l')) /\
                      not (mem_id (fst last2) (ops_of l')) /\
                      ops_of s1' = ops_of l' /\ ops_of s2' = ops_of l')) = ()
                      
#push-options "--z3rlimit 50"
let lem_l2a_base_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of lca) > 0 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    Add? (snd last2) /\ 
                       ((Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1) \/
                        (Rem? (snd last1) /\ get_ele last1 = get_ele last2)) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\

                    (let l' = inverse_st lca in
                     let s1' = inverse_st s1 in
                     let s2' = inverse_st s2 in
                     eq (do (concrete_merge (v_of l') (do (v_of s1') last1) (v_of s2')) last2)
                        (concrete_merge (v_of l') (do (v_of s1') last1) (do (v_of s2') last2))))

          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =
  let pre, lastl = un_snoc (ops_of lca) in
  lem_mem_ele_mem_id_single lastl (ops_of lca); 
  assert (mem_id (fst lastl) (ops_of lca)); 
  assert (fst lastl <> fst last1);
  assert (fst lastl <> fst last2);
  ()

let rec lem_l2a_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    Add? (snd last2) /\ 
                       ((Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1) \/
                        (Rem? (snd last1) /\ get_ele last1 = get_ele last2)) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 
          (decreases length (ops_of lca)) = 
  match length (ops_of lca) with
  |0 -> ()
  |_ -> let l' = inverse_st lca in
       let s1' = inverse_st s1 in
       let s2' = inverse_st s2 in 
       lem_lca_eq''_base_pre lca s1 s2 last1 last2;
       lem_l2a_base  l' s1' s2' last1 last2;
       lem_l2a_base_ind lca s1 s2 last1 last2
#pop-options

let lem_l2a_s10_s2_gt0 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    length (ops_of s2) > length (ops_of lca) /\
                    Add? (snd last2) /\ 
                       ((Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1) \/
                        (Rem? (snd last1) /\ get_ele last1 = get_ele last2)) /\
                    (let s2' = inverse_st s2 in
                    
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
         (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = ()
                      
let rec lem_l2a_s10 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Add? (snd last2) /\ 
                       ((Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1) \/
                        (Rem? (snd last1) /\ get_ele last1 = get_ele last2)) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2)]) =
  if ops_of s2 = ops_of lca then
     lem_l2a_base lca s1 s2 last1 last2
  else 
    (let s2' = inverse_st s2 in
     lem_l2a_s10 lca s1 s2' last1 last2;
     lem_l2a_s10_s2_gt0 lca s1 s2 last1 last2)

#push-options "--z3rlimit 50"
let lem_l2a_s1_gt0 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of s1) > length (ops_of lca) /\
                    Add? (snd last2) /\ 
                       ((Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1) \/
                        (Rem? (snd last1) /\ get_ele last1 = get_ele last2)) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                   
                    (let s1' = inverse_st s1 in
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)))) 
         (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                     (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()
#pop-options

let rec lem_l2a'' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires Add? (snd last2) /\ 
                       ((Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1) \/
                        (Rem? (snd last1) /\ get_ele last1 = get_ele last2)) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2); length (ops_of s1)]) = 
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    lem_l2a_base lca s1 s2 last1 last2
  else if ops_of s1 = ops_of lca then
    lem_l2a_s10 lca s1 s2 last1 last2
  else (let s1' = inverse_st s1 in
        lem_inverse (ops_of lca) (ops_of s1); 
        lem_l2a'' lca s1' s2 last1 last2;
        lem_l2a_s1_gt0 lca s1 s2 last1 last2)
        
let lem_l2a (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Add? (snd last2) /\ 
                       ((Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1) \/
                        (Rem? (snd last1) /\ get_ele last1 = get_ele last2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  lem_diff (ops_of s1) (ops_of lca); 
  lem_diff (ops_of s2) (ops_of lca);
  lem_suf_equal2_last (ops_of lca) (ops_of s1); 
  lem_suf_equal2_last (ops_of lca) (ops_of s2); 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  let s2' = inverse_st s2 in
  let s1' = inverse_st s1 in
  lem_l2a'' lca s1' s2' last1 last2
  
//////////////////////////////////////////

#push-options "--z3rlimit 50"
let lem_l1a_base_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of lca) > 0 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    Add? (snd last1) /\ 
                       ((Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2) \/
                        (Rem? (snd last2) /\ get_ele last1 = get_ele last2)) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\

                    (let l' = inverse_st lca in
                     let s1' = inverse_st s1 in
                     let s2' = inverse_st s2 in
                     eq (do (concrete_merge (v_of l') (v_of s1') (do (v_of s2') last2)) last1)
                        (concrete_merge (v_of l') (do (v_of s1') last1) (do (v_of s2') last2))))

          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let pre, lastl = un_snoc (ops_of lca) in
  lem_mem_ele_mem_id_single lastl (ops_of lca);
  assert (mem_id (fst lastl) (ops_of lca)); 
  assert (fst lastl <> fst last1);
  assert (fst lastl <> fst last2);
  ()

let rec lem_l1a_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    Add? (snd last1) /\ 
                       ((Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2) \/
                        (Rem? (snd last2) /\ get_ele last1 = get_ele last2)) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 
          (decreases length (ops_of lca)) = 
  match length (ops_of lca) with
  |0 -> ()
  |_ -> let l' = inverse_st lca in
       let s1' = inverse_st s1 in
       let s2' = inverse_st s2 in 
       lem_lca_eq''_base_pre lca s1 s2 last1 last2;
       lem_l1a_base  l' s1' s2' last1 last2;
       lem_l1a_base_ind lca s1 s2 last1 last2
#pop-options

let lem_l1a_s20_s1_gt0 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    length (ops_of s1) > length (ops_of lca) /\
                    Add? (snd last1) /\ 
                       ((Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2) \/
                        (Rem? (snd last2) /\ get_ele last1 = get_ele last2)) /\
                    (let s1' = inverse_st s1 in
                    
                     eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
         (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = ()
                      
let rec lem_l1a_s20 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    Add? (snd last1) /\ 
                       ((Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2) \/
                        (Rem? (snd last2) /\ get_ele last1 = get_ele last2)) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1)]) =
  if ops_of s1 = ops_of lca then
     lem_l1a_base lca s1 s2 last1 last2
  else 
    (let s1' = inverse_st s1 in
     lem_l1a_s20 lca s1' s2 last1 last2;
     lem_l1a_s20_s1_gt0 lca s1 s2 last1 last2)

#push-options "--z3rlimit 50"
let lem_l1a_s2_gt0 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of s2) > length (ops_of lca) /\
                    Add? (snd last1) /\ 
                       ((Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2) \/
                        (Rem? (snd last2) /\ get_ele last1 = get_ele last2)) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                   
                    (let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)))) 
         (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                     (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = ()
#pop-options

let rec lem_l1a'' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires Add? (snd last1) /\ 
                       ((Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2) \/
                        (Rem? (snd last2) /\ get_ele last1 = get_ele last2)) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1); length (ops_of s2)]) =
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    lem_l1a_base lca s1 s2 last1 last2
  else if ops_of s2 = ops_of lca then
    lem_l1a_s20 lca s1 s2 last1 last2
  else (let s2' = inverse_st s2 in
        lem_l1a'' lca s1 s2' last1 last2;
        lem_l1a_s2_gt0 lca s1 s2 last1 last2)
        
let lem_l1a (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Add? (snd last1) /\ 
                       ((Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2) \/
                        (Rem? (snd last2) /\ get_ele last1 = get_ele last2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  lem_diff (ops_of s1) (ops_of lca); 
  lem_diff (ops_of s2) (ops_of lca);
  lem_suf_equal2_last (ops_of lca) (ops_of s1); 
  lem_suf_equal2_last (ops_of lca) (ops_of s2); 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  let s2' = inverse_st s2 in
  let s1' = inverse_st s1 in
  lem_l1a'' lca s1' s2' last1 last2

//////////////////////////////////////////

let rec lem_not_id (l:log) (op:op_t)
  : Lemma (requires distinct_ops l /\ 
                    not (mem_id (fst op) l))
          (ensures not (mem op l)) (decreases length l) = 
  match length l with
  |0 -> ()
  |_ -> let hd = head l in
       let tl = tail l in
       assert (l = cons hd tl);
       distinct_invert_append (create 1 hd) tl; 
       lem_not_id (tail l) op
       
let rec lem_count_id_ele (l:log) (op:op_t)
  : Lemma (requires count_id (fst op) l = 1 /\ mem op l /\ distinct_ops l)
          (ensures count op l = 1) (decreases length l) =
  match length l with
  |1 -> ()
  |_ -> if (fst (head l) = fst op) 
         then (assert (not (mem_id (fst op) (tail l))); 
               assert (l = cons (head l) (tail l));
               distinct_invert_append (create 1 (head l)) (tail l); 
               lem_not_id (tail l) op)
          else (lemma_tl (head l) (tail l);
                lemma_append_count_id (create 1 (head l)) (tail l);
                distinct_invert_append (create 1 (head l)) (tail l);
                lem_count_id_ele (tail l) op)

let lem_lastop_suf_0_help (l2:log) (op:op_t)
  : Lemma (requires last (cons op l2) = op /\
                    count op (cons op l2) = 1)
          (ensures not (mem op l2) /\ length l2 = 0) =
  lemma_mem_append (create 1 op) l2;
  lemma_append_count (create 1 op) l2
  
let lem_lastop_suf_0 (l l1 l2:log) (op:op_t)
  : Lemma (requires distinct_ops l /\ mem op l /\
                    l = snoc l1 op ++ l2 /\
                    (lemma_mem_append (snoc l1 op) l2;
                    last l = op))
          (ensures length l2 = 0) =
  lemma_mem_append (snoc l1 op) l2;
  lemma_append_count (snoc l1 op) l2;
  mem_ele_id op l;
  count_1 l;
  lem_count_id_ele l op;
  assert (count op l = 1); 
  append_assoc l1 (create 1 op) l2;
  assert (l = l1 ++ cons op l2);

  lemma_mem_append l1 (cons op l2);
  lemma_append_count l1 (cons op l2);
  lemma_mem_append (create 1 op) l2;
  lemma_append_count (create 1 op) l2;
  assert (mem op (cons op l2)); 
  assert (count op (cons op l2) = 1); 
  assert (last l = last (cons op l2));
  lem_lastop_suf_0_help l2 op

#push-options "--z3rlimit 50"
let rem_add_lastop_neq_ele (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    common_pre_s2_gt0 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    fst last1 <> fst last2 /\
                    Add? (snd last1) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    ~ (Rem? (snd last2) /\ get_ele last1 = get_ele last2) /\
                    ~ (Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2))) =
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  let s1' = inverse_st s1 in
  lemma_mem_snoc (ops_of s1') last1;
  assert (mem last1 (ops_of s1));
  lem_last (ops_of s1);
  assert (last (ops_of s1) = last1);
  lem_diff (ops_of s1) (ops_of lca);
  assert (last (diff (ops_of s1) (ops_of lca)) = last1);
  assert (mem last1 (diff (ops_of s1) (ops_of lca)));
  let pre, suf = pre_suf (diff (ops_of s1) (ops_of lca)) last1 in
  lem_lastop_suf_0 (diff (ops_of s1) (ops_of lca)) pre suf last1;
  assert (length suf = 0);
  lemma_empty suf; 
  comm_empty_log last1 suf;  
  
  assert (((Rem? (snd last2) /\ get_ele last1 = get_ele last2) \/
           (Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2)) ==> commutative_seq last1 suf);  
 
  assert (((Rem? (snd last2) /\ get_ele last1 = get_ele last2) \/
           (Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2)) ==> not (commutative last1 last2));
  assert (((Rem? (snd last2) /\ get_ele last1 = get_ele last2) \/
           (Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2)) 
             ==> last (resolve_conflict last1 last2) = last1); 
  assert (((Rem? (snd last2) /\ get_ele last1 = get_ele last2) \/
           (Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2))
             ==> (not (commutative last1 last2) /\
                 last (resolve_conflict last1 last2) = last1 /\
                 commutative_seq last1 suf));
  assert (((Rem? (snd last2) /\ get_ele last1 = get_ele last2) \/
           (Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2))
             ==> exists_triple last2 (diff (ops_of s1) (ops_of lca)));
  ()
  
/////////////////////////////////////////

let lem_l2r_s10p (lca s1 s2:st)
  : Lemma (requires common_pre_s2_gt0 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Rem? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
          (ensures (let s2' = inverse_st s2 in
                    let _, last2 = un_snoc (ops_of s2) in
                    common_pre_nc lca s1 s2' /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of s2')) /\
                    not (mem_id (fst last2) (ops_of s1)))) =
  let s2' = inverse_st s2 in
  let _, last2 = un_snoc (ops_of s2) in
  assert (is_prefix (ops_of lca) (ops_of s1));
  assert (is_prefix (ops_of lca) (ops_of s2'));
  assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) ;
  lastop_diff (ops_of lca) (ops_of s2);
  assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) ;
  inverse_diff_id1 (ops_of lca) (ops_of s1) (ops_of s2);
  assert (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca))));
  assert (common_pre_nc lca s1 s2'); 
  lem_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  assert (not (mem_id (fst last2) (ops_of lca)) /\
          not (mem_id (fst last2) (ops_of s2')) /\
          not (mem_id (fst last2) (ops_of s1))); 
  ()

let lem_l2r_s10_base (lca s1 s2:st) (last2:op_t)
  : Lemma (requires common_pre_nc lca s1 s2 /\ 
                    ops_of s1 = ops_of lca /\
                    Rem? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca)
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) = ()

let lem_l2r_s10_ind (lca s1 s2:st) (last2:op_t)
  : Lemma (requires common_pre_s2_gt0 lca s1 s2 /\ 
                    ops_of s1 = ops_of lca /\
                    Rem? (snd last2) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of s1)) /\
                    not (mem_id (fst last2) (ops_of s2)) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    is_prefix (ops_of lca) (ops_of s2) /\

                    (let s2' = inverse_st s2 in
                    common_pre_nc lca s1 s2' /\ 
                    not (mem_id (fst last2) (ops_of s2')) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))))
                   
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))) = () 

let common_pre1_pre2 (lca s1 s2:st)
  : Lemma (requires common_pre_nc lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca))
          (ensures common_pre_s2_gt0 lca s1 s2) = ()
  
let lem_common_pre1_s2' (lca s1 s2:st) (last2:op_t)
  : Lemma (requires common_pre_s2_gt0 lca s1 s2 /\
                    not (mem_id (fst last2) (ops_of s2)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of s1)) /\
                   ops_of s1 = ops_of lca /\
                   not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   is_prefix (ops_of lca) (ops_of s2))
          (ensures (let s2' = inverse_st s2 in
                   common_pre_nc lca s1 s2' /\ 
                   not (mem_id (fst last2) (ops_of s2')) /\
                   is_prefix (ops_of lca) (ops_of s2'))) =
  let s2' = inverse_st s2 in
  assert (is_prefix (ops_of lca) (ops_of s1));
  lem_inverse (ops_of lca) (ops_of s2);
  assert (is_prefix (ops_of lca) (ops_of s2'));
  inverse_diff_id1 (ops_of lca) (ops_of s1) (ops_of s2);
  assert (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca))));
  assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1);
  lastop_diff (ops_of lca) (ops_of s2);
  assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1);
  assert (not (mem_id (fst last2) (ops_of s2'))); 
  ()
  
let rec lem_l2r_s10 (lca s1 s2:st) (last2:op_t)
 : Lemma (requires common_pre_nc lca s1 s2 /\ 
                   ops_of s1 = ops_of lca /\
                   Rem? (snd last2) /\
                   not (mem_id (fst last2) (ops_of lca)) /\
                   not (mem_id (fst last2) (ops_of s1)) /\
                   not (mem_id (fst last2) (ops_of s2)) /\
                   not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   is_prefix (ops_of lca) (ops_of s2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))
         (decreases %[length (ops_of s2)]) =
   if ops_of s2 = ops_of lca
     then lem_l2r_s10_base lca s1 s2 last2
   else 
     (let s2' = inverse_st s2 in
      common_pre1_pre2 lca s1 s2;
      lem_common_pre1_s2' lca s1 s2 last2;
      lem_l2r_s10 lca s1 s2' last2;
      lem_l2r_s10_ind lca s1 s2 last2)  

let not_add_eq (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    common_pre_s2_gt0 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                     Rem? (snd last2) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     (let s2' = inverse_st s2 in
                     is_prefix (ops_of lca) (ops_of s2')))) 
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    ~ (Add? (snd last1) /\ get_ele last1 = get_ele last2))) = 
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2); 
  assert (fst last1 <> fst last2);

  let s1' = inverse_st s1 in
  lemma_mem_snoc (ops_of s1') last1;
  assert (mem last1 (ops_of s1)); 
  lem_last (ops_of s1);
  assert (last (ops_of s1) = last1);
  lem_diff (ops_of s1) (ops_of lca);
  assert (last (diff (ops_of s1) (ops_of lca)) = last1);
  assert (mem last1 (diff (ops_of s1) (ops_of lca)));
  let pre, suf = pre_suf (diff (ops_of s1) (ops_of lca)) last1 in
  lem_lastop_suf_0 (diff (ops_of s1) (ops_of lca)) pre suf last1;
  assert (length suf = 0);
  lemma_empty suf; 
  comm_empty_log last1 suf; 
  assert (commutative_seq last1 suf);

  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> not (commutative last1 last2));
  resolve_conflict_prop last2 last1;
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> 
                last (resolve_conflict last2 last1) = last1);
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> 
                not (commutative last2 last1) /\
                last (resolve_conflict last2 last1) = last1 /\
                commutative_seq last1 suf);
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> exists_triple last2 (diff (ops_of s1) (ops_of lca)));
  assert (~ (Add? (snd last1) /\ get_ele last1 = get_ele last2)); ()

let trans_op_ele (a b c:concrete_st) (ele:nat)
  : Lemma (requires (forall e. S.mem e a <==> (S.mem e b /\ snd e <> ele)) /\
                    (forall e. (S.mem e b /\ snd e <> ele) <==> S.mem e c))
          (ensures eq a c) = ()

let lem_l2r_l1r_eq (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    common_pre_s2_gt0 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                     Rem? (snd last2) /\ Rem? (snd last1) && get_ele last1 = get_ele last2 /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     (let s2' = inverse_st s2 in
                     is_prefix (ops_of lca) (ops_of s2'))))              
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  let s2' = inverse_st s2 in  
  lem_last (ops_of s2);
  let s1' = inverse_st s1 in 
  lem_last (ops_of s1);
  let ds2 = S.remove_if (v_of s2) (fun e -> S.mem e (v_of lca)) in 
  let ds2' = S.remove_if (v_of s2') (fun e -> S.mem e (v_of lca)) in
  assert (forall e. S.mem e ds2 <==> S.mem e ds2' /\ snd e <> get_ele last2);
  
  let ds1 = S.remove_if (v_of s1) (fun e -> S.mem e (v_of lca)) in 
  let ds1' = S.remove_if (v_of s1') (fun e -> S.mem e (v_of lca)) in
  assert (forall e. S.mem e ds1 <==> S.mem e ds1' /\ snd e <> get_ele last2);

  let i1 = S.intersect (v_of s1) (v_of s2) in
  let i = S.intersect (v_of lca) i1 in
  let i1' = S.intersect (v_of s1) (v_of s2') in
  let i' = S.intersect (v_of lca) i1' in
  assert (forall e. (S.mem e i' /\ snd e <> get_ele last2) <==> S.mem e i);   
  assert (forall e. (S.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2')) /\ snd e <> get_ele last2) <==>
                S.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)); 
  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of s2'))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
               (get_ele last2)

let lem_l2r_neq_p1 (lca s1 s2:st)
 : Lemma (requires common_pre_s2_gt0 lca s1 s2 /\ 
                   length (ops_of s1) > length (ops_of lca) /\
                   (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
         (ensures (let s1' = inverse_st s1 in
                   common_pre_s2_gt0 lca s1' s2)) =
 let s1' = inverse_st s1 in
 let s2' = inverse_st s2 in
 lem_inverse (ops_of lca) (ops_of s1);
 assert (is_prefix (ops_of lca) (ops_of s1')); 
 inverse_diff_id (ops_of lca) (ops_of s1) (ops_of s2);
 assert (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))));
 lastop_diff (ops_of lca) (ops_of s1);
 assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1); 
 assert (common_pre_s2_gt0 lca s1' s2);
 ()

let rec commu_seq_prop (op:op_t) (l:log)
  : Lemma (requires Add? (snd op))
          (ensures commutative_seq op l <==> 
                   (forall e. mem e l /\ get_ele op = get_ele e ==>
                   Add? (snd e) /\ fst e = fst op))
                       (decreases length l) =
  match length l with
  |0 -> ()
  |1 -> ()
  |_ -> commu_seq_prop op (tail l)

let commu_seq_prop_l (op:op_t) (l':log) (last1:op_t)
  : Lemma (requires Add? (snd op) /\ get_ele last1 <> get_ele op /\ commutative_seq op l')
          (ensures commutative_seq op (snoc l' last1)) = 
  lemma_mem_snoc l' last1;
  commu_seq_prop op l';
  commu_seq_prop op (snoc l' last1)
  
let lem_l2r_neq_p2'_help (l:log) (last2:op_t)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd last2) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 <> get_ele last2 /\
                    exists_triple last2 l'))
          (ensures exists_triple last2 l) 
          [SMTPat (let l', last1 = un_snoc l in
                   (exists_triple last2 l'))] =
  let l', last1 = un_snoc l in
  let pre', op', suf' = find_triple last2 l' in
  lemma_mem_snoc l' last1;
  assert (mem op' l);
  let pre, suf = pre_suf l op' in
  commu_seq_prop op' suf';
  
  assert ((snoc pre op') ++ suf = snoc ((snoc pre' op') ++ suf') last1);
  append_assoc (snoc pre' op') suf' (create 1 last1);
  assert ((snoc pre op') ++ suf = ((snoc pre' op') ++ (snoc suf' last1)));
  lem_suf_equal4 l op';
  distinct_invert_append l' (create 1 last1);
  lem_suf_equal4 l' op';

  not_mem_id l' last1;
  mem_ele_id op' l;
  mem_ele_id op' l';
  lem_id_not_snoc l' suf' last1 op'; 
  assert (not (mem_id (fst op') (snoc suf' last1)));
 
  count_1 l;
  assert (count_id (fst op') (snoc pre op' ++ suf) = 1);
  lem_count_1 pre suf pre' (snoc suf' last1) op';
  
  assert (length suf = length (snoc suf' last1));
  lemma_append_inj (snoc pre op') suf (snoc pre' op') (snoc suf' last1);
  assert (suf = snoc suf' last1);
  commu_seq_prop_l op' suf' last1;
  assert (commutative_seq op' suf); 
  ()
  
let lem_l2r_neq_p2' (l:log) (last2:op_t)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd last2) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 <> get_ele last2))
          (ensures (let l', last1 = un_snoc l in 
                    (exists_triple last2 l' ==> exists_triple last2 l) /\
                    (not (exists_triple last2 l) ==> not (exists_triple last2 l')))) = ()

let lem_l2r_neq_p2 (lca s1 s2:st)
 : Lemma (requires common_pre_s2_gt0 lca s1 s2 /\ 
                   length (ops_of s1) > length (ops_of lca) /\
                   (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
         (ensures (let s1' = inverse_st s1 in
                   let s2' = inverse_st s2 in
                   let _, last2 = un_snoc (ops_of s2) in
                   (lem_l2r_neq_p1 lca s1 s2;
                    (not (exists_triple last2 (diff (ops_of s1') (ops_of lca))))))) = 
 lem_l2r_neq_p1 lca s1 s2;
 let s1' = inverse_st s1 in
 let _, last2 = un_snoc (ops_of s2) in
 let pre1, last1 = un_snoc (ops_of s1) in
 let pre1d, last1d = un_snoc (diff (ops_of s1) (ops_of lca)) in
 lem_diff (ops_of s1) (ops_of lca);
 assert (last1 = last1d);
 assert (get_ele last1d <> get_ele last2);
 assert ((diff (ops_of s1') (ops_of lca)) = pre1d);
 lem_l2r_neq_p2' (diff (ops_of s1) (ops_of lca)) last2

let lem_not_ele_diff1 (lca s1 s2 m:concrete_st) (ele:nat)
  : Lemma (requires not (mem_ele ele m) /\
                    eq m (concrete_merge lca s1 s2) /\
                    not (mem_ele ele (S.remove_if s2 (fun e -> S.mem e lca))) /\
                    (forall e. S.mem e lca /\ S.mem e s1 /\ S.mem e s2 ==> snd e <> ele))
          (ensures not (mem_ele ele (S.remove_if s1 (fun e -> S.mem e lca)))) = ()

let lem_not_ele_diff (s1' s1 lca:concrete_st) (op:op_t) (ele:nat)
  : Lemma (requires s1 = do s1' op /\ get_ele op <> ele /\
                    not (mem_ele ele ((S.remove_if s1' (fun e -> S.mem e lca)))))
          (ensures not (mem_ele ele ((S.remove_if s1 (fun e -> S.mem e lca))))) = ()

#push-options "--z3rlimit 100"
let lem_l2r_ind_rem (lca s1 s2:st)
  : Lemma (requires (Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    (let s1' = inverse_st s1 in
                    common_pre_s2_gt0 lca s1 s2 /\
                    (let s2' = inverse_st s2 in
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ Rem? (snd last1) /\ get_ele last1 <> get_ele last2 /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1') (v_of s2)))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let s2' = inverse_st s2 in  //check why this line is needed
  lem_last (ops_of s2);
  let s1' = inverse_st s1 in //check why this line is needed
  lem_last (ops_of s1)

#push-options "--z3rlimit 200"
let lem_l2r_ind_add (lca s1 s2:st)
  : Lemma (requires (Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    (let s1' = inverse_st s1 in
                    common_pre_s2_gt0 lca s1 s2 /\
                    (let s2' = inverse_st s2 in
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ Add? (snd last1) /\ get_ele last1 <> get_ele last2 /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1') (v_of s2)))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let s2' = inverse_st s2 in  //check why this line is needed
  lem_last (ops_of s2);
  let s1' = inverse_st s1 in //check why this line is needed
  lem_last (ops_of s1)
#pop-options

let lem_l2r_ind (lca s1 s2:st)
  : Lemma (requires (Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    (let s1' = inverse_st s1 in
                    common_pre_s2_gt0 lca s1 s2 /\
                    (let s2' = inverse_st s2 in
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last2 <> get_ele last1 /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1') (v_of s2)))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  if Add? (snd last1) then
    lem_l2r_ind_add lca s1 s2
  else lem_l2r_ind_rem lca s1 s2

let rec lem_l2r' (lca s1 s2:st)
 : Lemma (requires common_pre_s2_gt0 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Rem? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2'))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))
         (decreases %[length (ops_of s1)]) =
   let _, last2 = un_snoc (ops_of s2) in
   if ops_of s1 = ops_of lca then
     (let s2' = inverse_st s2 in
      lem_l2r_s10p lca s1 s2;
      lem_l2r_s10 lca s1 s2' last2) 
   else 
     (let _, last1 = un_snoc (ops_of s1) in
      not_add_eq lca s1 s2;
      assert (~ (Add? (snd last1) /\ get_ele last1 = get_ele last2));
      let s1' = inverse_st s1 in
      if Rem? (snd last1) && get_ele last1 = get_ele last2 then
        lem_l2r_l1r_eq lca s1 s2
      else if get_ele last1 <> get_ele last2 then
        (lem_l2r_neq_p1 lca s1 s2;
         lem_l2r_neq_p2 lca s1 s2;
         lem_l2r' lca s1' s2;
         lem_l2r_ind lca s1 s2)
      else ())
      
let lem_l2r (lca s1 s2:st)
 : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Rem? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
 lem_l2r' lca s1 s2

/////////////////////////////////////////

let pre1_pre2_s2 (lca s1 s2:st)
    : Lemma (requires common_pre_s2_gt0 lca s1 s2)
            (ensures common_pre_nc lca s1 (inverse_st s2)) = 
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2);
  inverse_diff_id1 (ops_of lca) (ops_of s1) (ops_of s2)

let rem_add_lastop_neq_ele' (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    common_pre_s2_gt0 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    fst last1 <> fst last2 /\
                    Add? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    ~ (Rem? (snd last1) /\ get_ele last1 = get_ele last2))) =
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  let s2' = inverse_st s2 in
  lemma_mem_snoc (ops_of s2') last2;
  assert (mem last2 (ops_of s2));
  lem_last (ops_of s2);
  assert (last (ops_of s2) = last2);
  lem_diff (ops_of s2) (ops_of lca);
  assert (last (diff (ops_of s2) (ops_of lca)) = last2);
  assert (mem last2 (diff (ops_of s2) (ops_of lca)));
  let pre, suf = pre_suf (diff (ops_of s2) (ops_of lca)) last2 in
  lem_lastop_suf_0 (diff (ops_of s2) (ops_of lca)) pre suf last2;
  assert (length suf = 0);
  lemma_empty suf; 
  comm_empty_log last2 suf; 
  
  assert (Rem? (snd last1) /\ get_ele last1 = get_ele last2 ==> commutative_seq last2 suf); 
  assert (Rem? (snd last1) /\ get_ele last1 = get_ele last2 ==> not (commutative last2 last1));
  assert (Rem? (snd last1) /\ get_ele last1 = get_ele last2 ==> last (resolve_conflict last2 last1) = last2);
  assert (Rem? (snd last1) /\ get_ele last1 = get_ele last2 ==> 
          (not (commutative last2 last1) /\
          last (resolve_conflict last2 last1) = last2 /\
          commutative_seq last2 suf));
  assert (Rem? (snd last1) /\ get_ele last1 = get_ele last2 ==> 
           exists_triple last1 (diff (ops_of s2) (ops_of lca)));
  ()

let lem_l2a_last'_base_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of lca) > 0 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    Add? (snd last2) /\
                    ((get_ele last1 <> get_ele last2) \/
                     (Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1)) /\

                    (let l' = inverse_st lca in
                     let s1' = inverse_st s1 in
                     let s2' = inverse_st s2 in
                     eq (do (concrete_merge (v_of l') (do (v_of s1') last1) (v_of s2')) last2)
                        (concrete_merge (v_of l') (do (v_of s1') last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let pre, lastl = un_snoc (ops_of lca) in
  lem_mem_ele_mem_id_single lastl (ops_of lca);
  assert (mem_id (fst lastl) (ops_of lca)); 
  assert (fst lastl <> fst last1);
  assert (fst lastl <> fst last2);
  ()

let lem_l2a_last'_base_pre (lca s1 s2:st) (last1 last2:op_t)
    : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                      not (mem_id (fst last1) (ops_of lca)) /\
                      not (mem_id (fst last2) (ops_of lca)) /\
                      length (ops_of lca) > 0)
            (ensures (let l' = inverse_st lca in
                      let s1' = inverse_st s1 in
                      let s2' = inverse_st s2 in
                      not (mem_id (fst last1) (ops_of l')) /\
                      not (mem_id (fst last2) (ops_of l')) /\
                      ops_of s1' = ops_of l' /\ ops_of s2' = ops_of l')) = ()
                      
let rec lem_l2a_last'_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    Add? (snd last2) /\
                    ((get_ele last1 <> get_ele last2) \/
                     (Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases length (ops_of lca)) = 
  match length (ops_of lca) with
  |0 -> ()
  |_ -> let l' = inverse_st lca in
       let s1' = inverse_st s1 in
       let s2' = inverse_st s2 in 
       lem_l2a_last'_base_pre lca s1 s2 last1 last2;
       lem_l2a_last'_base  l' s1' s2' last1 last2;
       lem_l2a_last'_base_ind lca s1 s2 last1 last2

let lem_l2a_last'_s10_s2_gt0 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    length (ops_of s2) > length (ops_of lca) /\
                    Add? (snd last2) /\ 
                    ((get_ele last1 <> get_ele last2) \/
                     (Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1)) /\
                    (let s2' = inverse_st s2 in
                    
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
         (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = ()

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (ensures (forall id. mem_id_s id (apply_log s l) ==> mem_id_s id s \/ mem_id id l))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_foldl (do s (head l)) (tail l)
 
let lem_l2a_last_help' (l:log) (last2:op_t)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Add? (snd last2) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 <> get_ele last2 /\
                    exists_triple last2 l'))
          (ensures exists_triple last2 l) 
          [SMTPat (let l', last1 = un_snoc l in
                   (exists_triple last2 l'))] =
  let l', last1 = un_snoc l in
  let pre', op', suf' = find_triple last2 l' in
  lemma_mem_snoc l' last1;
  assert (mem op' l);
  let pre, suf = pre_suf l op' in
  commu_seq_prop op' suf';
  
  assert ((snoc pre op') ++ suf = snoc ((snoc pre' op') ++ suf') last1);
  append_assoc (snoc pre' op') suf' (create 1 last1);
  assert ((snoc pre op') ++ suf = ((snoc pre' op') ++ (snoc suf' last1)));
  lem_suf_equal4 l op';
  distinct_invert_append l' (create 1 last1);
  lem_suf_equal4 l' op';

  not_mem_id l' last1;
  mem_ele_id op' l;
  mem_ele_id op' l';
  lem_id_not_snoc l' suf' last1 op'; 
  assert (not (mem_id (fst op') (snoc suf' last1)));
 
  count_1 l;
  assert (count_id (fst op') (snoc pre op' ++ suf) = 1);
  lem_count_1 pre suf pre' (snoc suf' last1) op';
  
  assert (length suf = length (snoc suf' last1));
  lemma_append_inj (snoc pre op') suf (snoc pre' op') (snoc suf' last1);
  assert (suf = snoc suf' last1);
  commu_seq_prop_l op' suf' last1;
  assert (commutative_seq op' suf); 
  ()
  
let rec lem_l2a_last'_s10 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Add? (snd last2) /\ 
                    ((get_ele last1 <> get_ele last2) \/
                     (Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last2 > fst last1)) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2)]) =
  if ops_of s2 = ops_of lca then
     lem_l2a_last'_base lca s1 s2 last1 last2
  else 
    (let s2' = inverse_st s2 in
     lem_l2a_last'_s10 lca s1 s2' last1 last2;
     lem_l2a_last'_s10_s2_gt0 lca s1 s2 last1 last2)

let lem_l2a_last'_s20_s1_gt0_l1_neq_help (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    Add? (snd last2) /\ 
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))))
          (ensures (let _, last1' = un_snoc (ops_of s1) in
                   ~ (Add? (snd last1') /\ get_ele last1' = get_ele last2 /\ fst last1' > fst last2) \/
                     (Rem? (snd last1') /\ get_ele last1' = get_ele last2))) = 
  let s1' = inverse_st s1 in
  let _, last1' = un_snoc (ops_of s1) in
  lemma_mem_snoc (ops_of s1') last1';
  assert (mem last1' (ops_of s1)); 
  lem_last (ops_of s1);
  assert (last (ops_of s1) = last1');
  lem_diff (ops_of s1) (ops_of lca);
  assert (last (diff (ops_of s1) (ops_of lca)) = last1');
  assert (mem last1' (diff (ops_of s1) (ops_of lca)));
  let pre, suf = pre_suf (diff (ops_of s1) (ops_of lca)) last1' in
  lem_lastop_suf_0 (diff (ops_of s1) (ops_of lca)) pre suf last1';
  assert (length suf = 0);
  lemma_empty suf; 
  comm_empty_log last1' suf; 
  assert (commutative_seq last1' suf);
  ()
  
let lem_l2a_last'_s20_s1_gt0_c1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    Add? (snd last2) /\ 
                    (get_ele last1 <> get_ele last2) /\
                    (let _, last1' = un_snoc (ops_of s1) in
                    (Rem? (snd last1') /\ get_ele last1' = get_ele last2)))
         (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = 
  lem_foldl init_st (ops_of lca); 
  assert (S.mem (fst last2, get_ele last2) (S.remove_if (do (v_of s2) last2) (fun e -> S.mem e (v_of lca)))); 
  let pre1, last1' = un_snoc (ops_of s1) in
  inverse_helper init_st pre1 last1'; 
  assert (not (mem_ele (get_ele last2) (v_of s1))); 
  assert (forall e. S.mem e (S.remove_if (v_of s1) (fun e -> S.mem e (v_of lca))) /\ snd e == get_ele last2 ==> fst last2 >= fst e);
  ()

let lem_l2a_last'_s20_s1_gt0_c2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    Add? (snd last2) /\ 
                    (get_ele last1 <> get_ele last2) /\
                    (let _, last1' = un_snoc (ops_of s1) in
                    (Add? (snd last1') /\ get_ele last1' = get_ele last2 /\ fst last1' <= fst last2)))
         (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = 
  lem_foldl init_st (ops_of lca); 
  assert (S.mem (fst last2, get_ele last2) (S.remove_if (do (v_of s2) last2) (fun e -> S.mem e (v_of lca)))); 
  let pre1, last1' = un_snoc (ops_of s1) in
  inverse_helper init_st pre1 last1'; 
  assert (forall e. S.mem e (S.remove_if (v_of s1) (fun e -> S.mem e (v_of lca))) /\ snd e == get_ele last2 ==> fst last2 >= fst e);
  ()
  
let lem_l2a_last'_s20_s1_gt0 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    Add? (snd last2) /\ 
                    (get_ele last1 <> get_ele last2) /\
                    (let _, last1' = un_snoc (ops_of s1) in
                    ~ (Add? (snd last1') /\ get_ele last1' = get_ele last2 /\ fst last1' > fst last2) \/
                     (Rem? (snd last1') /\ get_ele last1' = get_ele last2)) /\
                    (let s1' = inverse_st s1 in
                    is_prefix (ops_of lca) (ops_of s1') /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
         (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = 
  lem_foldl init_st (ops_of lca); 
  assert (S.mem (fst last2, get_ele last2) (S.remove_if (do (v_of s2) last2) (fun e -> S.mem e (v_of lca)))); 
  ()
 
let rec lem_l2a_last'_s20 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    Add? (snd last2) /\ 
                    (get_ele last1 <> get_ele last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1)]) = 
  if ops_of s1 = ops_of lca then
     lem_l2a_last'_base lca s1 s2 last1 last2
  else 
    (let s1' = inverse_st s1 in
     lem_inverse (ops_of lca) (ops_of s1);
     lem_l2a_last'_s20_s1_gt0_l1_neq_help lca s1 s2 last1 last2;
     let _, last1' = un_snoc (ops_of s1) in
     assert (~ (Add? (snd last1') /\ get_ele last1' = get_ele last2 /\ fst last1' > fst last2));
     if Rem? (snd last1') && get_ele last1' = get_ele last2 then
       lem_l2a_last'_s20_s1_gt0_c1 lca s1 s2 last1 last2
     else if Add? (snd last1') && get_ele last1' = get_ele last2 && fst last1' <= fst last2 then
       lem_l2a_last'_s20_s1_gt0_c2 lca s1 s2 last1 last2
     else 
       (assert (get_ele last1' <> get_ele last2);
       lem_diff (ops_of s1) (ops_of lca); 
       lem_suf_equal2_last (ops_of lca) (ops_of s1);
       assert (not (exists_triple last2 (diff (ops_of s1') (ops_of lca)))); 
       lem_l2a_last'_s20 lca s1' s2 last1 last2;
       lem_l2a_last'_s20_s1_gt0_l1_neq_help lca s1 s2 last1 last2;
       lem_l2a_last'_s20_s1_gt0 lca s1 s2 last1 last2))

let lem_l2a_last'_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires length (ops_of s2) > length (ops_of lca) /\
                    not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Add? (snd last2) /\
                    (get_ele last1 <> get_ele last2) /\
                    
                    (let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  ()
  
let rec lem_l2a_last' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires not (mem_id (fst last1) (ops_of lca)) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Add? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    (get_ele last1 <> get_ele last2))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2); length (ops_of s1)]) = 
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
     lem_l2a_last'_base lca s1 s2 last1 last2
  else if ops_of s2 = ops_of lca then
     lem_l2a_last'_s20 lca s1 s2 last1 last2
  else (let s2' = inverse_st s2 in
        lem_inverse (ops_of lca) (ops_of s2); 
        lem_l2a_last' lca s1 s2' last1 last2;
        lem_l2a_last'_ind lca s1 s2 last1 last2)

let not_add_eq_lt (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    Add? (snd last2) /\ 
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                   ~ (Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last1 < fst last2))) = 
  let s2' = inverse_st s2 in
  let _, last2 = un_snoc (ops_of s2) in
  lemma_mem_snoc (ops_of s2') last2;
  assert (mem last2 (ops_of s2)); 
  lem_last (ops_of s2);
  assert (last (ops_of s2) = last2); 
  lem_diff (ops_of s2) (ops_of lca);
  assert (last (diff (ops_of s2) (ops_of lca)) = last2);
  assert (mem last2 (diff (ops_of s2) (ops_of lca)));
  let pre, suf = pre_suf (diff (ops_of s2) (ops_of lca)) last2 in
  lem_lastop_suf_0 (diff (ops_of s2) (ops_of lca)) pre suf last2;
  assert (length suf = 0);
  lemma_empty suf; 
  comm_empty_log last2 suf; 
  assert (commutative_seq last2 suf); 
  ()
  
let lem_l2a_last (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Add? (snd last2) /\
                     ((get_ele last1 <> get_ele last2) \/
                      (Add? (snd last1) /\ get_ele last1 = get_ele last2 /\ fst last1 < fst last2)) /\
                      
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  lem_diff (ops_of s1) (ops_of lca); 
  lem_diff (ops_of s2) (ops_of lca);
  lem_suf_equal2_last (ops_of lca) (ops_of s1); 
  lem_suf_equal2_last (ops_of lca) (ops_of s2); 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  let s2' = inverse_st s2 in
  let s1' = inverse_st s1 in
  lem_inverse (ops_of lca) (ops_of s1);
  lem_inverse (ops_of lca) (ops_of s2);
  not_add_eq_lt lca s1 s2;
  lem_l2a_last' lca s1' s2' last1 last2
  
/////////////////////////////////////////

let lem_exists (lastop:op_t) (l:log)
  : Lemma (ensures exists_triple lastop l <==>
                   ((Rem? (snd lastop) /\
                     (exists op. mem op l /\ Add? (snd op) /\ get_ele op = get_ele lastop /\ fst op <> fst lastop /\
                     (let _, suf = pre_suf l op in
                     commutative_seq op suf))) \/
                  
                   (Add? (snd lastop) /\
                     (exists (op:op_t). mem op l /\ Add? (snd op) /\ get_ele op = get_ele lastop /\ fst op > fst lastop /\
                     (let _, suf = pre_suf l op in
                     commutative_seq op suf))))) = ()

let linearizable_gt0_s2'_op (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\
                     (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                      suf2 = snd (pre_suf (ops_of s2) op2))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let s2' = inverse_st_op s2 op2 in
                       eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) op2)
                          (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') op2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let pre2, op2, suf2 = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  let s2' = inverse_st_op s2 op2 in
  lem_exists last1 (diff (ops_of s2) (ops_of lca));
  lem_inverse (ops_of lca) (ops_of s1);
  lem_diff (ops_of s1) (ops_of lca);
  lem_suf_equal2_last (ops_of lca) (ops_of s1);
  lem_diff (ops_of s2) (ops_of lca);
  lem_suf_equal2 (ops_of lca) (ops_of s2) op2;
  lem_inverse_op (ops_of lca) (ops_of s2) op2;
  lem_l2a'' lca (inverse_st s1) s2' last1 op2

let linearizable_gt0_s1'_op (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     exists_triple last2 (diff (ops_of s1) (ops_of lca)) /\
                     (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                      suf1 = snd (pre_suf (ops_of s1) op1))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let (pre1, op1, suf2) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    let s1' = inverse_st_op s1 op1 in
                       eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) op1)
                          (concrete_merge (v_of lca) (do (v_of s1') op1) (v_of s2)))) =
  let _, last2 = un_snoc (ops_of s2) in
  let pre1, op1, suf1 = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  let s1' = inverse_st_op s1 op1 in
  lem_exists last2 (diff (ops_of s1) (ops_of lca));
  lem_inverse (ops_of lca) (ops_of s2);
  lem_diff (ops_of s2) (ops_of lca);
  lem_suf_equal2_last (ops_of lca) (ops_of s2);
  lem_diff (ops_of s1) (ops_of lca);
  lem_suf_equal2 (ops_of lca) (ops_of s1) op1;
  lem_inverse_op (ops_of lca) (ops_of s1) op1;
  lem_l1a'' lca s1' (inverse_st s2) op1 last2

let linearizable_gt0_s1' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last1 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  resolve_conflict_prop last1 last2;
  assert ((Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2) \/
          (Add? (snd last1) /\ Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2)); 
  if Rem? (snd last1) then ()
    else (assert (Add? (snd last1)); 
          rem_add_lastop_neq_ele lca s1 s2;
          assert (~ (Rem? (snd last2) /\ get_ele last1 = get_ele last2));
          assert (~ (Add? (snd last2) /\ get_ele last1 = get_ele last2 /\ fst last1 > fst last2)); ()); 
  assert (~ (Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 = get_ele last2));
  ()

let linearizable_gt0_s2' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) <> last1 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  resolve_conflict_prop last1 last2;
  assert (last (resolve_conflict last1 last2) = last2);
  if Add? (snd last2) then
    (rem_add_lastop_neq_ele' lca s1 s2; 
     lem_l2a_last lca s1 s2)
  else lem_l2r lca s1 s2
  
/////////////////////////////////////////


////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
let concrete_st_s = S.set nat

// init state 
let init_st_s = S.empty
 
// apply an operation to a state 
let do_s (st_s:concrete_st_s) (o:op_t) : concrete_st_s =
  match snd o with
  |(Add e) -> S.union (S.singleton e) st_s
  |(Rem e) -> S.remove_if st_s (fun ele -> ele = e) 

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  (forall e. S.mem e st_s <==> mem_ele e st)

//initial states are equivalent
let initial_eq (_:unit) 
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////
