module Framework_comm

open FStar.Seq
open App_comm
open FStar.Ghost

#set-options "--query_stats"

#push-options "--z3rlimit 500"
let linearizable_s1_01 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1))
          (ensures (exists l. interleaving_predicate l lca s1 s2)) =
  split_prefix init_st (ops_of lca) (ops_of s2);
  linearizable_s1_0 lca s1 s2

let linearizable_s2_01 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1))
          (ensures (exists l. interleaving_predicate l lca s1 s2)) =
  split_prefix init_st (ops_of lca) (ops_of s1);
  linearizable_s2_0 lca s1 s2

let interleaving_helper_inv2_comm (lca s1 s2 l':log)
  : Lemma
      (requires (*Seq.length s1 > 0 /\*) is_prefix lca s1 /\ is_prefix lca s2 /\
                Seq.length (diff s1 lca) > 0 /\ Seq.length (diff s2 lca) > 0 /\
                exists_triple (snd (un_snoc s1)) (diff s2 lca) /\
                (let (pre2, op2, suf2) = find_triple (snd (un_snoc s1)) (diff s2 lca) in
                is_interleaving l' (diff s1 lca) (pre2 ++ suf2)))
      (ensures (let (_, op2, _) = find_triple (snd (un_snoc s1)) (diff s2 lca) in
                is_interleaving (Seq.snoc l' op2) (diff s1 lca) (diff s2 lca)))
  = let (_, op2, _) = find_triple (snd (un_snoc (diff s1 lca))) (diff s2 lca) in
    let l = Seq.snoc l' op2 in
    ()

let interleaving_helper_inv1_comm (lca s1 s2 l':log)
  : Lemma
      (requires (*Seq.length s2 > 0 /\*) is_prefix lca s1 /\ is_prefix lca s2 /\
                Seq.length (diff s1 lca) > 0 /\ Seq.length (diff s2 lca) > 0 /\
                not (exists_triple (snd (un_snoc s1)) (diff s2 lca)) /\
                exists_triple (snd (un_snoc s2)) (diff s1 lca) /\
                (let (pre1, op1, suf1) = find_triple (snd (un_snoc s2)) (diff s1 lca) in
                is_interleaving l' (pre1 ++ suf1) (diff s2 lca)))
      (ensures (let (_, op1, _) = find_triple (snd (un_snoc s2)) (diff s1 lca) in
                is_interleaving (Seq.snoc l' op1) (diff s1 lca) (diff s2 lca)))
  = let (_, op1, _) = find_triple (snd (un_snoc (diff s2 lca))) (diff s1 lca) in
    let l = Seq.snoc l' op1 in
    ()
 
let interleaving_helper_inv1 (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s1 > 0 /\ is_prefix lca s1 /\ is_prefix lca s2 /\
                Seq.length (diff s1 lca) > 0 /\ Seq.length (diff s2 lca) > 0 /\
                not (exists_triple (snd (un_snoc s1)) (diff s2 lca)) /\
                not (exists_triple (snd (un_snoc s2)) (diff s1 lca)) /\
                is_interleaving l' (diff (fst (Seq.un_snoc s1)) lca) (diff s2 lca))
      (ensures (let _, last1 = un_snoc s1 in
                is_interleaving (Seq.snoc l' last1) (diff s1 lca) (diff s2 lca)))
  = let prefix1, last1 = Seq.un_snoc (diff s1 lca) in
    let l = Seq.snoc l' last1 in
    introduce exists l'. is_interleaving l' prefix1 (diff s2 lca) /\
                    l = Seq.snoc l' last1
    with l'
    and ()
    
let interleaving_helper_inv2 (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s2 > 0 /\ is_prefix lca s1 /\ is_prefix lca s2 /\
                Seq.length (diff s1 lca) > 0 /\ Seq.length (diff s2 lca) > 0 /\
                not (exists_triple (snd (un_snoc s1)) (diff s2 lca)) /\
                not (exists_triple (snd (un_snoc s2)) (diff s1 lca)) /\
                is_interleaving l' (diff s1 lca) (diff (fst (Seq.un_snoc s2)) lca))
      (ensures (let _, last2 = un_snoc s2 in
                is_interleaving (Seq.snoc l' last2) (diff s1 lca) (diff s2 lca)))
  = let prefix2, last2 = Seq.un_snoc (diff s2 lca) in
    let l = Seq.snoc l' last2 in
    introduce exists l'. is_interleaving l' (diff s1 lca) prefix2 /\
                    l = Seq.snoc l' last2
    with l'
    and ()

// taking inverse on any one branch and applying the operation again is equivalent to
// concrete merge
let linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     
                     (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                       (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                        suf2 = snd (pre_suf (ops_of s2) op2))) /\

                      ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                        exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                          (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                           suf1 = snd (pre_suf (ops_of s1) op1))) /\

                     ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                         fst last1 <> fst last2 /\
                         (last (resolve_conflict last1 last2) = last1 ==>
                          is_prefix (ops_of lca) (ops_of (inverse_st s1))) /\
                           
                         (last (resolve_conflict last1 last2) <> last1 ==>
                          is_prefix (ops_of lca) (ops_of (inverse_st s2))))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                       (let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                       (let s2' = inverse_st_op s2 op2 in

                        // eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) op2)
                          //  (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) /\
                      
                       eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) op2)
                          (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') op2))))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                       (let (pre1, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                       (let s1' = inverse_st_op s1 op1 in                    
                       eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) op1)
                          (concrete_merge (v_of lca) (do (v_of s1') op1) (v_of s2))))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                    
                    (last (resolve_conflict last1 last2) = last1 ==>                    
                      eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))) /\                                  
                   
                    (last (resolve_conflict last1 last2) <> last1 ==>                   
                      eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2)))))) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  if exists_triple last1 (diff (ops_of s2) (ops_of lca)) then
     linearizable_gt0_s1'_op lca s1 s2
  else if not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) &&
          exists_triple last2 (diff (ops_of s1) (ops_of lca)) then
     linearizable_gt0_s2'_op lca s1 s2
  else if not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) &&
          not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) &&
          last (resolve_conflict last1 last2) = last1 then
     linearizable_gt0_s1' lca s1 s2
  else linearizable_gt0_s2' lca s1 s2

#push-options "--z3rlimit 500"
let interleaving_s1_inv (lca s1 s2:st) (l':log)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    not (exists_triple (snd (un_snoc (ops_of s1))) (diff (ops_of s2) (ops_of lca))) /\
                    not (exists_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca))) /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    interleaving_predicate l' lca (inverse_st s1) s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let l = Seq.snoc l' last1 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) =

  let _, last1 = un_snoc (ops_of s1) in
  let l = Seq.snoc l' last1 in
  interleaving_helper_inv1 (ops_of lca) (ops_of s1) (ops_of s2) l'; 
  linearizable_gt0 lca s1 s2;
  lem_do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) (seq_foldl (v_of lca) l') last1;
  inverse_helper (v_of lca) l' last1;
  eq_is_equiv (seq_foldl (v_of lca) l) (do (seq_foldl (v_of lca) l') last1);
  transitive (seq_foldl (v_of lca) l) (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  assert (interleaving_predicate l lca s1 s2); ()

let interleaving_s2_inv (lca s1 s2:st) (l':log)
  : Lemma (requires common_pre lca s1 s2 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    not (exists_triple (snd (un_snoc (ops_of s1))) (diff (ops_of s2) (ops_of lca))) /\
                    not (exists_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca))) /\
                    interleaving_predicate l' lca s1 (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) <> last1))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let l = Seq.snoc l' last2 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) =
  let _, last2 = un_snoc (ops_of s2) in
  let l = Seq.snoc l' last2 in
  interleaving_helper_inv2 (ops_of lca) (ops_of s1) (ops_of s2) l'; 
  linearizable_gt0 lca s1 s2;
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) (seq_foldl (v_of lca) l') last2;
  inverse_helper (v_of lca) l' last2;
  eq_is_equiv (seq_foldl (v_of lca) l) (do (seq_foldl (v_of lca) l') last2);
  transitive (seq_foldl (v_of lca) l) (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  assert (interleaving_predicate l lca s1 s2); ()

let rec lem_app (l a b:log)
  : Lemma (requires l ++ a = l ++ b)
          (ensures a = b) (decreases length l) =
  match length l with
  |0 -> lemma_empty l; append_empty_l a; append_empty_l b
  |_ -> lemma_append_cons l a; 
       lemma_append_cons l b;
       lemma_cons_inj (head l) (head l) (tail l ++ a) (tail l ++ b);
       lem_app (tail l) a b

let interleaving_s2_inv_comm (lca s1 s2:st) (l':log)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                    exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\
                    (let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                     lem_suf_equal (ops_of lca) (ops_of s2) op2;
                  
                    (let inv2 = inverse_st_op s2 op2 in
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    interleaving_predicate l' lca s1 inv2))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let l = Seq.snoc l' op2 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in 
  lem_suf_equal (ops_of lca) (ops_of s2) op2;
  lem_inverse_op (ops_of lca) (ops_of s2) op2; 
  let inv2 = inverse_st_op s2 op2 in
  lem_diff (ops_of inv2) (ops_of lca);
  lem_app (ops_of lca) (pre2 ++ suf2) (diff (ops_of inv2) (ops_of lca));
  let l = Seq.snoc l' op2 in 
  lem_diff (ops_of s1) (ops_of lca); 
  lem_diff (ops_of s2) (ops_of lca);
  interleaving_helper_inv2_comm (ops_of lca) (ops_of s1) (ops_of s2) l';
  assert (is_interleaving l (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)));
  linearizable_gt0 lca s1 s2;
  lem_trans_merge_s2' (v_of lca) (v_of s1) (do (v_of inv2) op2) (v_of s2);  
  transitive (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)
             (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) op2))
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) (seq_foldl (v_of lca) l') op2;
  symmetric (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)
            (do (seq_foldl (v_of lca) l') op2);
  inverse_helper (v_of lca) l' op2; 
  eq_is_equiv (seq_foldl (v_of lca) l) (do (seq_foldl (v_of lca) l') op2);
  transitive (seq_foldl (v_of lca) l)
             (do (seq_foldl (v_of lca) l') op2)
             (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2); 
  transitive (seq_foldl (v_of lca) l) (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  assert (interleaving_predicate l lca s1 s2); ()           

let interleaving_s1_inv_comm (lca s1 s2:st) (l':log)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                    exists_triple last2 (diff (ops_of s1) (ops_of lca)) /\
                    (let (pre1, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    lem_suf_equal (ops_of lca) (ops_of s1) op1;
                    
                    (let inv1 = inverse_st_op s1 op1 in
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    interleaving_predicate l' lca inv1 s2))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    let l = Seq.snoc l' op1 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) =
  let _, last2 = un_snoc (ops_of s2) in
  let (pre1, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in 
  lem_suf_equal (ops_of lca) (ops_of s1) op1;
  lem_inverse_op (ops_of lca) (ops_of s1) op1; 
  let inv1 = inverse_st_op s1 op1 in
  lem_diff (ops_of inv1) (ops_of lca);
  lem_app (ops_of lca) (pre1 ++ suf1) (diff (ops_of inv1) (ops_of lca));
  let l = Seq.snoc l' op1 in 
  lem_diff (ops_of s1) (ops_of lca); 
  lem_diff (ops_of s2) (ops_of lca);
  interleaving_helper_inv1_comm (ops_of lca) (ops_of s1) (ops_of s2) l';
  assert (is_interleaving l (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)));
  linearizable_gt0 lca s1 s2;
  assert (eq (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
             (concrete_merge (v_of lca) (do (v_of inv1) op1) (v_of s2)));
  lem_trans_merge_s1' (v_of lca) (do (v_of inv1) op1) (v_of s2) (v_of s1);  
  transitive (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
             (concrete_merge (v_of lca) (do (v_of inv1) op1) (v_of s2))
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  lem_do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) (seq_foldl (v_of lca) l') op1;
  symmetric (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
            (do (seq_foldl (v_of lca) l') op1);
  inverse_helper (v_of lca) l' op1; 
  eq_is_equiv (seq_foldl (v_of lca) l) (do (seq_foldl (v_of lca) l') op1);
  transitive (seq_foldl (v_of lca) l)
             (do (seq_foldl (v_of lca) l') op1)
             (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1); 
  transitive (seq_foldl (v_of lca) l) (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  assert (interleaving_predicate l lca s1 s2); () 
#pop-options

#push-options "--z3rlimit 500"
let linearizable_s1_gt0_pre (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last1))
          (ensures (let inv1 = inverse_st s1 in 
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))) =
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s1);
  inverse_diff_id (ops_of lca) (ops_of s1) (ops_of s2)

let linearizable_s2_gt0_pre (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple (snd (un_snoc (ops_of s1))) (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) <> last1))
          (ensures (let inv2 = inverse_st s2 in 
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca)))))) =
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2);
  inverse_diff_id1 (ops_of lca) (ops_of s1) (ops_of s2)

let linearizable_s2_gt0_pre_comm (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    exists_triple last1 (diff (ops_of s2) (ops_of lca))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in 
                    suf2 = snd (pre_suf (ops_of s2) op2) /\
                    (let inv2 = inverse_st_op s2 op2 in 
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca))))))))
  = admit();let _, last1 = un_snoc (ops_of s1) in
    let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in 
    lem_suf_equal (ops_of lca) (ops_of s2) op2;
    let inv2 = inverse_st_op s2 op2 in
    lem_inverse_op (ops_of lca) (ops_of s2) op2;
    assume (is_prefix (ops_of lca) (ops_of inv2)); 
    lem_diff (ops_of inv2) (ops_of lca); 
    assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1); admit();
    assert (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca))));
    ()

let linearizable_s1_gt0_pre_comm (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                    exists_triple last2 (diff (ops_of s1) (ops_of lca))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in 
                    suf1 = snd (pre_suf (ops_of s1) op1) /\
                    (let inv1 = inverse_st_op s1 op1 in 
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))))) 
  = admit();let _, last2 = un_snoc (ops_of s2) in
    let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in 
    lem_suf_equal (ops_of lca) (ops_of s1) op1;
    let inv1 = inverse_st_op s1 op1 in
    lem_inverse_op (ops_of lca) (ops_of s1) op1;
    assert (is_prefix (ops_of lca) (ops_of inv1));
    lem_diff (ops_of inv1) (ops_of lca); 
    assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1);
    assert (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))));
    ()
#pop-options


#set-options "--z3rlimit 2000 --fuel 1 --ifuel 1"
let rec linearizable (lca s1 s2:st)
  : Lemma 
      (requires 
         is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2) /\
         (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
         (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
         (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
      (ensures 
         (exists l. interleaving_predicate l lca s1 s2))
      (decreases %[Seq.length (ops_of s2); Seq.length (ops_of s1)])

  = if ops_of s1 = ops_of lca 
    then begin
      linearizable_s1_01 lca s1 s2
    end
    else 
    if ops_of s2 = ops_of lca
    then begin
      linearizable_s2_01 lca s1 s2
    end
    else begin 
        assert (Seq.length (ops_of s1) > Seq.length (ops_of lca)); 
        assert (Seq.length (ops_of s2) > Seq.length (ops_of lca));
        let _, last1 = un_snoc (ops_of s1) in
        let _, last2 = un_snoc (ops_of s2) in
        lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
        assert (fst last1 <> fst last2);
        let inv1 = inverse_st s1 in 
        let inv2 = inverse_st s2 in 

        if exists_triple last1 (diff (ops_of s2) (ops_of lca)) then
        begin
          let pre2, op2, suf2 = find_triple (snd (un_snoc (ops_of s1))) (diff (ops_of s2) (ops_of lca)) in
          lem_suf_equal (ops_of lca) (ops_of s2) op2; 
          let s2' = inverse_st_op s2 op2 in 
          assert (length (ops_of s2') = length (ops_of s2) - 1);
          linearizable_s2_gt0_pre_comm lca s1 s2;
          assert ((ops_of s2) == ((Seq.snoc pre2 op2) ++ suf2));
          assert (ops_of s2' == pre2 ++ suf2);
          linearizable lca s1 s2';
          eliminate exists l'. interleaving_predicate l' lca s1 s2'
          returns exists l. interleaving_predicate l lca s1 s2
          with _. begin
            let l = Seq.snoc l' op2 in
            introduce exists l. interleaving_predicate l lca s1 s2
            with l
            and begin 
              interleaving_s2_inv_comm lca s1 s2 l'
            end
          end
         end

        else if not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) &&
                exists_triple last2 (diff (ops_of s1) (ops_of lca)) then
        begin 
          let pre1, op1, suf1 = find_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca)) in
          lem_suf_equal (ops_of lca) (ops_of s1) op1; 
          let s1' = inverse_st_op s1 op1 in 
          assert (length (ops_of s1') = length (ops_of s1) - 1);
          linearizable_s2_gt0_pre_comm lca s1 s2;
          assert ((ops_of s1) == ((Seq.snoc pre1 op1) ++ suf1));
          assert (ops_of s1' == pre1 ++ suf1);
          linearizable lca s1' s2;
          eliminate exists l'. interleaving_predicate l' lca s1' s2
          returns exists l. interleaving_predicate l lca s1 s2
          with _. begin
            let l = Seq.snoc l' op1 in
            introduce exists l. interleaving_predicate l lca s1 s2
            with l
            and begin 
              interleaving_s1_inv_comm lca s1 s2 l'
            end
          end
        end

        else if not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) &&
                not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) &&
                last (resolve_conflict last1 last2) = last1 then
        begin 
          linearizable_s1_gt0_pre lca s1 s2;
          linearizable lca inv1 s2;
          eliminate exists l'. interleaving_predicate l' lca inv1 s2
          returns exists l. interleaving_predicate l lca s1 s2
          with _. begin
            let l = Seq.snoc l' last1 in
            introduce exists l. interleaving_predicate l lca s1 s2
            with l
            and begin
              interleaving_s1_inv lca s1 s2 l'
            end
          end
        end
        
        else 
        begin 
          assert (last (resolve_conflict last1 last2) <> last1);
          linearizable_s2_gt0_pre lca s1 s2;
          linearizable lca s1 inv2;
          eliminate exists l'. interleaving_predicate l' lca s1 inv2
          returns exists l. interleaving_predicate l lca s1 s2
          with _. begin
            let l = Seq.snoc l' last2 in
            introduce exists l. interleaving_predicate l lca s1 s2
            with l
            and begin
              interleaving_s2_inv lca s1 s2 l'
            end
          end
        end
      end
