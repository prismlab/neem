module Framework

open FStar.Seq
open App
open Utils

#set-options "--query_stats"

// l is interleaving of l1 and l2
let rec is_interleaving (l l1 l2:log)
  : Tot eqtype (decreases %[Seq.length l1; Seq.length l2]) =

  // if l1 is empty, then l == l2
  (Seq.length l1 = 0 ==> l == l2)

  /\

  // similarly for l2 being empty
  ((Seq.length l1 > 0  /\ Seq.length l2 == 0) ==> l == l1)

  /\

  // if both are non-empty and lengths > 1
  // then three cases
  ((Seq.length l1 > 0 /\ Seq.length l2 > 0) ==>

   (let prefix1, last1 = un_snoc l1 in
    let prefix2, last2 = un_snoc l2 in

    (exists l'.
          is_interleaving l' prefix1 prefix2 /\
          fst last1 <> fst last2 /\
          l == l' ++ (resolve_conflict last1 last2))

    \/

    (exists l'.
          is_interleaving l' l1 prefix2 /\
          l == Seq.snoc l' last2)

    \/

    (exists l'.
          is_interleaving l' prefix1 l2 /\
          l == Seq.snoc l' last1)))

let interleaving_predicate (l:log) (lca s1:st)
  (s2:st{concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
         is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2)}) =
  is_interleaving l (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) /\
  eq (apply_log (v_of lca) l)
     (concrete_merge (v_of lca) (v_of s1) (v_of s2))

#push-options "--z3rlimit 500"
let rec linearizable_s1_0''_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    fst last2 > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))
          (decreases %[length (ops_of lca)]) =
  if length (ops_of lca) = 0 then
    linearizable_s1_0''_base_base lca s1 s2' last2
  else 
    (let l' = inverse_st lca in
     let s1' = inverse_st s1 in
     let s2'' = inverse_st s2' in
     linearizable_s1_0''_base_pre lca s1 s2' last2;
     linearizable_s1_0''_base l' s1' s2'' last2;
     linearizable_s1_0''_base_ind lca s1 s2' last2)

let rec linearizable_s1_0'' (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\
                    fst last2 > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))
          (decreases %[length (ops_of s2')]) =
  if ops_of s2' = ops_of lca then
    linearizable_s1_0''_base lca s1 s2' last2
  else 
    (let inv2 = inverse_st s2' in
    lem_inverse (ops_of lca) (ops_of s2');
    lastop_diff (ops_of lca) (ops_of s2');
    inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2');
    linearizable_s1_0''_pre lca s1 s2' last2;
    linearizable_s1_0'' lca s1 (inverse_st s2') last2;
    linearizable_s1_0''_ind lca s1 s2' last2)
    
let linearizable_s1_0' (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = 
  let pre2, last2 = un_snoc (ops_of s2) in
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2);
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  assert (is_prefix (ops_of lca) (snoc (ops_of (inverse_st s2)) last2));
  lemma_mem_snoc pre2 last2; 
  assert (mem last2 (ops_of s2));
  mem_ele_id last2 (ops_of s2);
  assert (mem_id (fst last2) (ops_of s2));
  assert (fst last2 > 0);
  lem_diff (ops_of s2) (ops_of lca);
  linearizable_s1_0'' lca s1 (inverse_st s2) last2

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures (exists l. interleaving_predicate l lca s1 s2)) =
  split_prefix init_st (ops_of lca) (ops_of s2);
  if ops_of s2 = ops_of lca then
    linearizable_s1_0_s2_0_base lca s1 s2 
  else linearizable_s1_0' lca s1 s2

let rec linearizable_s2_0''_base (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2))
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)))
          (decreases %[length (ops_of lca)]) =
  if length (ops_of lca) = 0 then
    linearizable_s2_0''_base_base lca s1' s2 last1
  else 
    (let l' = inverse_st lca in
     let s1'' = inverse_st s1' in
     let s2' = inverse_st s2 in
     linearizable_s2_0''_base_pre lca s1' s2 last1;
     linearizable_s2_0''_base l' s1'' s2' last1; 
     linearizable_s2_0''_base_ind lca s1' s2 last1)

let rec linearizable_s2_0'' (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s2 = ops_of lca /\
                    fst last1 > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2))
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)))
          (decreases %[length (ops_of s1')]) =
  if ops_of s1' = ops_of lca then
    linearizable_s2_0''_base lca s1' s2 last1
  else 
    (let inv1 = inverse_st s1' in
    lem_inverse (ops_of lca) (ops_of s1');
    lastop_diff (ops_of lca) (ops_of s1');
    inverse_diff_id_s1' (ops_of lca) (ops_of s1') (ops_of s2);
    linearizable_s2_0''_pre lca s1' s2 last1;
    linearizable_s2_0'' lca (inverse_st s1') s2 last1;
    linearizable_s2_0''_ind lca s1' s2 last1)
    
let linearizable_s2_0' (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca /\
                    length (ops_of s1) > length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) =
  let pre1, last1 = un_snoc (ops_of s1) in
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s1);
  inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
  assert (is_prefix (ops_of lca) (snoc (ops_of (inverse_st s1)) last1));
  lemma_mem_snoc pre1 last1; 
  assert (mem last1 (ops_of s1));
  mem_ele_id last1 (ops_of s1);
  assert (mem_id (fst last1) (ops_of s1));
  assert (fst last1 > 0);
  lem_diff (ops_of s1) (ops_of lca);
  linearizable_s2_0'' lca (inverse_st s1) s2 last1

let linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures (exists l. interleaving_predicate l lca s1 s2)) =
  split_prefix init_st (ops_of lca) (ops_of s1);
  if ops_of s1 = ops_of lca then
    linearizable_s1_0_s2_0_base lca s1 s2 
  else linearizable_s2_0' lca s1 s2

let rec linearizable_gt0_s2'_s10 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases  %[length (ops_of s2)]) =
  if ops_of s2 = ops_of lca then
     linearizable_gt0_base lca s1 s2 last1 last2
  else 
    (let s2' = inverse_st s2 in
     lem_inverse (ops_of lca) (ops_of s2);
     lastop_diff (ops_of lca) (ops_of s2);
     inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
     linearizable_gt0_s2'_s10_pre lca s1 s2 last1 last2;
     linearizable_gt0_s2'_s10 lca s1 s2' last1 last2;
     linearizable_gt0_ind lca s1 s2 last1 last2)

let rec linearizable_gt0_s2' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\ 
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1); length (ops_of s2)]) = 
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    linearizable_gt0_base lca s1 s2 last1 last2 
  else if ops_of s1 = ops_of lca then
    linearizable_gt0_s2'_s10 lca s1 s2 last1 last2 
  else (let s1' = inverse_st s1 in
        lem_inverse (ops_of lca) (ops_of s1);
        lastop_diff (ops_of lca) (ops_of s1);
        inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
        linearizable_gt0_s2'_pre lca s1 s2 last1 last2;
        linearizable_gt0_s2' lca s1' s2 last1 last2;
        linearizable_gt0_ind1 lca s1 s2 last1 last2)  

let linearizable_gt0_s2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  assert (v_of s2 == do (v_of (inverse_st s2)) last2);
  assert (v_of s1 == do (v_of (inverse_st s1)) last1);
  lem_inverse (ops_of lca) (ops_of s2);
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s1);
  inverse_diff_id_s1'_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  linearizable_gt0_s2' lca (inverse_st s1) (inverse_st s2) last1 last2

let rec linearizable_gt0_s1'_s20 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases  %[length (ops_of s1)]) =
  if ops_of s1 = ops_of lca then
     linearizable_gt0_base lca s1 s2 last1 last2
  else 
    (let s1' = inverse_st s1 in
     lem_inverse (ops_of lca) (ops_of s1);
     lastop_diff (ops_of lca) (ops_of s1);
     inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
     linearizable_gt0_s1'_s20_pre lca s1 s2 last1 last2;
     linearizable_gt0_s1'_s20 lca s1' s2 last1 last2;
     linearizable_gt0_ind1 lca s1 s2 last1 last2)

let rec linearizable_gt0_s1' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2); length (ops_of s1)]) =
   if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    linearizable_gt0_base lca s1 s2 last1 last2 
  else if ops_of s2 = ops_of lca then
    linearizable_gt0_s1'_s20 lca s1 s2 last1 last2 
  else (let s2' = inverse_st s2 in
        lem_inverse (ops_of lca) (ops_of s2);
        lastop_diff (ops_of lca) (ops_of s2);
        inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
        linearizable_gt0_s1'_pre lca s1 s2 last1 last2;
        linearizable_gt0_s1' lca s1 s2' last1 last2;
        linearizable_gt0_ind lca s1 s2 last1 last2) 

let linearizable_gt0_s1 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  assert (v_of s2 == do (v_of (inverse_st s2)) last2);
  assert (v_of s1 == do (v_of (inverse_st s1)) last1);
  lem_inverse (ops_of lca) (ops_of s2);
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s1);
  inverse_diff_id_s1'_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  linearizable_gt0_s1' lca (inverse_st s1) (inverse_st s2) last1 last2

let linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    (last (resolve_conflict last1 last2) = last1 ==>
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\

                    (last (resolve_conflict last1 last2) <> last1 ==>
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (last (resolve_conflict last1 last2) = last1 ==>
                     eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                        (concrete_merge (v_of lca) (v_of s1) (v_of s2))) /\
                 
                    (last (resolve_conflict last1 last2) <> last1 ==>
                     eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                        (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  if last (resolve_conflict last1 last2) = last1 then
    linearizable_gt0_s1 lca s1 s2
  else linearizable_gt0_s2 lca s1 s2

let interleaving_helper_inv1 (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s1 > 0 /\
                is_prefix lca (fst (Seq.un_snoc s1)) /\ is_prefix lca s2 /\
                is_interleaving l' (diff (fst (Seq.un_snoc s1)) lca) (diff s2 lca))
      (ensures (let _, last1 = un_snoc s1 in
                is_interleaving (Seq.snoc l' last1) (diff s1 lca) (diff s2 lca)))
  = assert (is_interleaving l' (fst (Seq.un_snoc (diff s1 lca))) (diff s2 lca));
    let prefix1, last1 = Seq.un_snoc (diff s1 lca) in
    let l = Seq.snoc l' last1 in
    assert (is_interleaving l (diff s1 lca) (diff s2 lca)); ()

let interleaving_helper_inv2 (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s2 > 0 /\
                is_prefix lca (fst (Seq.un_snoc s2)) /\ is_prefix lca s1 /\
                is_interleaving l' (diff s1 lca) (diff (fst (Seq.un_snoc s2)) lca))
      (ensures (let _, last2 = un_snoc s2 in
                is_interleaving (Seq.snoc l' last2) (diff s1 lca) (diff s2 lca)))
  = assert (is_interleaving l' (diff s1 lca) (fst (Seq.un_snoc (diff s2 lca))));
    let prefix2, last2 = Seq.un_snoc (diff s2 lca) in
    let l = Seq.snoc l' last2 in
    assert (is_interleaving l (diff s1 lca) (diff s2 lca)); ()

let interleaving_s1_inv (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                    interleaving_predicate l' lca (inverse_st s1) s2 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
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
  symmetric (apply_log (v_of lca) l')
            (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2));
  lem_do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) (apply_log (v_of lca) l') last1; 
  symmetric (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1) (do (apply_log (v_of lca) l') last1);
  inverse_helper (v_of lca) l' last1;
  eq_is_equiv (apply_log (v_of lca) l) (do (apply_log (v_of lca) l') last1); 
  transitive (apply_log (v_of lca) l) (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))

let interleaving_s2_inv (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    interleaving_predicate l' lca s1 (inverse_st s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
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
  symmetric (apply_log (v_of lca) l')
            (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2)));
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) (apply_log (v_of lca) l') last2;
  symmetric (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2) (do (apply_log (v_of lca) l') last2);
  inverse_helper (v_of lca) l' last2;
  eq_is_equiv (apply_log (v_of lca) l) (do (apply_log (v_of lca) l') last2);
  transitive (apply_log (v_of lca) l) (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))

let linearizable_s1_gt0_pre (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last1))
          (ensures (let inv1 = inverse_st s1 in 
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))) =
  let inv1 = inverse_st s1 in 
  lem_inverse (ops_of lca) (ops_of s1);
  lemma_split (ops_of inv1) (Seq.length (ops_of lca));
  lem_diff (ops_of inv1) (ops_of lca); 
  lem_diff (ops_of s1) (ops_of lca)

let linearizable_s2_gt0_pre (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) <> last1))
          (ensures (let inv2 = inverse_st s2 in 
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca)))))) =
  let inv2 = inverse_st s2 in 
  lem_inverse (ops_of lca) (ops_of s2);
  lemma_split (ops_of inv2) (Seq.length (ops_of lca));
  lem_diff (ops_of inv2) (ops_of lca); 
  lem_diff (ops_of s2) (ops_of lca)

let rec linearizable (lca s1 s2:st)
  : Lemma 
      (requires 
         is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2) /\
         (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
         (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
         (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
         concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
      (ensures 
         (exists l. interleaving_predicate l lca s1 s2))
      (decreases %[Seq.length (ops_of s1); Seq.length (ops_of s2)])

  = if ops_of s1 = ops_of lca 
    then begin
      linearizable_s1_0 lca s1 s2
    end
    
    else 
    if ops_of s2 = ops_of lca
    then begin
      linearizable_s2_0 lca s1 s2
    end
    
    else begin 
        let _, last1 = un_snoc (ops_of s1) in
        let _, last2 = un_snoc (ops_of s2) in
        lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
        linearizable_gt0_merge_pre lca s1 s2 last1 last2;

        let inv1 = inverse_st s1 in 
        let inv2 = inverse_st s2 in 

        if last (resolve_conflict last1 last2) = last1 then
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
