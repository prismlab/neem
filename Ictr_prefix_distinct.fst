module Ictr_prefix_distinct

open FStar.Seq
open FStar.Ghost

// the concrete state type
// e.g. for the increment only counter (icounter), concrete_st = nat
type concrete_st = nat

//initial state
let init_st = 0

// operation type
// (the only operation is increment, so unit is fine)
type op_t = unit

// apply an operation to a state
let do (s:concrete_st) (_:log_entry) : concrete_st = s + 1

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (ensures ((seq_foldl do s l) = s + length l))
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

//conflict resolution
let resolve_conflict (x y:log_entry) : log =
  cons x (cons y empty)

// concrete merge pre-condition
let concrete_merge_pre lca a b : prop
  = a >= lca /\ b >= lca

// concrete merge operation
let concrete_merge (lca:concrete_st) (cst1:concrete_st) (cst2:concrete_st{concrete_merge_pre lca cst1 cst2}) 
  : concrete_st = cst1 + cst2 - lca

let merge_prop (lca s1 s2:st)
  : Lemma (requires init_of lca == init_st /\
                    init_of lca == init_of s1 /\
                    init_of lca == init_of s2 /\ 
                    is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (ops_of s2))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2)) =
  lem_foldl (init_of lca) (ops_of lca); 
  lem_foldl (init_of s1) (ops_of s1); 
  lem_foldl (init_of s2) (ops_of s2)

#push-options "--z3rlimit 100"
let merge_inv_prop (lca s1 s2:st)
  : Lemma (requires init_of lca == init_st /\
                    init_of lca == init_of s1 /\
                    init_of lca == init_of s2 /\
                    is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (diff (ops_of s1) (ops_of lca)) > 0 /\ 
                    length (diff (ops_of s2) (ops_of lca)) > 0)
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) =
  lem_foldl (init_of lca) (ops_of lca);
  lem_foldl (init_of s1) (ops_of (inverse_st s1));
  lem_foldl (init_of s2) (ops_of (inverse_st s2))
#pop-options

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires 
             init_of lca == init_st /\
             init_of lca == init_of s1 /\
             init_of lca == init_of s2 /\ 
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             is_prefix (ops_of lca) (ops_of s1) /\
             is_prefix (ops_of lca) (ops_of s2) /\
             Seq.length (diff (ops_of s1) (ops_of lca)) = 0) 
          (ensures 
             concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
             seq_foldl do (v_of lca) (diff (ops_of s2) (ops_of lca)) /\
             interleaving_predicate (diff (ops_of s2) (ops_of lca)) lca s1 s2 /\
               (exists l. interleaving_predicate l lca s1 s2)) =
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  lem_foldl (init_of lca) (ops_of lca);
  lem_foldl (init_of s2) (ops_of s2)

let linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires 
             init_of lca == init_st /\
             init_of lca == init_of s1 /\
             init_of lca == init_of s2 /\ 
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             is_prefix (ops_of lca) (ops_of s1) /\
             is_prefix (ops_of lca) (ops_of s2) /\
             Seq.length (diff (ops_of s2) (ops_of lca)) = 0)
          (ensures 
             concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
             seq_foldl do (v_of lca) (diff (ops_of s1) (ops_of lca)) /\
             interleaving_predicate (diff (ops_of s1) (ops_of lca)) lca s1 s2 /\
             (exists l. interleaving_predicate l lca s1 s2)) =
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl (init_of s1) (ops_of s1);
  lem_foldl (init_of lca) (ops_of lca)

#push-options "--z3rlimit 200"
let linearizable_s1s2_gt01 (lca s1 s2:st) (l':log)
  : Lemma (requires 
             init_of lca == init_st /\
             init_of lca == init_of s1 /\
             init_of lca == init_of s2 /\ 
             is_prefix (ops_of lca) (ops_of s1) /\
             is_prefix (ops_of lca) (ops_of s2) /\
             Seq.length (diff (ops_of s1) (ops_of lca)) > 0 /\
             Seq.length (diff (ops_of s2) (ops_of lca)) > 0 /\
             is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
             is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
             interleaving_predicate l' lca (inverse_st s1) (inverse_st s2))
         (ensures
           (let l = Seq.append l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2))) in
               linearized_merge (v_of lca) l == 
               linearized_merge (linearized_merge (v_of lca) l')
                 (resolve_conflict (last (ops_of s1)) (last (ops_of s2))))) =

  let l = Seq.append l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2))) in
  lem_foldl (v_of lca) l;
  lem_foldl (v_of lca) l';
  lem_foldl (linearized_merge (v_of lca) l') (resolve_conflict (last (ops_of s1)) (last (ops_of s2)));
  Seq.lemma_append_count l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))
#pop-options

#push-options "--z3rlimit 200"
let linearizable_s1s2_gt02 (lca s1 s2:st) (l':log)
  : Lemma (requires 
             init_of lca == init_st /\
             init_of lca == init_of s1 /\
             init_of lca == init_of s2 /\ 
             is_prefix (ops_of lca) (ops_of s1) /\
             is_prefix (ops_of lca) (ops_of s2) /\
             Seq.length (diff (ops_of s1) (ops_of lca)) > 0 /\
             Seq.length (diff (ops_of s2) (ops_of lca)) > 0 /\
             is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
             is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
             interleaving_predicate l' lca (inverse_st s1) (inverse_st s2))
         (ensures
           concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
               linearized_merge (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
                 (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))) =

  lem_foldl (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) 
            (resolve_conflict (last (ops_of s1)) (last (ops_of s2)));
  assert (linearized_merge (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
          (resolve_conflict (last (ops_of s1)) (last (ops_of s2))) ==
          v_of (inverse_st s1) + v_of (inverse_st s2) - v_of lca + 2);
  inverse_st_props s1; inverse_st_props s2;    
  assert (v_of (inverse_st s1) + v_of (inverse_st s2) - v_of lca + 2 ==
           (v_of s1 - 1) + (v_of s2 - 1) - v_of lca + 2);
  assert (v_of (inverse_st s1) + v_of (inverse_st s2) - v_of lca + 2 ==
               v_of s1 + v_of s2 - v_of lca); ()
#pop-options

let linearizable_s1s2_gt0 (lca s1 s2:st) (l':log)
  : Lemma (requires 
             init_of lca == init_st /\
             init_of lca == init_of s1 /\
             init_of lca == init_of s2 /\ 
             is_prefix (ops_of lca) (ops_of s1) /\
             is_prefix (ops_of lca) (ops_of s2) /\
             Seq.length (diff (ops_of s1) (ops_of lca)) > 0 /\
             Seq.length (diff (ops_of s2) (ops_of lca)) > 0 /\
             is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
             is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
             interleaving_predicate l' lca (inverse_st s1) (inverse_st s2))
         (ensures
           (let l = Seq.append l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2))) in
                linearized_merge (v_of lca) l == 
                linearized_merge (linearized_merge (v_of lca) l')
                  (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))) /\
           concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
               linearized_merge (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
                 (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))) =

  linearizable_s1s2_gt01 lca s1 s2 l';
  linearizable_s1s2_gt02 lca s1 s2 l'

