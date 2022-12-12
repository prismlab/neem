module Ictr_inv_b1_b2

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
  : Lemma (ensures ((seq_foldl do s l) = s + length l) /\
                   (length l > 0 ==> (seq_foldl do s l = seq_foldl do s (fst (un_snoc l)) + 1)))
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
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (ops_of s2))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2)) = 
  lem_foldl init_st (ops_of lca); 
  lem_foldl init_st (ops_of s1); 
  lem_foldl init_st (ops_of s2)

let merge_inv_s1_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\ 
                    length (ops_of s1) > length (ops_of lca))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) =
  lem_foldl init_st (ops_of lca); 
  lem_foldl init_st (ops_of s2); 
  lem_foldl init_st (ops_of (inverse_st s1))

let merge_inv_s2_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) =
  lem_foldl init_st (ops_of lca); 
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of (inverse_st s2))

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                ops_of s1 = ops_of lca)
      (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
               seq_foldl do (v_of lca) (diff (ops_of s2) (ops_of lca))) =
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  lem_foldl init_st (ops_of s2);
  lem_foldl init_st (ops_of lca)

let linearizable_s2_0 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                ops_of s2 = ops_of lca)
      (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
               seq_foldl do (v_of lca) (diff (ops_of s1) (ops_of lca))) =
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of lca)

#push-options "--z3rlimit 500"
let linearizable_s1_gt0 (lca s1 s2:st) (l':log)
  : Lemma 
      (requires is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                interleaving_predicate l' lca (inverse_st s1) s2)
      (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
               do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) (Seq.last (ops_of s1))) =
  ()

let linearizable_s2_gt0 (lca s1 s2:st) (l':log)
  : Lemma 
      (requires is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                interleaving_predicate l' lca s1 (inverse_st s2))
      (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
               do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) (Seq.last (ops_of s2))) =
  ()
#pop-options

