module Ictr_working_opt_m2

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

#push-options "--z3rlimit 300"
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
                    length (diff (ops_of s1) (ops_of lca)) > 0)
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) =
  lem_foldl init_st (ops_of lca); 
  lem_foldl init_st (ops_of s2); 
  lem_foldl init_st (ops_of (inverse_st s1))
#pop-options

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (diff (ops_of s1) (ops_of lca)) = 0)
      (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
               seq_foldl do (v_of lca) (diff (ops_of s2) (ops_of lca))) =
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  lem_foldl init_st (ops_of s2);
  lem_foldl init_st (ops_of lca)

#push-options "--z3rlimit 300"
let linearizable_s1_gt0 (lca s1 s2:st) (l':log)
  : Lemma 
      (requires is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (diff (ops_of s1) (ops_of lca)) > 0 /\
                is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                interleaving_predicate l' lca (inverse_st s1) s2)
      (ensures (let l = Seq.snoc l' (last (ops_of s1)) in
                linearized_merge (v_of lca) l == 
                concrete_merge (v_of lca) (v_of s1) (v_of s2))) =
  let l = Seq.snoc l' (last (ops_of s1)) in
  assert (length l = length l' + 1);
  assert (linearized_merge (v_of lca) l' == concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)); 
  lem_foldl (v_of lca) l'; 
  assert (v_of lca + length l' == concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2));
  assert (v_of lca + length l' == (v_of (inverse_st s1)) + (v_of s2) - (v_of lca));
  assert (v_of lca + length l' == (v_of s1 - 1) + (v_of s2) - (v_of lca));
  assert (v_of lca + length l' + 1 == (v_of s1) + (v_of s2) - (v_of lca));
  lem_foldl (v_of lca) l;
  assert (linearized_merge (v_of lca) l == v_of lca + length l); 
  assert (linearized_merge (v_of lca) l == v_of lca + length l' + 1);
  ()
#pop-options


