module Ictr

open FStar.Seq
open FStar.Ghost

// the concrete state type
// e.g. for the increment only counter (icounter), concrete_st = nat
type concrete_st = nat

// operation type
// (the only operation is increment, so unit is fine)
type op_t = unit

// apply an operation to a state
let do (s:concrete_st) (_:log_entry) : concrete_st = s + 1

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (ensures (seq_foldl do s l) = s + length l) 
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

//conflict resolution
let resolve_conflict (x y:log_entry) : log =
  cons x (cons y empty)

let resolve_conflict_len (x y:log_entry)
  : Lemma (Seq.length (resolve_conflict x y) = 2)
  = ()

let resolve_conflict_mem (x y:log_entry)
  : Lemma (resolve_conflict_len x y;
           let s = resolve_conflict x y in
           (Seq.length s == 1 ==> is_x_or_y s x y) /\
           (Seq.length s == 2 ==> is_x_and_y s x y))
  = ()

// concrete merge pre-condition
let concrete_merge_pre lca a b : prop
  = a >= lca /\ b >= lca

// concrete merge operation
let concrete_merge (lca:concrete_st) (cst1:concrete_st) (cst2:concrete_st{concrete_merge_pre lca cst1 cst2}) 
  : concrete_st = cst1 + cst2 - lca

let merge_prop (lca s1 s2:st)
  : Lemma (requires v_of lca == init_of s1 /\
                    init_of s1 == init_of s2) 
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2)) =
  lem_foldl (init_of s1) (ops_of s1);
  lem_foldl (init_of s2) (ops_of s2)

let merge_inv_prop (lca s1 s2:st)
  : Lemma (requires length (ops_of s1) > 0 /\ length (ops_of s2) > 0 /\
                    v_of lca == init_of s1 /\
                    init_of s1 == init_of s2)
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) =
  lem_foldl (init_of s1) (ops_of (inverse_st s1));
  lem_foldl (init_of s2) (ops_of (inverse_st s2))

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires 
             v_of lca == init_of s1 /\
             init_of s1 == init_of s2 /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             length (ops_of s1) = 0) 
          (ensures 
             concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
             seq_foldl do (v_of lca) (ops_of s2)) =
  ()

let linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires 
             v_of lca == init_of s1 /\
             init_of s1 == init_of s2 /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             length (ops_of s2) = 0) 
          (ensures 
             concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
             seq_foldl do (v_of lca) (ops_of s1)) =
  ()

#set-options "--z3rlimit 20"
let linearizable_s1s2_gt0 (lca s1 s2:st) (l':log)
  : Lemma (requires 
             v_of lca == init_of s1 /\
             init_of s1 == init_of s2 /\
             length (ops_of s1) > 0 /\ length (ops_of s2) > 0 /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
             interleaving_predicate l' lca (inverse_st s1) (inverse_st s2))
          (ensures 
             (let l = Seq.append l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2))) in
               v_of (linearized_merge (v_of lca) l) == 
               v_of (linearized_merge (v_of (linearized_merge (v_of lca) l'))
                    (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))) /\

               concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
               v_of (linearized_merge (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) 
                    (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))))) =
    lem_foldl (init_of s1) (ops_of s1);
    lem_foldl (init_of s2) (ops_of s2);
    lem_foldl (init_of s1) (ops_of (inverse_st s1));
    lem_foldl (init_of s2) (ops_of (inverse_st s2));
    let l = Seq.append l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2))) in
    lem_foldl (v_of lca) l;
    lem_foldl (v_of (linearized_merge (v_of lca) l')) (resolve_conflict (last (ops_of s1)) (last (ops_of s2)));
    lem_foldl (v_of lca) l'

