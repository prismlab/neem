module App

open FStar.Seq
open FStar.Ghost

#set-options "--query_stats"

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

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = nat

// init state 
let init_st_s = 0

// apply an operation to a state 
let do_s (s:concrete_st_s) (_:log_entry) : concrete_st_s = s + 1

//equivalence relation between the concrete states of sequential type and MRDT
let eq (st_s:concrete_st_s) (st:concrete_st) = st_s = st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq st_s st)
          (ensures eq (do_s st_s op) (do st op)) 
  = ()

////////////////////////////////////////////////////////////////

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (ensures (seq_foldl s l = s + length l) /\
                   (length l > 0 ==> (seq_foldl s l = seq_foldl s (fst (un_snoc l)) + 1)))
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

#set-options "--z3rlimit 50"
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
               seq_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))) =
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
               seq_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))) =
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of lca)

let lem_add (lca s1 s2:nat)
  : Lemma (ensures s1 - 1 + s2 - lca + 1 = s1 + s2 - lca /\
                   s1 + (s2 - 1) - lca + 1 = s1 + s2 - lca)
  = ()
  
#push-options "--z3rlimit 100"
let linearizable_s1_gt0 (lca s1 s2:st)
  : Lemma 
      (requires is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2))
      (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
               do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) (Seq.last (ops_of s1))) =
  let p1, last1 = un_snoc (ops_of s1) in
  inverse_helper init_st p1 last1;
  assert (v_of (inverse_st s1) + v_of s2 - v_of lca =
          v_of s1 - 1 + v_of s2 - v_of lca);
  lem_add (v_of lca) (v_of s1) (v_of s2);
  assert (v_of s1 - 1 + v_of s2 - v_of lca + 1 =
          v_of s1 + v_of s2 - v_of lca);
  assert (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2) + 1 =
          concrete_merge (v_of lca) (v_of s1) (v_of s2));
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

let linearizable_s2_gt0 (lca s1 s2:st)
  : Lemma 
      (requires is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))
      (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
               do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) (Seq.last (ops_of s2))) =
  let p2, last2 = un_snoc (ops_of s2) in
  inverse_helper init_st p2 last2;
  assert (v_of s1 + v_of (inverse_st s2) - v_of lca =
          v_of s1 + (v_of s2 - 1) - v_of lca);
  lem_add (v_of lca) (v_of s1) (v_of s2);
  assert (v_of s1 + (v_of s2 - 1) - v_of lca + 1 =
          v_of s1 + v_of s2 - v_of lca);
  assert (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2)) + 1 =
          concrete_merge (v_of lca) (v_of s1) (v_of s2));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))
#pop-options
