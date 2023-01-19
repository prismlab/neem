module App

open FStar.Seq
open FStar.Ghost

#set-options "--query_stats"

// the concrete state type
// e.g. for the PN counter, concrete_st = int
type concrete_st = int

//initial state
let init_st = 0

// operation type
type op_t:eqtype = 
  |Inc
  |Dec

// concrete do pre-condition
let concrete_do_pre _ _ = true

// apply an operation to a state
let do (s:concrete_st) (op:log_entry{concrete_do_pre s op}) : concrete_st = 
  match snd op with
  |Inc -> s + 1
  |Dec -> s - 1

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = int

// init state 
let init_st_s = 0

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:log_entry) : concrete_st_s = 
  match snd op with
  |Inc -> s + 1
  |Dec -> s - 1

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) 
  = ()

////////////////////////////////////////////////////////////////

let rec count_inc (l:log) : Tot nat (decreases length l) =
  match length l with
  |0 -> 0
  |_ -> match snd (head l) with
       |Inc -> 1 + count_inc (tail l)
       |_ -> count_inc (tail l)

let rec count_dec (l:log) : Tot nat (decreases length l) =
  match length l with
  |0 -> 0
  |_ -> match snd (head l) with
       |Dec -> 1 + count_dec (tail l)
       |_ -> count_dec (tail l)

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires foldl_prop s l)
          (ensures (seq_foldl s l = s + count_inc l - count_dec l) /\
                   (length l > 0 /\ snd (Seq.last l) = Inc ==> 
                           (foldl_prop s (fst (Seq.un_snoc l)) /\ seq_foldl s l = seq_foldl s (fst (Seq.un_snoc l)) + 1)) /\
                   (length l > 0 /\ snd (Seq.last l) = Dec ==>
                           (foldl_prop s (fst (Seq.un_snoc l)) /\ seq_foldl s l = seq_foldl s (fst (Seq.un_snoc l)) - 1)))
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

//conflict resolution
let resolve_conflict (x y:log_entry) : (l:log{length l > 0 /\ last l = y}) =
  cons x (cons y empty)

let resolve_conflict_prop (x y:log_entry)
  : Lemma (requires fst x <> fst y)
          (ensures last (resolve_conflict x y) <> x)
  = ()
  
// concrete merge pre-condition
let concrete_merge_pre lca a b : prop = true

// concrete merge operation
let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) 
  : concrete_st = s1 + s2 - lca

#push-options "--z3rlimit 100"
let merge_inv_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))) =
  lem_foldl init_st (ops_of lca); 
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of (inverse_st s2))

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
          (ensures v_of s2 == concrete_merge (v_of lca) (v_of s1) (v_of s2)) =
  lem_foldl init_st (ops_of s2)

let linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    ops_of s2 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
          (ensures v_of s1 == concrete_merge (v_of lca) (v_of s1) (v_of s2)) =
  lem_foldl init_st (ops_of s1)

let lem_add (lca s1 s2:int)
  : Lemma (ensures s1 + (s2 - 1) - lca + 1 = s1 + s2 - lca /\
                   s1 + (s2 + 1) - lca - 1 = s1 + s2 - lca)
  = ()

let linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     (last (resolve_conflict last1 last2) = last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                           concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                     (last (resolve_conflict last1 last2) <> last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                           concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                      do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                      do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) =
  let _,last1 = un_snoc (ops_of s1) in
  let _,last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  assert (concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2); 
  lem_add (v_of lca) (v_of s1) (v_of s2)

let convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ s1' == do s1 o /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures concrete_merge lca s1' s2 == concrete_merge s1 (concrete_merge lca s1 s2) s1') 
  = ()
#pop-options
