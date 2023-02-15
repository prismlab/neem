module App

open FStar.Seq
open FStar.Ghost

// the concrete state type
// It is a pair of timestamp and value
type concrete_st = nat & nat

//initial state
let init_st = (0, 0)

let eq (a b:concrete_st) = a == b

let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a = b)
          (ensures eq a b) = ()
          
// operation type
// (the only operation is Write value, so nat is fine)
type op_t = nat

// concrete do pre-condition
let concrete_do_pre _ _ = true

// apply an operation to a state
let do (s:concrete_st) (op:log_entry) : (r:concrete_st{r = op}) = op

let lem_do (a b:concrete_st) (op:log_entry)
   : Lemma (requires concrete_do_pre a op /\ eq a b)
           (ensures concrete_do_pre b op /\ eq (do a op) (do b op)) = ()
           
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = nat

// init state 
let init_st_s = 0

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:log_entry) : concrete_st_s = snd op

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == snd st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) 
  = ()

////////////////////////////////////////////////////////////////

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires foldl_prop s l)
          (ensures (length l > 0 ==> (let _, last = un_snoc l in seq_foldl s l = last) /\
                                     mem_id (fst (seq_foldl s l)) l) /\
                   (length l = 0 ==> (seq_foldl s l = s)) /\
                   (length l > 0 /\ (forall id. mem_id id l ==> lt (fst s) id) ==> (lt (fst s) (fst (seq_foldl s l)))) /\
                   (fst (seq_foldl s l) = fst s \/ mem_id (fst (seq_foldl s l)) l))
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

//conflict resolution
let resolve_conflict (x y:log_entry) : (l:log{forall e. mem e l <==> e = x \/ e = y}) =
  if lt (fst y) (fst x)
    then cons y (cons x empty)
      else cons x (cons y empty)

#push-options "--z3rlimit 50"
let resolve_conflict_prop (x y:log_entry)
  : Lemma (requires fst x <> fst y)
          (ensures (lt (fst y) (fst x) <==> last (resolve_conflict x y) = x) /\
                   (last (resolve_conflict x y) <> x <==> lt (fst x) (fst y)))
  = ()

// concrete merge pre-condition
let concrete_merge_pre lca a b : prop = 
  fst a >= fst lca /\ fst b >= fst lca /\
  (fst a = fst b ==> a = b)

// concrete merge operation
let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) : concrete_st = 
  if lt (fst s1) (fst s2) then s2 else s1

#push-options "--z3rlimit 100"
let merge_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2)) = 
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1); 
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))

let merge_inv_s1_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) = last1))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) =
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s1); 
  inverse_diff_id (ops_of lca) (ops_of s1) (ops_of s2);
  merge_prop lca (inverse_st s1) s2

let merge_inv_s2_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) =
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2); 
  inverse_diff_id (ops_of lca) (ops_of s2) (ops_of s1);
  merge_prop lca s1 (inverse_st s2)

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
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  if last (resolve_conflict last1 last2) = last1 then
    merge_inv_s1_prop lca s1 s2 else
      merge_inv_s2_prop lca s1 s2
  
let linearizable_s1_0 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                ops_of s1 = ops_of lca /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
      (ensures v_of s2 == concrete_merge (v_of lca) (v_of s1) (v_of s2)) =
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))
  
let linearizable_s2_0 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                ops_of s2 = ops_of lca /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
      (ensures v_of s1 == concrete_merge (v_of lca) (v_of s1) (v_of s2)) =
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

let linearizable_s1_gt0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) = last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  assert (concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1);
  lem_seq_foldl init_st (ops_of s1);
  lem_seq_foldl init_st (ops_of s2);
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2);
  resolve_conflict_prop last1 last2;
  lem_foldl init_st (ops_of s1)

let linearizable_s2_gt0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  assert (concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2);
  lem_seq_foldl init_st (ops_of s1);
  lem_seq_foldl init_st (ops_of s2);
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2); 
  resolve_conflict_prop last1 last2;
  lem_foldl init_st (ops_of s2)

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
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  if last (resolve_conflict last1 last2) = last1 then
    linearizable_s1_gt0 lca s1 s2 else
      linearizable_s2_gt0 lca s1 s2

let convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ s1' == do s1 o /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures concrete_merge lca s1' s2 == concrete_merge s1 (concrete_merge lca s1 s2) s1') 
  = ()
#pop-options
