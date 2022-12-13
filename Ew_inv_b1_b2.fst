module Ew_inv_b1_b2

open FStar.Seq
open FStar.Ghost

// the concrete state type
// It is a pair of counter and boolean representing the flag state
type concrete_st = nat & bool

//initial state
let init_st = (0, false)

// operation type
// (the only operation is Write value, so nat is fine)
type op_t:eqtype = 
  |Enable
  |Disable

// apply an operation to a state
let do (s:concrete_st) (o:log_entry) : concrete_st = 
  match snd o with
  |Enable -> (fst s + 1, true)
  |Disable -> (fst s, false)

let rec count_en (l:log) : Tot nat (decreases length l) =
  match length l with
  |0 -> 0
  |_ -> match snd (head l) with
       |Enable -> 1 + count_en (tail l)
       |_ -> count_en (tail l)

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (ensures (fst (linearized_merge s l) = fst s + count_en l) /\
                   ((length l > 0 /\ (exists e. mem e l /\ snd e = Enable)) <==> fst (linearized_merge s l) > fst s) /\
                   ((length l = 0 \/ (length l > 0 /\ (forall e. mem e l ==> snd e <> Enable))) <==> fst (linearized_merge s l) = fst s) /\
                   (((length l > 0 /\ snd (last l) = Disable) \/
                   (length l = 0 /\ snd s = false)) <==> snd (linearized_merge s l) = false) /\
                   (((length l > 0 /\ snd (last l) = Enable) \/
                   (length l = 0 /\ snd s = true)) <==> snd (linearized_merge s l) = true))
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

//conflict resolution
let resolve_conflict (x y:log_entry) : (l:log{forall e. mem e l <==> e = x \/ e = y}) =
  if snd x = Enable && snd y = Disable then
     cons y (cons x empty) else
       cons x (cons y empty)

#push-options "--z3rlimit 50"
let resolve_conflict_prop (x y:log_entry)
  : Lemma (requires fst x <> fst y)
          (ensures Seq.length (resolve_conflict x y) = 2 /\
                   ((snd x = Disable /\ snd y = Disable) ==> count_en (resolve_conflict x y) = 0) /\
                   ((snd x = Enable /\ snd y = Enable) ==> count_en (resolve_conflict x y) = 2) /\
            (((snd x = Enable /\ snd y = Disable) \/ (snd x = Disable /\ snd y = Enable)) ==> count_en (resolve_conflict x y) = 1) /\
            (snd x = Enable /\ snd y = Disable <==> last (resolve_conflict x y) = x) /\
            (snd x <> Enable \/ snd y <> Disable <==> last (resolve_conflict x y) = y) /\
            (last (resolve_conflict x y) <> x <==> last (resolve_conflict x y) = y) /\
            (last (resolve_conflict x y) <> y <==> last (resolve_conflict x y) = x) /\
            (last (resolve_conflict x y) <> x <==> snd x <> Enable \/ snd y <> Disable) /\
            (last (resolve_conflict x y) <> y <==> snd x = Enable /\ snd y = Disable))
  = ()

// concrete merge pre-condition
let concrete_merge_pre lca a b : prop
  = fst a >= fst lca /\ fst b >= fst lca

val merge_flag : l:concrete_st
               -> a:concrete_st
               -> b:concrete_st{concrete_merge_pre l a b}
               -> Tot (b1:bool {(b1 = true <==> (snd a = true /\ fst a > fst l) \/
                                             (snd b = true /\ fst b > fst l) \/
                                             (snd a = true /\ snd b = true) \/ 
                                             (snd a = true /\ snd b = false /\ fst a > fst l) \/
                                             (snd b = true /\ snd a = false /\ fst b > fst l)) /\
                               (b1 = false <==> (snd a = false /\ fst b = fst l) \/
                                              (snd b = false /\ fst a = fst l) \/
                                              (snd a = false /\ snd b = false) \/ 
                                              (snd a = true /\ snd b = false /\ fst a = fst l) \/
                                              (snd b = true /\ snd a = false /\ fst b = fst l))})
let merge_flag l a b =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac - lc > 0
          else bc - lc > 0

// concrete merge operation
let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) : concrete_st = 
  (fst s1 + fst s2 - fst lca, merge_flag lca s1 s2)

#push-options "--z3rlimit 50"
let merge_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (ops_of s2))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2)) = 
  lem_foldl init_st (ops_of s1); 
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))

let merge_inv_s1_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s1) > length (ops_of lca))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) =
  lem_foldl init_st (ops_of s2); 
  lem_foldl init_st (ops_of (inverse_st s1));
  lem_inverse (ops_of lca) (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of (inverse_st s1));
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of (inverse_st s1)) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))

let merge_inv_s2_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) =
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of (inverse_st s2));
  lem_inverse (ops_of lca) (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of (inverse_st s2));
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of (inverse_st s2)) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                ops_of s1 = ops_of lca /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
      (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
               seq_foldl do (v_of lca) (diff (ops_of s2) (ops_of lca))) =
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s2);
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
                (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
      (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
               seq_foldl do (v_of lca) (diff (ops_of s1) (ops_of lca))) =
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

let lem_add (lca s1 s2:nat)
  : Lemma (ensures s1 - 1 + s2 - lca + 1 = s1 + s2 - lca /\
                   s1 + s2 - 1 - lca + 1 = s1 + s2 - lca)
  = ()

#push-options "--z3rlimit 100"
let linearizable_s1_gt0 (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ Seq.length (ops_of s1) > 0 /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ Seq.length (ops_of s2) > 0 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                    interleaving_predicate l' lca (inverse_st s1) s2 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) = last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) =
  let p1, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  assert (snd last1 = Enable /\ snd last2 = Disable);
  inverse_helper init_st p1 last1;
  assert (fst (v_of (inverse_st s1)) + fst (v_of s2) - fst (v_of lca) =
          fst (v_of s1) - 1 + fst (v_of s2) - fst (v_of lca));
  lem_add (fst (v_of lca)) (fst (v_of s1)) (fst (v_of s2));
  assert ((fst (v_of s1) - 1 + fst (v_of s2) - fst (v_of lca) + 1) =
          (fst (v_of s1) + fst (v_of s2) - fst (v_of lca)));
  assert (fst (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) + 1 =
          fst (concrete_merge (v_of lca) (v_of s1) (v_of s2)));
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca)); 
  assert (fst (v_of s1) > fst (v_of lca));
  assert (merge_flag (v_of lca) (v_of s1) (v_of s2) = true);
  ()

let linearizable_s2_gt01 (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ Seq.length (ops_of s1) > 0 /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ Seq.length (ops_of s2) > 0 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    interleaving_predicate l' lca s1 (inverse_st s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1 /\
                     snd last1 = Disable /\ snd last2 = Disable))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) = 
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  inverse_helper init_st p2 last2;
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2)

let linearizable_s2_gt02 (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ Seq.length (ops_of s1) > 0 /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ Seq.length (ops_of s2) > 0 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    interleaving_predicate l' lca s1 (inverse_st s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1 /\
                     snd last1 = Enable /\ snd last2 = Enable))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) = 
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  inverse_helper init_st p2 last2;
  assert (fst (v_of s1) + fst (v_of (inverse_st s2)) - fst (v_of lca) =
          fst (v_of s1) + fst (v_of s2) - 1 - fst (v_of lca));
  lem_add (fst (v_of lca)) (fst (v_of s1)) (fst (v_of s2));
  assert ((fst (v_of s1) + fst (v_of s2) - 1 - fst (v_of lca) + 1) =
          (fst (v_of s1) + fst (v_of s2) - fst (v_of lca)));
  assert (fst (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) + 1 =
          fst (concrete_merge (v_of lca) (v_of s1) (v_of s2)));
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2)
#pop-options

#push-options "--z3rlimit 100"
let linearizable_s2_gt03 (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ Seq.length (ops_of s1) > 0 /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ Seq.length (ops_of s2) > 0 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    interleaving_predicate l' lca s1 (inverse_st s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1 /\
                     snd last1 = Disable /\ snd last2 = Enable))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) = 
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  inverse_helper init_st p2 last2;
  assert (fst (v_of s1) + fst (v_of (inverse_st s2)) - fst (v_of lca) =
          fst (v_of s1) + fst (v_of s2) - 1 - fst (v_of lca));
  lem_add (fst (v_of lca)) (fst (v_of s1)) (fst (v_of s2));
  assert ((fst (v_of s1) + fst (v_of s2) - 1 - fst (v_of lca) + 1) =
          (fst (v_of s1) + fst (v_of s2) - fst (v_of lca)));
  assert (fst (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) + 1 =
          fst (concrete_merge (v_of lca) (v_of s1) (v_of s2)));
  assert (fst (v_of s2) > fst (v_of lca));
  assert (merge_flag (v_of lca) (v_of s1) (v_of s2) = true);
  ()
#pop-options

let linearizable_s2_gt0 (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ Seq.length (ops_of s1) > 0 /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ Seq.length (ops_of s2) > 0 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    interleaving_predicate l' lca s1 (inverse_st s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  match snd last1, snd last2 with
  |Disable, Disable -> linearizable_s2_gt01 lca s1 s2 l'
  |Disable, Enable -> linearizable_s2_gt03 lca s1 s2 l'
  |Enable, Enable -> linearizable_s2_gt02 lca s1 s2 l'

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = bool

// init state 
let init_st_s = false

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:log_entry) : concrete_st_s = 
  if snd op = Enable then true else false

//equivalence relation between the concrete states of sequential type and MRDT
let eq (st_s:concrete_st_s) (st:concrete_st) = st_s = snd st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq st_s st)
          (ensures eq (do_s st_s op) (do st op)) 
  = ()
