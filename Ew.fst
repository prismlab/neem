module Ew

open FStar.Seq
open FStar.Ghost

// the concrete state type
// e.g. for the enable win flag , concrete_st = nat & bool
type concrete_st = nat & bool

// operation type
type op_t = 
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
  : Lemma (ensures (fst (seq_foldl do s l) = fst s + count_en l) /\
                  ((length l > 0 /\ (exists e. mem e l /\ snd e = Enable)) <==> fst (seq_foldl do s l) > fst s) /\
             ((length l = 0 \/ (length l > 0 /\ (forall e. mem e l ==> snd e <> Enable))) <==> fst (seq_foldl do s l) = fst s) /\
                   (((length l > 0 /\ snd (last l) = Disable) \/
                    (length l = 0 /\ snd s = false)) <==> snd (seq_foldl do s l) = false) /\
                   (((length l > 0 /\ snd (last l) = Enable) \/
                    (length l = 0 /\ snd s = true)) <==> snd (seq_foldl do s l) = true))
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

//conflict resolution
let resolve_conflict (x y:log_entry) : log =
  if snd x = Enable && snd y = Disable then
    cons y (cons x empty) else
      cons x (cons y empty)

let resolve_conflict_prop (x y:log_entry)
  : Lemma (ensures Seq.length (resolve_conflict x y) = 2 /\
           ((snd x = Disable /\ snd y = Disable) ==> count_en (resolve_conflict x y) = 0) /\
           ((snd x = Enable /\ snd y = Enable) ==> count_en (resolve_conflict x y) = 2) /\
    (((snd x = Enable /\ snd y = Disable) \/ (snd x = Disable /\ snd y = Enable)) ==> count_en (resolve_conflict x y) = 1))
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
let concrete_merge (lca:concrete_st) (cst1:concrete_st) (cst2:concrete_st{concrete_merge_pre lca cst1 cst2}) 
  : concrete_st = 
  (fst cst1 + fst cst2 - fst lca, merge_flag lca cst1 cst2)

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
  lem_foldl (init_of s2) (ops_of s2)

let linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires 
             v_of lca == init_of s1 /\
             init_of s1 == init_of s2 /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             length (ops_of s2) = 0) 
          (ensures 
             concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
             seq_foldl do (v_of lca) (ops_of s1)) =
  lem_foldl (init_of s1) (ops_of s1)

#set-options "--z3rlimit 20"
let linearizable_s1s2_gt01 (lca s1 s2:st) (l':log)
  : Lemma (requires 
             v_of lca == init_of s1 /\
             init_of s1 == init_of s2 /\
             length (ops_of s1) > 0 /\ length (ops_of s2) > 0 /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
             interleaving_predicate l' lca (inverse_st s1) (inverse_st s2))
          (ensures 
             concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
               v_of (linearized_merge (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
                    (resolve_conflict (last (ops_of s1)) (last (ops_of s2))))) =
  resolve_conflict_prop (last (ops_of s1)) (last (ops_of s2));
  inverse_st_props s1; inverse_st_props s2;
  lem_foldl (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) 
            (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))

let rec lemma_append_count_en (lo:log) (hi:log)
  : Lemma
      (ensures (count_en ( lo ++ hi) = (count_en lo + count_en hi)))
      (decreases (length lo))
      [SMTPat (lo ++ hi)]
  = if length lo = 0
      then cut (equal ( lo ++ hi) hi)
        else (cut (equal (cons (head lo) ( (tail lo) ++ hi)) ( lo ++ hi));
              lemma_append_count_en (tail lo) hi;
              let tl_l_h = (tail lo) ++ hi in
              let lh = cons (head lo) tl_l_h in
              cut (equal (tail lh) tl_l_h))

let linearizable_s1s2_gt0 (lca s1 s2:st) (l':log)
  : Lemma (requires 
             v_of lca == init_of s1 /\
             init_of s1 == init_of s2 /\
             length (ops_of s1) > 0 /\ length (ops_of s2) > 0 /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
             interleaving_predicate l' lca (inverse_st s1) (inverse_st s2))
          (ensures 
             concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
             v_of (linearized_merge (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
                  (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))) /\

             (let l = Seq.append l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2))) in
               v_of (linearized_merge (v_of lca) l) == 
               v_of (linearized_merge (v_of (linearized_merge (v_of lca) l'))
                    (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))))) =
  linearizable_s1s2_gt01 lca s1 s2 l';
  let l = Seq.append l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2))) in
  lem_foldl (v_of lca) l;
  lem_foldl (v_of lca) l';
  lem_foldl (v_of (linearized_merge (v_of lca) l')) (resolve_conflict (last (ops_of s1)) (last (ops_of s2)));
  lemma_append_count_en l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))

