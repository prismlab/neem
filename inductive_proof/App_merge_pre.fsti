module App_merge_pre

open FStar.Seq
open FStar.Ghost

#set-options "--query_stats"

let lt (a b:nat) : bool = a < b

// the concrete state type
val concrete_st : Type0

// init state
val init_st : concrete_st

// equivalence between 2 concrete states
val eq (a b:concrete_st) : Type0

val symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a)

val transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c)

val eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b)

// operation type
val app_op_t : eqtype

type timestamp_t = pos 

type op_t = timestamp_t & app_op_t

type log = seq op_t

unfold
let ( ++ ) (l1 l2:log) = Seq.append l1 l2

let rec count_id (id:nat) (l:log) : Tot nat (decreases length l) =
  if length l = 0 then 0
  else (let tl_count = count_id id (tail l) in
        if fst (head l) = id then 1 + tl_count 
        else tl_count)

let mem_id (id:timestamp_t) (l:log) : bool = count_id id l > 0
  
let distinct_ops (l:log) : prop = (forall (id:timestamp_t).{:pattern count_id id l} count_id id l <= 1)

#push-options "--z3rlimit 50"
let rec lemma_append_count_id (lo:log) (hi:log)
  : Lemma
      (ensures (forall x. count_id x (lo ++ hi) = (count_id x lo + count_id x hi)) /\
               (forall id. mem_id id (lo ++ hi) <==> (mem_id id lo \/ mem_id id hi)))
      (decreases (length lo))
  = if length lo = 0
       then (assert (equal (lo ++ hi) hi); ())
       else (assert (equal (cons (head lo) ((tail lo) ++ hi)) (lo ++ hi));
           lemma_append_count_id (tail lo) hi;
           let tl_l_h = (tail lo) ++ hi in
           let lh = cons (head lo) tl_l_h in
           (assert (equal (tail lh) tl_l_h); ()))
#pop-options

let distinct_invert_append (a b:log)
  : Lemma
      (requires distinct_ops (a ++ b))
      (ensures distinct_ops a /\ distinct_ops b /\ 
               (forall id.{:pattern (mem_id id a ==> mem_id id b)} mem_id id a ==> not (mem_id id b)))
      [SMTPat (distinct_ops (a ++ b))]
  = lemma_append_count_id a b

type st0 = concrete_st & erased log
  
let v_of (s:st0) : concrete_st = fst s
let ops_of (s:st0) : GTot log = snd s

// apply an operation to a state
val do (s:concrete_st) (o:op_t) : concrete_st

val lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op))

let rec apply_log (x:concrete_st) (l:log) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |_ -> apply_log (do x (head l)) (tail l)                   

let rec lem_apply_log (x:concrete_st) (l:log)
  : Lemma (ensures (length l > 0 ==> apply_log x l == do (apply_log x (fst (un_snoc l))) (last l)))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_apply_log (do x (head l)) (tail l)
  
let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  (v_of s == apply_log init_st (ops_of s))

type st = s:st0{valid_st s}

//conflict resolution
val resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : (l:log{(forall e. mem e l <==> (e == x \/ e == y))})

// concrete merge pre
val concrete_merge_pre (lca s1 s2:concrete_st) : prop

// concrete merge operation
val concrete_merge (lca s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) : concrete_st

// p is a prefix of l
let is_prefix (p:log) (l:log) : Tot prop =
  Seq.length l >= Seq.length p /\ Seq.equal p (Seq.slice l 0 (Seq.length p))

// s is a suffix of l
let is_suffix (s:log) (l:log) : Tot prop =
  Seq.length l >= Seq.length s /\ Seq.equal s (Seq.slice l (Seq.length l - Seq.length s) (Seq.length l))
  
// s1 - lca
let diff (s1:log) (lca:log{is_prefix lca s1}) 
  : Tot (l:log{(length s1 == length lca + length l) /\ (s1 == lca ++ l) /\
                (forall e. mem e s1 <==> (mem e lca \/ mem e l)) /\
                (forall op. mem op l ==> length s1 > length lca) /\
                is_suffix l s1}) =
  let s = snd (split s1 (length lca)) in
  lemma_split s1 (length lca);
  lemma_mem_append lca s;
  s

let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{(v_of s == do (v_of i) (last (ops_of s))) /\
               (ops_of i = fst (un_snoc (ops_of s))) /\
               (ops_of s = snoc (ops_of i) (last (ops_of s))) /\
               is_prefix (ops_of i) (ops_of s) /\
               (forall id. mem_id id (ops_of i) <==> mem_id id (ops_of s) /\ id <> fst (last (ops_of s)))}) =
  let p,_ = un_snoc (ops_of s) in
  let r = apply_log init_st p in
  lem_apply_log init_st (ops_of s);
  let p, l = un_snoc (ops_of s) in
  let r = apply_log init_st p in
  lemma_split (ops_of s) (length (ops_of s) - 1); 
  lemma_append_count_id p (snd (split (ops_of s) (length (ops_of s) - 1))); 
  distinct_invert_append p (snd (split (ops_of s) (length (ops_of s) - 1)));
  (r, hide p)

let rec mem_ele_id (op:op_t) (l:log)
  : Lemma (requires mem op l)
          (ensures mem_id (fst op) l) (decreases length l) =
  if head l = op then ()
    else mem_ele_id op (tail l)
    
val linearizable_s1_0''_base_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    length (ops_of lca) > 0)
        
          (ensures (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    concrete_merge_pre (v_of l') (v_of s1') (do (v_of s2'') last2)))
                    
val linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))

val linearizable_s1_0''_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    length (ops_of s2') > length (ops_of lca))
        
          (ensures (let inv2 = inverse_st s2' in
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of inv2) last2)))

val linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    is_prefix (ops_of l') (ops_of s1') /\ 
                    is_prefix (ops_of l') (ops_of s2'') /\
                    is_prefix (ops_of l') (snoc (ops_of s2'') last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s1') (ops_of l')) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s2'') (ops_of l')) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of l')) ==> not (mem_id id (diff (ops_of s2'') (ops_of l')))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    concrete_merge_pre (v_of l') (v_of s1') (do (v_of s2'') last2) /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))
          
val linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let inv2 = inverse_st s2' in
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    is_prefix (ops_of lca) (snoc (ops_of inv2) last2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of inv2) last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))
          
val linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

val linearizable_s2_0''_base_pre (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    length (ops_of lca) > 0)
         
          (ensures (let l' = inverse_st lca in
                    let s1'' = inverse_st s1' in
                    let s2' = inverse_st s2 in
                    concrete_merge_pre (v_of l') (do (v_of s1'') last1) (v_of s2')))

val linearizable_s2_0''_base_base (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)))

val linearizable_s2_0''_pre (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    length (ops_of s1') > length (ops_of lca))
         
          (ensures (let inv1 = inverse_st s1' in
                    concrete_merge_pre (v_of lca) (do (v_of inv1) last1) (v_of s2)))

val linearizable_s2_0''_base_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let l' = inverse_st lca in
                    let s1'' = inverse_st s1' in
                    let s2' = inverse_st s2 in
                    is_prefix (ops_of l') (ops_of s1'') /\ 
                    is_prefix (ops_of l') (ops_of s2') /\
                    is_prefix (ops_of l') (snoc (ops_of s1'') last1) /\
                    ops_of s1'' = ops_of l' /\ ops_of s2' = ops_of l' /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s1'') (ops_of l')) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s2') (ops_of l')) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1'') (ops_of l')) ==> not (mem_id id (diff (ops_of s2') (ops_of l')))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    concrete_merge_pre (v_of l') (do (v_of s1'') last1) (v_of s2') /\
                    eq (do (v_of s1'') last1) (concrete_merge (v_of l') (do (v_of s1'') last1) (v_of s2'))))

          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)))
          
val linearizable_s2_0''_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s2 = ops_of lca /\
                    length (ops_of s1') > length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let inv1 = inverse_st s1' in
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    is_prefix (ops_of lca) (snoc (ops_of inv1) last1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (do (v_of inv1) last1) (v_of s2) /\
                    eq (do (v_of inv1) last1) (concrete_merge (v_of lca) (do (v_of inv1) last1) (v_of s2))))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)))

val linearizable_gt0_s2'_s10_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    length (ops_of s2) > length (ops_of lca))
        
          (ensures (let s2' = inverse_st s2 in
                   concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                   concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2')))

val linearizable_gt0_s2'_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\ 
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca))
        
          (ensures (let s1' = inverse_st s1 in
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2)))

val linearizable_gt0_s1'_s20_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    length (ops_of s1) > length (ops_of lca))
       
          (ensures (let s1' = inverse_st s1 in
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1') (do (v_of s2) last2)))

val linearizable_gt0_s1'_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    length (ops_of s2) > length (ops_of lca))
        
          (ensures (let s2' = inverse_st s2 in
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2)))

val linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2)) /\
                
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2)) /\
                      
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
         
          (ensures (last (resolve_conflict last1 last2) = last1 ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (last (resolve_conflict last1 last2) <> last1 ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))                 

val linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
          
                    (let s2' = inverse_st s2 in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                      concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2)) /\
                   
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2') /\
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2)) /\
                      
                     is_prefix (ops_of lca) (ops_of s2') /\
                     (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                     (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca))))))
       
          (ensures (let s2' = inverse_st s2 in
                   (last (resolve_conflict last1 last2) = last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)) ==>
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   (ops_of s1 = ops_of lca /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)) ==>
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))))
                       
val linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\

                    (let s1' = inverse_st s1 in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                      concrete_merge_pre (v_of lca) (v_of s1') (do (v_of s2) last2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) /\
                   
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) /\
                   
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))))
        
          (ensures (let s1' = inverse_st s1 in
                   (ops_of s2 = ops_of lca /\
                   last (resolve_conflict last1 last2) = last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   (last (resolve_conflict last1 last2) <> last1 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))
                       
val linearizable_gt0_merge_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    last1 = last (ops_of s1) /\
                    last2 = last (ops_of s2) /\             
                    fst last1 <> fst last2 /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
       
          (ensures (last (resolve_conflict last1 last2) = last1 ==>
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\

                   (last (resolve_conflict last1 last2) <> last1 ==>
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))                    

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
val concrete_st_s : Type0

// init state 
val init_st_s : concrete_st_s

// apply an operation to a state 
val do_s (st_s:concrete_st_s) (_:op_t) : concrete_st_s

//equivalence relation between the concrete states of sequential type and MRDT
val eq_sm (st_s:concrete_st_s) (st:concrete_st) : prop

//initial states are equivalent
val initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st)

//equivalence between states of sequential type and MRDT at every operation
val do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op))

////////////////////////////////////////////////////////////////




(*val convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ eq s1' (do s1 o) /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures eq (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1'))*)
