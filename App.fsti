module App

open FStar.Seq
open FStar.Ghost

#set-options "--query_stats"

let lt (a b:nat) : bool = a < b

// the concrete state type
val concrete_st : Type0

// init state
val init_st : concrete_st

// operation type
val op_t : eqtype

type timestamp_t = nat

type log_entry = timestamp_t & op_t

type log = seq log_entry

unfold
let ( ++ ) (l1 l2:log) = Seq.append l1 l2

let rec count_id (id:nat) (l:log) : Tot nat (decreases length l) =
  if length l = 0 then 0
     else if fst (head l) = id
          then 1 + count_id id (tail l)
          else count_id id (tail l)

let mem_id (id:nat) (l:log) : bool = count_id id l > 0
  
let distinct_ops (l:log) : prop = (forall (id:nat). count_id id l <= 1) /\ (forall (id:nat). mem_id id l ==> id <> 0)

#push-options "--z3rlimit 50"
let rec lemma_append_count_id (lo:log) (hi:log)
  : Lemma
      (ensures (forall x. count_id x (lo ++ hi) = (count_id x lo + count_id x hi)))
      (decreases (length lo))
  =  if length lo = 0
       then cut (equal (lo ++ hi) hi)
       else (cut (equal (cons (head lo) ((tail lo) ++ hi)) (lo ++ hi));
           lemma_append_count_id (tail lo) hi;
           let tl_l_h = (tail lo) ++ hi in
           let lh = cons (head lo) tl_l_h in
           cut (equal (tail lh) tl_l_h))
#pop-options

let distinct_invert_append (a b:log)
  : Lemma
      (requires distinct_ops (a ++ b))
      (ensures distinct_ops a /\ distinct_ops b /\ (forall id. mem_id id a ==> not (mem_id id b)))
      [SMTPat (distinct_ops (a ++ b))]
= lemma_append_count_id a b

type st0 = concrete_st & erased log
  
let v_of (s:st0) : concrete_st = fst s
let ops_of (s:st0) : GTot log = snd s

// concrete do pre-condition
val concrete_do_pre (_:concrete_st) (_:log_entry) : prop

// apply an operation to a state
val do (s:concrete_st) (o:log_entry{concrete_do_pre s o}) : concrete_st

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
val concrete_st_s : Type0

// init state 
val init_st_s : concrete_st_s

// apply an operation to a state 
val do_s (st_s:concrete_st_s) (_:log_entry) : concrete_st_s

//equivalence relation between the concrete states of sequential type and MRDT
val eq (st_s:concrete_st_s) (st:concrete_st) : bool

//initial states are equivalent
val initial_eq (_:unit)
  : Lemma (ensures eq init_st_s init_st)

//equivalence between states of sequential type and MRDT at every operation
val do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq st_s st /\ concrete_do_pre st op)
          (ensures eq (do_s st_s op) (do st op))

////////////////////////////////////////////////////////////////

let rec foldl_prop (x:concrete_st) (l:log) : Tot prop (decreases length l) =
  match length l with
  |0 -> True
  |1 -> concrete_do_pre x (head l)
  |_ -> concrete_do_pre x (head l) /\ foldl_prop (do x (head l)) (tail l)

let rec seq_foldl (x:concrete_st) (l:log{foldl_prop x l}) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |1 -> do x (head l)
  |_ -> seq_foldl (do x (head l)) (tail l)                   

let rec lem_seq_foldl (x:concrete_st) (l:log)
  : Lemma (requires foldl_prop x l)
          (ensures (length l > 0 ==> foldl_prop x (fst (un_snoc l)) /\
                   concrete_do_pre (seq_foldl x (fst (un_snoc l))) (last l) /\
                   seq_foldl x l  == do (seq_foldl x (fst (un_snoc l))) (last l)))
          (decreases length l) = 
  match length l with
  |0 -> ()
  |1 -> ()
  |_ -> lem_seq_foldl (do x (head l)) (tail l)

let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  foldl_prop init_st (ops_of s) /\
  v_of s == seq_foldl init_st (ops_of s)

type st = s:st0{valid_st s}

//conflict resolution
val resolve_conflict (x y:log_entry) : (l:log{Seq.length l = 1 \/ Seq.length l = 2})

// l is interleaving of l1 and l2
let rec is_interleaving (l l1 l2:log)
  : Tot eqtype (decreases %[Seq.length l1; Seq.length l2]) =

  // if l1 is empty, then l == l2
  (Seq.length l1 == 0 ==> l == l2)

  /\

  // similarly for l2 being empty
  ((Seq.length l1 > 0  /\ Seq.length l2 == 0) ==> l == l1)

  /\

  // if both are non-empty and lengths > 1
  // then three cases
  ((Seq.length l1 > 0 /\ Seq.length l2 > 0) ==>

   (let prefix1, last1 = un_snoc l1 in
    let prefix2, last2 = un_snoc l2 in

    (exists l'.
          is_interleaving l' prefix1 prefix2 /\
          l == l' ++ (resolve_conflict last1 last2))

    \/

    (exists l'.
          is_interleaving l' l1 prefix2 /\
          l == Seq.snoc l' last2)

    \/

    (exists l'.
          is_interleaving l' prefix1 l2 /\
          l == Seq.snoc l' last1)))

// concrete merge pre-condition
val concrete_merge_pre (lca a b:concrete_st) : prop

// concrete merge operation
val concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) : concrete_st

let is_prefix (p:log) (l:log) : Tot prop =
  Seq.length l >= Seq.length p /\ Seq.equal p (Seq.slice l 0 (Seq.length p))

let diff (s1:log) (lca:log{is_prefix lca s1}) 
  : Tot (l:log{(length s1 = length lca + length l) /\ (s1 = lca ++ l)}) =
  let s = snd (split s1 (length lca)) in
  lemma_split s1 (length lca);
  s

let lem_diff (s1:log) (l:log{is_prefix l s1})
  : Lemma (requires distinct_ops s1)
          (ensures distinct_ops (diff s1 l) /\ (forall id. mem_id id (diff s1 l) <==> mem_id id s1 /\ not (mem_id id l)) /\
                   (Seq.length s1 > Seq.length l ==> last s1 = last (diff s1 l) /\ Seq.length (diff s1 l) > 0))
  =  let s = snd (split s1 (length l)) in
    lemma_split s1 (length l);
    lemma_append_count_id l s

let rec split_prefix (s:concrete_st) (l:log) (a:log)
  : Lemma (requires is_prefix l a /\ foldl_prop s a)
          (ensures foldl_prop s l /\ foldl_prop (seq_foldl s l) (diff a l) /\
                   (seq_foldl s a == seq_foldl (seq_foldl s l) (diff a l)) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) = (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |1 -> ()
    |_ -> split_prefix (do s (head l)) (tail l) (tail a)

#push-options "--z3rlimit 100"
let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{(concrete_do_pre (v_of i) (last (ops_of s))) /\
               (v_of s == do (v_of i) (last (ops_of s))) /\
               (ops_of i = fst (un_snoc (ops_of s))) /\
               (ops_of s = snoc (ops_of i) (last (ops_of s))) /\
               is_prefix (ops_of i) (ops_of s) /\
               (forall id. mem_id id (ops_of i) <==> mem_id id (ops_of s) /\ id <> fst (last (ops_of s)))}) = 
  lem_seq_foldl init_st (ops_of s);
  let p, l = un_snoc (ops_of s) in
  let r = seq_foldl init_st p in
  lemma_split (ops_of s) (length (ops_of s) - 1);
  lemma_append_count_id p (snd (split (ops_of s) (length (ops_of s) - 1)));
  distinct_invert_append p (snd (split (ops_of s) (length (ops_of s) - 1)));
  (r, hide p)

let lem_inverse (lca s1:log)
  : Lemma (requires is_prefix lca s1 /\
                    Seq.length s1 > Seq.length lca)
          (ensures (is_prefix lca (fst (un_snoc s1)))) 
  =  lemma_split (fst (un_snoc s1)) (length lca)

let un_snoc_prop (a:log)
  : Lemma (requires distinct_ops a /\ length a > 0)
          (ensures (forall id. mem_id id a <==> mem_id id (fst (un_snoc a)) \/ id = fst (last a)) /\
                   (forall id. mem_id id a /\ id <> fst (last a) <==> mem_id id (fst (un_snoc a))) /\
                   (let _, l = un_snoc a in 
                    mem_id (fst l) a)) =
  let p, l = un_snoc a in
  lemma_split a (length a - 1);
  lemma_append_count_id p (snd (split a (length a - 1)));
  distinct_invert_append p (snd (split a (length a - 1)))

let lastop_diff (l a:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ is_prefix l a /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    length a > length l)
          (ensures (length (diff a l) > 0) /\
                   (let _, last = un_snoc a in
                   mem_id (fst last) a /\ mem_id (fst last) (diff a l)))
  = un_snoc_prop a;
    lem_diff a l;
    un_snoc_prop (diff a l)

let lastop_neq (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (let _, la = un_snoc a in
                    let _, lb = un_snoc b in
                    fst la <> fst lb)) =
  lastop_diff l a;
  lastop_diff l b
#pop-options

let interleaving_predicate (l:log) (lca s1:st)
  (s2:st{concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\ 
         is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2)}) =
  is_interleaving l (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) /\
  foldl_prop (v_of lca) l /\
  seq_foldl (v_of lca) l ==
  concrete_merge (v_of lca) (v_of s1) (v_of s2)

val merge_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (ops_of s2))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))

val merge_inv_s1_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s1) > length (ops_of lca))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2))

val merge_inv_s2_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))

val linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
          (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
                   seq_foldl (v_of lca) (diff (ops_of s2) (ops_of lca)))

val linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    ops_of s2 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
          (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
                   seq_foldl (v_of lca) (diff (ops_of s1) (ops_of lca)))

let linearizable_s1_01 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1)) 
          (ensures (exists l. interleaving_predicate l lca s1 s2)) =
  split_prefix init_st (ops_of lca) (ops_of s2);
  linearizable_s1_0 lca s1 s2

let linearizable_s2_01 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    ops_of s2 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1)) 
          (ensures (exists l. interleaving_predicate l lca s1 s2)) =
  split_prefix init_st (ops_of lca) (ops_of s1);
  linearizable_s2_0 lca s1 s2

let rec inverse_helper (s:concrete_st) (l':log) (op:log_entry)
  : Lemma 
    (requires (foldl_prop s l' /\ concrete_do_pre (seq_foldl s l') op))
    (ensures (let l = Seq.snoc l' op in 
              foldl_prop s l /\
              seq_foldl s l == do (seq_foldl s l') op)) (decreases length l')
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |1 -> ()
    |_ -> inverse_helper (do s (head l')) (tail l') op

val linearizable_s1_gt0 (lca s1 s2:st)
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
                   do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1))

val linearizable_s2_gt0 (lca s1 s2:st)
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
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))

let interleaving_helper_inv1 (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s1 > 0 /\
                is_prefix lca (fst (Seq.un_snoc s1)) /\ is_prefix lca s2 /\
                is_interleaving l' (diff (fst (Seq.un_snoc s1)) lca) (diff s2 lca))
      (ensures (let _, last1 = un_snoc s1 in
                is_interleaving (Seq.snoc l' last1) (diff s1 lca) (diff s2 lca)))
  = assert (is_interleaving l' (fst (Seq.un_snoc (diff s1 lca))) (diff s2 lca));
    let prefix1, last1 = Seq.un_snoc (diff s1 lca) in
    let l = Seq.snoc l' last1 in
    introduce exists l'. is_interleaving l' prefix1 (diff s2 lca) /\
                    l = Seq.snoc l' last1
    with l'
    and ()

let interleaving_helper_inv2 (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s2 > 0 /\
                is_prefix lca (fst (Seq.un_snoc s2)) /\ is_prefix lca s1 /\
                is_interleaving l' (diff s1 lca) (diff (fst (Seq.un_snoc s2)) lca))
      (ensures (let _, last2 = un_snoc s2 in
                is_interleaving (Seq.snoc l' last2) (diff s1 lca) (diff s2 lca)))
  = assert (is_interleaving l' (diff s1 lca) (fst (Seq.un_snoc (diff s2 lca))));
    let prefix2, last2 = Seq.un_snoc (diff s2 lca) in
    let l = Seq.snoc l' last2 in
    introduce exists l'. is_interleaving l' (diff s1 lca) prefix2 /\
                    l = Seq.snoc l' last2
    with l'
    and ()

#push-options "--z3rlimit 200"
let interleaving_s1_inv (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
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
                    let l = Seq.snoc l' last1 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) =
  let _, last1 = un_snoc (ops_of s1) in
  interleaving_helper_inv1 (ops_of lca) (ops_of s1) (ops_of s2) l'; 
  linearizable_s1_gt0 lca s1 s2;
  inverse_helper (v_of lca) l' last1

let interleaving_s2_inv (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
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
                    let l = Seq.snoc l' last2 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) =
  let _, last2 = un_snoc (ops_of s2) in
  interleaving_helper_inv2 (ops_of lca) (ops_of s1) (ops_of s2) l';
  linearizable_s2_gt0 lca s1 s2;
  inverse_helper (v_of lca) l' last2
#pop-options

#push-options "--z3rlimit 100"
let linearizable_s1_gt0_pre (lca s1 s2:st)
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
          (ensures (let inv1 = inverse_st s1 in 
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))) =
  let inv1 = inverse_st s1 in 
  lem_inverse (ops_of lca) (ops_of s1);
  merge_inv_s1_prop lca s1 s2; 
  lemma_split (ops_of inv1) (Seq.length (ops_of lca));
  lem_diff (ops_of inv1) (ops_of lca); 
  lem_diff (ops_of s1) (ops_of lca)

let linearizable_s2_gt0_pre (lca s1 s2:st)
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
          (ensures (let inv2 = inverse_st s2 in 
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca)))))) =
  let inv2 = inverse_st s2 in 
  lem_inverse (ops_of lca) (ops_of s2);
  merge_inv_s2_prop lca s1 s2; 
  lemma_split (ops_of inv2) (Seq.length (ops_of lca));
  lem_diff (ops_of inv2) (ops_of lca); 
  lem_diff (ops_of s2) (ops_of lca)
#pop-options
