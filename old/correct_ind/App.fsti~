module App

open FStar.Seq
open FStar.Ghost

#set-options "--query_stats"

let lt (a b:nat) : bool = a < b

// the concrete state type
val concrete_st : eqtype

// init state
val init_st : concrete_st

// equivalence between 2 concrete states
val eq (a b:concrete_st) : prop

val symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a)
          [SMTPat (eq a b)]

val transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c)

val eq_is_equiv (a b:concrete_st)
  : Lemma (requires a = b)
          (ensures eq a b)

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
      (ensures (forall x. count_id x (lo ++ hi) = (count_id x lo + count_id x hi)) /\
               (forall id. mem_id id (lo ++ hi) <==> (mem_id id lo \/ mem_id id hi)))
      (decreases (length lo))
  = if length lo = 0
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

// apply an operation to a state
val do (s:concrete_st) (o:log_entry) : concrete_st

val lem_do (a b:concrete_st) (op:log_entry)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op))

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
val concrete_st_s : Type0

// init state 
val init_st_s : concrete_st_s

// apply an operation to a state 
val do_s (st_s:concrete_st_s) (_:log_entry) : concrete_st_s

//equivalence relation between the concrete states of sequential type and MRDT
val eq_sm (st_s:concrete_st_s) (st:concrete_st) : prop

//initial states are equivalent
val initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st)

//equivalence between states of sequential type and MRDT at every operation
val do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op))

////////////////////////////////////////////////////////////////

let rec seq_foldl (x:concrete_st) (l:log) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |1 -> do x (head l)
  |_ -> seq_foldl (do x (head l)) (tail l)                   

let rec lem_seq_foldl (x:concrete_st) (l:log)
  : Lemma (ensures (length l > 0 ==> 
                       (seq_foldl x l = do (seq_foldl x (fst (un_snoc l))) (last l))))
          (decreases length l) =
  match length l with
  |0 -> ()
  |1 -> ()
  |_ -> lem_seq_foldl (do x (head l)) (tail l)
  
let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  (v_of s = seq_foldl init_st (ops_of s))

type st = s:st0{valid_st s}

//conflict resolution
val resolve_conflict (x:log_entry) (y:log_entry{fst x <> fst y}) : (l:log{Seq.length l = 1 \/ Seq.length l = 2})

// l is interleaving of l1 and l2
let rec is_interleaving (l l1 l2:log)
  : Tot eqtype (decreases %[Seq.length l1; Seq.length l2]) =

  // if l1 is empty, then l == l2
  (Seq.length l1 = 0 ==> l = l2)

  /\

  // similarly for l2 being empty
  ((Seq.length l1 > 0  /\ Seq.length l2 = 0) ==> l = l1)

  /\

  // if both are non-empty and lengths > 1
  // then three cases
  ((Seq.length l1 > 0 /\ Seq.length l2 > 0) ==>

   (let prefix1, last1 = un_snoc l1 in
    let prefix2, last2 = un_snoc l2 in
    fst last1 <> fst last2 /\

    (exists l'.
          is_interleaving l' prefix1 prefix2 /\
          l = l' ++ (resolve_conflict last1 last2))

    \/

    (exists l'.
          is_interleaving l' l1 prefix2 /\
          l = Seq.snoc l' last2)

    \/

    (exists l'.
          is_interleaving l' prefix1 l2 /\
          l = Seq.snoc l' last1)))

// concrete merge operation
val concrete_merge (lca s1 s2:concrete_st) : concrete_st

// p is a prefix of l
let is_prefix (p:log) (l:log) : Tot prop =
  Seq.length l >= Seq.length p /\ Seq.equal p (Seq.slice l 0 (Seq.length p))

// s is a suffix of l
let is_suffix (s:log) (l:log) : Tot prop =
  Seq.length l >= Seq.length s /\ Seq.equal s (Seq.slice l (Seq.length l - Seq.length s) (Seq.length l))
  
// s1 - lca
let diff (s1:log) (lca:log{is_prefix lca s1}) 
  : Tot (l:log{(length s1 = length lca + length l) /\ (s1 = lca ++ l) /\
                (forall e. mem e s1 <==> (mem e lca \/ mem e l)) /\
                (forall op. mem op l ==> length s1 > length lca) /\
                is_suffix l s1}) =
  let s = snd (split s1 (length lca)) in
  lemma_split s1 (length lca);
  lemma_mem_append lca s;
  s

let rec lem_un_snoc_id (a b:log)
  : Lemma (requires length b > 0 /\ a = fst (un_snoc b))
          (ensures (forall id. mem_id id a ==> mem_id id b)) (decreases length a) =
  match length a with
  |0 -> ()
  |_ -> lem_un_snoc_id (tail a) (tail b)

let rec mem_ele_id (op:log_entry) (l:log)
  : Lemma (requires mem op l)
          (ensures mem_id (fst op) l) (decreases length l) =
  if head l = op then ()
    else mem_ele_id op (tail l)
    
#push-options "--z3rlimit 200" 
let lem_diff (s1 l:log)
  : Lemma (requires distinct_ops s1 /\ is_prefix l s1)
          (ensures distinct_ops (diff s1 l) /\ (forall id. mem_id id (diff s1 l) <==> mem_id id s1 /\ not (mem_id id l)) /\
                   (forall id. mem_id id s1 <==> mem_id id l \/ mem_id id (diff s1 l)) /\
                   (Seq.length s1 > Seq.length l ==> (last s1 = last (diff s1 l) /\ Seq.length (diff s1 l) > 0) /\
                     (let _, l1 = un_snoc s1 in
                      let _, ld = un_snoc (diff s1 l) in
                      l1 = ld) /\
                     (let s1',lastop = un_snoc s1 in 
                       diff s1' l = fst (un_snoc (diff s1 l)))))
  = let s = snd (split s1 (length l)) in
    lemma_split s1 (length l);
    lemma_append_count_id l s

let lem_diff_lastop (s1 l:log)
  : Lemma (requires distinct_ops s1 /\ is_prefix l s1 /\ length s1 > length l)
          (ensures (let s1',lastop = un_snoc s1 in 
                    mem_id (fst lastop) (diff s1 l))) =
  lem_diff s1 l;
  let ds1',lastop = un_snoc (diff s1 l) in 
  lemma_mem_append ds1' (create 1 lastop);
  mem_ele_id lastop (diff s1 l)

let lem_lt_lastop_id_lca (lca s1:log)
  : Lemma (requires is_prefix lca s1 /\ length (diff s1 lca) > 0 /\ distinct_ops s1 /\
                    (forall id id1. mem_id id lca /\ mem_id id1 (diff s1 lca) ==> lt id id1))
          (ensures (let _, lastop = un_snoc s1 in
                    (forall id. mem_id id lca ==> lt id (fst lastop)))) =
    distinct_invert_append lca (diff s1 lca); 
    let pre, lst = un_snoc s1 in
    lem_diff s1 lca;
    mem_ele_id lst (diff s1 lca)
    
let rec split_prefix (s:concrete_st) (l:log) (a:log)
  : Lemma (requires is_prefix l a)
          (ensures (seq_foldl s a = seq_foldl (seq_foldl s l) (diff a l)) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) = (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |1 -> ()
    |_ -> split_prefix (do s (head l)) (tail l) (tail a)
         
#push-options "--z3rlimit 50"
let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{(v_of s = do (v_of i) (last (ops_of s))) /\
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
  = lemma_split (fst (un_snoc s1)) (length lca)

let un_snoc_prop (a:log)
  : Lemma (requires distinct_ops a /\ length a > 0)
          (ensures (forall id. mem_id id a <==> mem_id id (fst (un_snoc a)) \/ id = fst (last a)) /\
                   (forall id. mem_id id a /\ id <> fst (last a) <==> mem_id id (fst (un_snoc a))) /\
                   (let _, l = un_snoc a in 
                    mem_id (fst l) a) /\ distinct_ops (fst (un_snoc a))) =
  let p, l = un_snoc a in
  lemma_split a (length a - 1);
  lemma_append_count_id p (snd (split a (length a - 1)));
  distinct_invert_append p (snd (split a (length a - 1)))
#pop-options

#push-options "--z3rlimit 200"
let lastop_diff (l a:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ is_prefix l a /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    length a > length l)
          (ensures (length (diff a l) > 0) /\
                   (let p, last = un_snoc a in
                   mem_id (fst last) a /\ mem_id (fst last) (diff a l) /\
                   (forall id id1. mem_id id l /\ mem_id id1 (diff p l) ==> lt id id1)))
  = un_snoc_prop a;
    lem_diff a l;
    un_snoc_prop (diff a l);
    lem_inverse l a

let inverse_diff_id_s1' (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ 
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (forall id. mem_id id (diff (fst (un_snoc a)) l) ==> not (mem_id id (diff b l))))
  = un_snoc_prop a;
    lem_diff a l; 
    lem_inverse l a;
    lem_diff (fst (un_snoc a)) l

let inverse_diff_id_s2' (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (forall id. mem_id id (diff a l) ==> not (mem_id id (diff (fst (un_snoc b)) l))))
  = un_snoc_prop b;
    lem_diff b l; 
    lem_inverse l b;
    lem_diff (fst (un_snoc b)) l

let inverse_diff_id_s1'_s2' (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (forall id. mem_id id (diff (fst (un_snoc a)) l) ==> not (mem_id id (diff (fst (un_snoc b)) l))))
  = un_snoc_prop a;
    lem_diff a l; 
    lem_inverse l a;
    lem_diff (fst (un_snoc a)) l;
    un_snoc_prop b;
    lem_diff b l; 
    lem_inverse l b;
    lem_diff (fst (un_snoc b)) l
    
let lastop_neq (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (let p, la = un_snoc a in
                    let _, lb = un_snoc b in
                    fst la <> fst lb)) =
  lastop_diff l a;
  lastop_diff l b
#pop-options

let interleaving_predicate (l:log) (lca s1:st)
  (s2:st{is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2)}) =
  is_interleaving l (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) /\
  eq (seq_foldl (v_of lca) l)
     (concrete_merge (v_of lca) (v_of s1) (v_of s2))

val linearizable_s1_0_base (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

val linearizable_s1_0_ind (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    eq (v_of s2') (concrete_merge (v_of lca) (v_of s1) (v_of s2'))))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

#push-options "--z3rlimit 500"
let rec linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))
          (decreases length (ops_of s2)) =
  if ops_of s2 = ops_of lca then 
    linearizable_s1_0_base lca s1 s2
  else
    (assert (length (ops_of s2) > length (ops_of lca));
    let s2' = inverse_st s2 in
    lem_inverse (ops_of lca) (ops_of s2);
    lastop_diff (ops_of lca) (ops_of s2);
    inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
    linearizable_s1_0 lca s1 s2';
    linearizable_s1_0_ind lca s1 s2)
#pop-options

val linearizable_s2_0_base (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

val linearizable_s2_0_ind (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    (let s1' = inverse_st s1 in
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    eq (v_of s1') (concrete_merge (v_of lca) (v_of s1') (v_of s2))))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

#push-options "--z3rlimit 500"
let rec linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))
          (decreases length (ops_of s1)) =
  if ops_of s1 = ops_of lca then 
    linearizable_s2_0_base lca s1 s2
  else
    (assert (length (ops_of s1) > length (ops_of lca));
    let s1' = inverse_st s1 in
    lem_inverse (ops_of lca) (ops_of s1);
    lastop_diff (ops_of lca) (ops_of s1);
    inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
    linearizable_s2_0 lca s1' s2;
    linearizable_s2_0_ind lca s1 s2)
#pop-options

let rec inverse_helper (s:concrete_st) (l':log) (op:log_entry)
  : Lemma 
    (ensures (let l = Seq.snoc l' op in 
              (seq_foldl s l = do (seq_foldl s l') op))) (decreases length l')
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |1 -> ()
    |_ -> inverse_helper (do s (head l')) (tail l') op

val linearizable_gt0_s2'_base (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))))

val linearizable_gt0_s2'_s10_ind (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    length (ops_of s2) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))) /\
                    
                    (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                                      
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))))

val linearizable_gt0_s2'_s10_base (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))))

let rec linearizable_gt0_s2'_s10 (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))))
          (decreases length (ops_of s2)) =
  if ops_of s2 = ops_of lca then 
    linearizable_gt0_s2'_s10_base lca s1 s2 last2
  else (assert (length (ops_of s2) > length (ops_of lca));
        let s2' = inverse_st s2 in
        lem_inverse (ops_of lca) (ops_of s2);
        lastop_diff (ops_of lca) (ops_of s2);
        inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
        linearizable_gt0_s2'_s10 lca s1 s2' last2;
        linearizable_gt0_s2'_s10_ind lca s1 s2 last2)

val linearizable_gt0_s2'_s1_gt0_ind (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires length (ops_of s1) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))) /\
                    
                    (let s1' = inverse_st s1 in
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    not (mem_id (fst last2) (diff (ops_of s1') (ops_of lca))) /\
                    
                    (eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last2)
                        (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))))

#push-options "--z3rlimit 1000 --fuel 1 --ifuel 1"
let rec linearizable_gt0_s2' (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))))
          (decreases length (ops_of s1)) =
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    linearizable_gt0_s2'_base lca s1 s2 last2
  else if ops_of s1 = ops_of lca then
    linearizable_gt0_s2'_s10 lca s1 s2 last2
  else (assert (length (ops_of s1) > length (ops_of lca));
        let s1' = inverse_st s1 in
        lem_inverse (ops_of lca) (ops_of s1);
        lastop_diff (ops_of lca) (ops_of s1);
        inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
        lem_diff (ops_of s1) (ops_of lca);
        lem_un_snoc_id (diff (ops_of s1') (ops_of lca)) (diff (ops_of s1) (ops_of lca));
        linearizable_gt0_s2' lca s1' s2 last2;
        linearizable_gt0_s2'_s1_gt0_ind lca s1 s2 last2)
#pop-options

#push-options "--z3rlimit 500"
let linearizable_gt0_s2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last2 = un_snoc (ops_of s2) in
  assert (v_of s2 = do (v_of (inverse_st s2)) last2);
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2);
  inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  lem_diff (ops_of s2) (ops_of lca);
  lem_diff_lastop (ops_of s2) (ops_of lca);
  lem_lt_lastop_id_lca (ops_of lca) (ops_of s2);
  linearizable_gt0_s2' lca s1 (inverse_st s2) last2

////////////////////////////////

val linearizable_gt0_s2''_base (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))

val linearizable_gt0_s2''_s10_base (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))

val linearizable_gt0_s2''_s10_s2_gt0 (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\

                    (let s2' = inverse_st s2 in
                     is_prefix (ops_of lca) (ops_of s2') /\
                     (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                     (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 

let rec linearizable_gt0_s2''_s10 (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases  %[length (ops_of s2)]) =
  if ops_of s2 = ops_of lca then
     linearizable_gt0_s2''_s10_base lca s1 s2 last1 last2
  else 
    (assert (length (ops_of s2) > length (ops_of lca)); 
     let s2' = inverse_st s2 in
     lem_inverse (ops_of lca) (ops_of s2);
     lastop_diff (ops_of lca) (ops_of s2);
     inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
     linearizable_gt0_s2''_s10 lca s1 s2' last1 last2;
     linearizable_gt0_s2''_s10_s2_gt0 lca s1 s2 last1 last2)

val linearizable_gt0_s2''_s1_gt0 (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                  //  Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                   // is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\

                    (let s1' = inverse_st s1 in
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))

#push-options "--z3rlimit 1000 --fuel 1 --ifuel 1"
let rec linearizable_gt0_s2'' (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                  //  Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                  //  Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                   // is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s1); length (ops_of s2)]) = 
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    linearizable_gt0_s2''_base lca s1 s2 last1 last2 
  else if ops_of s1 = ops_of lca then
    linearizable_gt0_s2''_s10 lca s1 s2 last1 last2 
  else (assert (length (ops_of s1) > length (ops_of lca));
        let s1' = inverse_st s1 in
        lem_inverse (ops_of lca) (ops_of s1);
        lastop_diff (ops_of lca) (ops_of s1);
        inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
        linearizable_gt0_s2'' lca s1' s2 last1 last2;
        linearizable_gt0_s2''_s1_gt0 lca s1 s2 last1 last2)  

let linearizable_gt0_s2''' (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  assert (v_of s2 = do (v_of (inverse_st s2)) last2);
  assert (v_of s1 = do (v_of (inverse_st s1)) last1);
  lem_inverse (ops_of lca) (ops_of s2);
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s1);
  inverse_diff_id_s1'_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  //lem_diff (ops_of s2) (ops_of lca);
  //lem_diff_lastop (ops_of s2) (ops_of lca);
  //lem_lt_lastop_id_lca (ops_of lca) (ops_of s2);
  linearizable_gt0_s2'' lca (inverse_st s1) (inverse_st s2) last1 last2


/////////////////////////

val linearizable_gt0_s1'_base (lca s1 s2:st) (last1:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    not (mem_id (fst last1) (diff (ops_of s2) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2))))

val linearizable_gt0_s1'_s20_base (lca s1 s2:st) (last1:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    not (mem_id (fst last1) (diff (ops_of s2) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2))))

val linearizable_gt0_s1'_s20_ind (lca s1 s2:st) (last1:log_entry)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    length (ops_of s1) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    not (mem_id (fst last1) (diff (ops_of s2) (ops_of lca))) /\
                    
                    (let s1' = inverse_st s1 in
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                                      
                    (eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2))))

let rec linearizable_gt0_s1'_s20 (lca s1 s2:st) (last1:log_entry)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    not (mem_id (fst last1) (diff (ops_of s2) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2))))
          (decreases length (ops_of s1)) =
  if ops_of s1 = ops_of lca then 
    linearizable_gt0_s1'_s20_base lca s1 s2 last1
  else (assert (length (ops_of s1) > length (ops_of lca));
        let s1' = inverse_st s1 in
        lem_inverse (ops_of lca) (ops_of s1);
        lastop_diff (ops_of lca) (ops_of s1);
        inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
        linearizable_gt0_s1'_s20 lca s1' s2 last1;
        linearizable_gt0_s1'_s20_ind lca s1 s2 last1)

val linearizable_gt0_s1'_s2_gt0_ind (lca s1 s2:st) (last1:log_entry)
  : Lemma (requires length (ops_of s2) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    not (mem_id (fst last1) (diff (ops_of s2) (ops_of lca))) /\
                    
                    (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    not (mem_id (fst last1) (diff (ops_of s2') (ops_of lca))) /\
                    
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2))))


//////////////////////////////TRIAL///////////////////////////

val linearizable_gt0_s1''_base (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))

val linearizable_gt0_s1''_s20_base (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))

val linearizable_gt0_s1''_s20_s1_gt0 (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\

                    (let s1' = inverse_st s1 in
                     is_prefix (ops_of lca) (ops_of s1') /\
                     (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                     (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                     eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 

let rec linearizable_gt0_s1''_s20 (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases  %[length (ops_of s1)]) =
  if ops_of s1 = ops_of lca then
     linearizable_gt0_s1''_s20_base lca s1 s2 last1 last2
  else 
    (assert (length (ops_of s1) > length (ops_of lca)); 
     let s1' = inverse_st s1 in
     lem_inverse (ops_of lca) (ops_of s1);
     lastop_diff (ops_of lca) (ops_of s1);
     inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
     linearizable_gt0_s1''_s20 lca s1' s2 last1 last2;
     linearizable_gt0_s1''_s20_s1_gt0 lca s1 s2 last1 last2)

val linearizable_gt0_s1''_s2_gt0 (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                  //  Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                   // is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\

                    (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))

#push-options "--z3rlimit 1000 --fuel 1 --ifuel 1"
let rec linearizable_gt0_s1'' (lca s1 s2:st) (last1 last2: log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                  //  Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                  //  Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                   // is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2); length (ops_of s1)]) = 
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    linearizable_gt0_s1''_base lca s1 s2 last1 last2 
  else if ops_of s2 = ops_of lca then
    linearizable_gt0_s1''_s20 lca s1 s2 last1 last2 
  else (assert (length (ops_of s2) > length (ops_of lca));
        let s2' = inverse_st s2 in
        lem_inverse (ops_of lca) (ops_of s2);
        lastop_diff (ops_of lca) (ops_of s2);
        inverse_diff_id_s2' (ops_of lca) (ops_of s1) (ops_of s2);
        linearizable_gt0_s1'' lca s1 s2' last1 last2;
        linearizable_gt0_s1''_s2_gt0 lca s1 s2 last1 last2) 

let linearizable_gt0_s1''' (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  assert (v_of s2 = do (v_of (inverse_st s2)) last2);
  assert (v_of s1 = do (v_of (inverse_st s1)) last1);
  lem_inverse (ops_of lca) (ops_of s2);
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s1);
  inverse_diff_id_s1'_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  //lem_diff (ops_of s1) (ops_of lca);
  //lem_diff_lastop (ops_of s1) (ops_of lca);
  //lem_lt_lastop_id_lca (ops_of lca) (ops_of s1);
  linearizable_gt0_s1'' lca (inverse_st s1) (inverse_st s2) last1 last2



val linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     (last (resolve_conflict last1 last2) = last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                     (last (resolve_conflict last1 last2) <> last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s2))))) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2)))))

val convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ eq s1' (do s1 o) /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures eq (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1'))
