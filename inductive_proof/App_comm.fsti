module App_comm

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

// few properties of equivalence relation
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

#push-options "--z3rlimit 100"
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
      (ensures distinct_ops a /\ distinct_ops b /\ 
               (forall id. mem_id id a ==> not (mem_id id b)))
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

// equivalence relation between the concrete states of sequential type and MRDT
val eq_sm (st_s:concrete_st_s) (st:concrete_st) : prop

// initial states are equivalent
val initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st)

// equivalence between states of sequential type and MRDT at every operation
val do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op))

////////////////////////////////////////////////////////////////

// applying a log of operations to a concrete state
let rec seq_foldl (x:concrete_st) (l:log) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |1 -> do x (head l)
  |_ -> seq_foldl (do x (head l)) (tail l)                   

// property of seq_foldl
let rec lem_seq_foldl (x:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (length l > 0 ==> (seq_foldl x l = seq_foldl (do x (head l)) (tail l)) /\
                                    (seq_foldl x l = do (seq_foldl x (fst (un_snoc l))) (last l))) /\
                   (length l = 0 ==> seq_foldl x l = x))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_seq_foldl (do x (head l)) (tail l)

let rec lem_seq_foldl_forall (l:log) 
  : Lemma (requires true)
          (ensures (forall x. (length l > 0 ==> (seq_foldl x l = seq_foldl (do x (head l)) (tail l)) /\
                                          (seq_foldl x l = do (seq_foldl x (fst (un_snoc l))) (last l))) /\
                         (length l = 0 ==> seq_foldl x l = x)))
                   
                   (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_seq_foldl_forall (tail l)

// valid state
let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  (v_of s = seq_foldl init_st (ops_of s))

type st = s:st0{valid_st s}

//operations x and y are commutative
val commutative (x y: log_entry) :  bool

val comm_symmetric (x y:log_entry) 
  : Lemma (requires commutative x y)
          (ensures commutative y x)
          [SMTPat (commutative x y)]
          
// if x and y are commutative ops, applying them in any order should give equivalent results
val commutative_prop (x y:log_entry) 
  : Lemma (requires commutative x y)
          (ensures (forall s. eq (seq_foldl s (cons x (cons y empty))) (seq_foldl s (cons y (cons x empty)))))

let rec forallb (#a:eqtype) (f:a -> bool) (l:seq a)
  : Tot (b:bool{(forall e. mem e l ==> f e) <==> b = true}) (decreases length l) =
  match length l with
  |0 -> true
  |_ -> if f (head l) then forallb f (tail l) else false

//commutativity for a sequence of operation
let commutative_seq (x:log_entry) (l:log) : bool =
  forallb (fun e -> commutative x e) l

let comm_empty_log (x:log_entry) (l:log)
  : Lemma (ensures length l = 0 ==> commutative_seq x l) = ()

#push-options "--z3rlimit 200"
let rec existsb (#a:eqtype) (f:a -> bool) (l:seq a)
  : Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true}) (decreases length l) =
  match length l with
  |0 -> false
  |_ -> if f (head l) then true else existsb f (tail l)

// returns position of op in a log of operations
let rec pos (op:log_entry) (l:log{mem op l}) : Tot (n:nat{n >= 0 /\ n < length l})
    (decreases length l) =
  match length l with
  |1 -> 0
  |_ -> if head l = op then 0 else 1 + pos op (tail l)

// p is a prefix of l
let is_prefix (p:log) (l:log) : Tot prop =
  Seq.length l >= Seq.length p /\ Seq.equal p (Seq.slice l 0 (Seq.length p))

// s is a suffix of l
let is_suffix (s:log) (l:log) : Tot prop =
  Seq.length l >= Seq.length s /\ Seq.equal s (Seq.slice l (Seq.length l - Seq.length s) (Seq.length l))

// l = (snoc (fst ps) op) ++ snd ps
#push-options "--z3rlimit 30"
let pre_suf1 (l:log) (op:log_entry{mem op l})
  : Tot (ps:(log & log){is_prefix (fst ps) l /\ is_suffix (snd ps) l /\ 
                    length l = length (fst ps) + 1 + length (snd ps)}) = 
    assert (length l >= 1);
    assert (pos op l + 1 <= length l);
    let r = (fst (split l (pos op l)), snd (split l (pos op l + 1))) in
    lemma_split l (length (fst r));
    lemma_count_slice l (pos op l);
    assert (is_prefix (fst r) l /\ is_suffix (snd r) l /\ length l = length (fst r) + 1 + length (snd r)); 
    assert (is_prefix (fst r) (Seq.snoc (fst r) op));
    lemma_split (Seq.snoc (fst r) op) (length (fst r)); 
    lemma_count_slice l (pos op l + 1);
    lemma_split l (length (fst r) + 1);
    r

let rec pre_suf_prop1 (l:log) (op:log_entry)
  : Lemma (requires mem op l)
          (ensures (let ps = pre_suf1 l op in
                    Seq.equal l (Seq.snoc (fst ps) op ++ (snd ps)))) (decreases length l) =
    
    match length l with
    |1 -> ()
    |_ -> if head l = op then () 
            else pre_suf_prop1 (tail l) op

let pre_suf_prop2 (l:log) (op:log_entry)
  : Lemma (requires mem op l)
          (ensures (let ps = pre_suf1 l op in
                    (forall e. mem e l <==> mem e (fst ps) \/ e = op \/ mem e (snd ps)))) =
  let ps = pre_suf1 l op in
  pre_suf_prop1 l op;
  lemma_mem_snoc (fst ps) op;
  lemma_mem_append (snoc (fst ps) op) (snd ps)

#pop-options

let distinct_append (a b:log)
  : Lemma (requires distinct_ops a /\ distinct_ops b /\
                    (forall id. mem_id id a ==> not (mem_id id b)))
          (ensures (distinct_ops (a ++ b)) /\
                   (forall id. mem_id id (a ++ b) <==> mem_id id a \/ mem_id id b)) =
  lemma_append_count_id a b

let rec not_id_not_ele (op:log_entry) (l:log)
  : Lemma (requires not (mem_id (fst op) l))
          (ensures not (mem op l)) (decreases length l) =
  if length l = 0 then ()
    else if head l = op then ()
      else not_id_not_ele op (tail l)
      
#push-options "--z3rlimit 30"
let lemma_mem_snoc_id (l:log) (op:log_entry)
  : Lemma (requires distinct_ops l /\ not (mem_id (fst op) l))
          (ensures (forall id. mem_id id (snoc l op) <==> mem_id id l \/ id = fst op) /\
                   (forall id. mem_id id l <==> mem_id id (snoc l op) /\ id <> fst op)) =
  lemma_append_count_id l (Seq.create 1 op)
#pop-options

// l = Seq.snoc (fst ps) op ++ (snd ps)
let pre_suf (l:log) (op:log_entry{mem op l})
  : Tot (ps:(log & log){ps = pre_suf1 l op /\
                    is_prefix (fst ps) l /\ is_suffix (snd ps) l /\ 
                    length l = length (fst ps) + 1 + length (snd ps) /\
                    Seq.equal l (Seq.snoc (fst ps) op ++ (snd ps)) /\
                    l = (Seq.snoc (fst ps) op ++ (snd ps)) /\
                    (forall e. mem e l <==> mem e (fst ps) \/ e = op \/ mem e (snd ps))}) =
    let r =  pre_suf1 l op in
    pre_suf_prop1 l op;
    pre_suf_prop2 l op;
    r
  
let lem_id (l p s :log) (o_id:nat)
  : Lemma (requires distinct_ops p /\ distinct_ops s /\ distinct_ops (p ++ s) /\ distinct_ops l /\
                    (forall id. mem_id id l <==> mem_id id p \/ id = o_id \/ mem_id id s) /\
                    (forall id. mem_id id (p ++ s) <==> mem_id id p \/ mem_id id s) /\
                    not (mem_id o_id (p ++ s)))
          (ensures (forall id. mem_id id (p ++ s) <==> mem_id id l /\ id <> o_id))
   = ()

#push-options "--z3rlimit 200"
let pre_suf_prop (l:log) (op:log_entry)
  : Lemma (requires distinct_ops l /\ mem op l)
          (ensures (let ps = pre_suf l op in
                    distinct_ops (fst ps) /\ distinct_ops (snd ps) /\ 
                    (forall id. mem_id id (fst ps) ==> not (mem_id id (snd ps))) /\
                    distinct_ops (fst ps ++ snd ps) /\
                    (forall id. mem_id id l <==> mem_id id (fst ps) \/ id = fst op \/ mem_id id (snd ps)) /\
                    (forall id. mem_id id (fst ps ++ snd ps) <==> mem_id id l /\ id <> fst op))) =
  let ps = pre_suf l op in
  distinct_invert_append (snoc (fst ps) op) (snd ps);
  distinct_invert_append (fst ps) (create 1 op);
  lemma_mem_snoc_id (fst ps) op;
  distinct_append (fst ps) (snd ps);
  lem_id l (fst ps) (snd ps) (fst op)
#pop-options

//conflict resolution
val resolve_conflict (x:log_entry) (y:log_entry{fst x <> fst y}) : (l:log{Seq.length l = 1 \/ Seq.length l = 2})

// returns true if there exists an operation op in log l such that
// 1. last_op and op are non-commutative
// 2. op is commutative with all the operations in the suffix of l
// 3. op should be applied after last_op according to resolve_conflict
let exists_triple (last_op:log_entry) (l:log)
  : (b:bool{b = true <==> (exists op. mem op l /\ fst last_op <> fst op /\
                         (let pre,suf = pre_suf l op in
                          not (commutative last_op op) /\
                          last (resolve_conflict last_op op) = op /\
                          commutative_seq op suf))}) =
  existsb (fun (op:log_entry) -> mem op l &&  fst last_op <> fst op &&
                              (let pre,suf = pre_suf l op in
                              not (commutative last_op op) &&
                              last (resolve_conflict last_op op) = op &&
                              commutative_seq op suf)) l

let fst_t (f,_,_) = f
let snd_t (_,s,_) = s
let thr_t (_,_,t) = t

// returns an operation op in l such that
// 1. last_op and op are non-commutative
// 2. op is commutative with all the operations in the suffix of l
// 3. op should be applied after last_op according to resolve_conflict
#push-options "--z3rlimit 200" 
let rec find_op (last_op:log_entry) (l l1:log)
  : Pure log_entry
         (requires length l > 0 /\ length l1 > 0 /\
                   (exists op. mem op l /\ mem op l1 /\ 
                          fst last_op <> fst op /\ 
                          not (commutative last_op op) /\
                          last (resolve_conflict last_op op) = op /\
                          (let _, suf = pre_suf l1 op in
                          commutative_seq op suf)))
         (ensures (fun op -> mem op l /\ mem op l1 /\ 
                          fst last_op <> fst op /\
                          not (commutative last_op op) /\
                          last (resolve_conflict last_op op) = op /\
                          (let _, suf = pre_suf l1 op in
                          commutative_seq op suf))) (decreases length l) =

 match length l with
  |1 -> last l
  |_ -> let pre, op = un_snoc l in
       if (mem op l1 && fst last_op <> fst op &&
           not (commutative last_op op) &&
           last (resolve_conflict last_op op) = op &&
           (let _, suf = pre_suf l1 op in
            commutative_seq op suf)) then op 
        else (lemma_mem_snoc pre op;
              find_op last_op pre l1)
              
// returns a triple such that 
// 1. l = (snoc prefix op) ++ suffix
// 2. last_op and op are non-commutative
// 3. op is commutative with all the operations in the suffix of l
// 4. op should be applied after last_op according to resolve_conflict
let find_triple (last_op:log_entry) (l:log{(exists_triple last_op l)}) 
  : (t:(log & log_entry & log) {mem (snd_t t) l /\ (fst_t t, thr_t t) = pre_suf l (snd_t t) /\
                                is_prefix (fst_t t) l /\ is_suffix (thr_t t) l /\
                                Seq.equal l ((Seq.snoc (fst_t t) (snd_t t)) ++ (thr_t t)) /\
                                length l = length (fst_t t) + 1 + length (thr_t t) /\

                                fst last_op <> fst (snd_t t) /\
                                not (commutative last_op (snd_t t)) /\
                                last (resolve_conflict last_op (snd_t t)) = snd_t t /\
                                commutative_seq (snd_t t) (thr_t t)}) =
  let op = find_op last_op l l in
  let pre, suf = pre_suf l op in
  (pre, op, suf)


// l is interleaving of l1 and l2
let rec is_interleaving (l l1 l2:log)
  : Tot eqtype (decreases %[Seq.length l1; Seq.length l2]) =

  // if l1 is empty, then l == l2
  (Seq.length l1 == 0 ==> l == l2)

  /\

  // similarly for l2 being empty
  ((Seq.length l1 > 0  /\ Seq.length l2 == 0) ==> l == l1)

  /\

  // if both are non-empty

  ((Seq.length l1 > 0 /\ Seq.length l2 > 0 /\
    exists_triple (snd (un_snoc l1)) l2) ==>
    (let pre, op, suf = find_triple (snd (un_snoc l1)) l2 in
      (exists l'.
         is_interleaving l' l1 (pre ++ suf) /\
         l == Seq.snoc l' op)))

   /\

   ((Seq.length l1 > 0 /\ Seq.length l2 > 0 /\
    not (exists_triple (snd (un_snoc l1)) l2) /\
    exists_triple (snd (un_snoc l2)) l1) ==>
    (let pre, op, suf = find_triple (snd (un_snoc l2)) l1 in
      (exists l'.
         is_interleaving l' (pre ++ suf) l2 /\
         l == Seq.snoc l' op)))

   /\

   ((Seq.length l1 > 0 /\ Seq.length l2 > 0 /\
    not (exists_triple (snd (un_snoc l1)) l2) /\
    not (exists_triple (snd (un_snoc l2)) l1)) ==>

    (let prefix1, last1 = un_snoc l1 in
     let prefix2, last2 = un_snoc l2 in
 
    (exists l'.
        fst last1 <> fst last2 /\
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

let lt_is_neq (lca s1:log)
  : Lemma (requires distinct_ops s1 /\ is_prefix lca s1 /\ 
                    (forall id id1. mem_id id lca /\ mem_id id1 (diff s1 lca) ==> lt id id1))
          (ensures (forall id. mem_id id lca ==> not (mem_id id (diff s1 lca)))) (decreases length lca) =
  let s = snd (split s1 (length lca)) in
  lemma_split s1 (length lca);
  lemma_append_count_id lca s

let lem_is_diff (s1 lca d:log)
  : Lemma (requires s1 = lca ++ d)
          (ensures is_prefix lca s1 /\ d = diff s1 lca) =
  lemma_split s1 (length lca);
  lemma_mem_append lca d;
  lemma_append_count lca d;
  assert (is_suffix d s1);
  ()

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

let rec split_prefix_forall (l:log) (a:log)
  : Lemma (requires is_prefix l a)
          (ensures (forall s. (seq_foldl s a = seq_foldl (seq_foldl s l) (diff a l))) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) = (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |1 -> ()
    |_ -> split_prefix_forall (tail l) (tail a)

let lem_last (a:log)
  : Lemma (ensures (length a > 0 ==> 
                      (let _, lst = un_snoc a in 
                       last a = lst))) = ()
                    
// returns the inverse state by undoing the last operation
#push-options "--z3rlimit 50"
let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{(v_of s = do (v_of i) (last (ops_of s))) /\
               (ops_of i = fst (un_snoc (ops_of s))) /\
               (ops_of s = snoc (ops_of i) (last (ops_of s))) /\
               length (ops_of i) = length (ops_of s) - 1 /\
               is_prefix (ops_of i) (ops_of s) /\
               (let _, last2 = un_snoc (ops_of s) in
                (lem_last (ops_of s);
                s == (do (v_of i) last2, hide (snoc (ops_of i) last2)))) /\
               (forall id. mem_id id (ops_of i) <==> mem_id id (ops_of s) /\ id <> fst (last (ops_of s)))}) = 
  lem_seq_foldl init_st (ops_of s);
  let p, l = un_snoc (ops_of s) in
  let r = seq_foldl init_st p in
  lemma_split (ops_of s) (length (ops_of s) - 1); 
  lemma_append_count_id p (snd (split (ops_of s) (length (ops_of s) - 1))); 
  distinct_invert_append p (snd (split (ops_of s) (length (ops_of s) - 1))); 
  (r, hide p)

let rec inverse_helper (s:concrete_st) (l':log) (op:log_entry)
  : Lemma 
    (ensures (let l = Seq.snoc l' op in 
              (seq_foldl s l = do (seq_foldl s l') op)))
    (decreases length l')
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |_ ->  inverse_helper (do s (head l')) (tail l') op

let lem_eq_is_equiv_st (x:concrete_st) (a b:log)
  : Lemma (requires (a = b /\ seq_foldl x a = seq_foldl x b))
          (ensures eq (seq_foldl x a) (seq_foldl x b))
          [SMTPat (eq (seq_foldl x a) (seq_foldl x b))] = 
  eq_is_equiv (seq_foldl x a) (seq_foldl x b)
  
let lem_eq_is_equiv (a b:log)
  : Lemma (requires (a = b /\ (forall x. seq_foldl x a = seq_foldl x b)))
          (ensures (forall x. eq (seq_foldl x a) (seq_foldl x b))) = ()

let lem_len_0 (l:log)
  : Lemma (requires length l = 0)
          (ensures (forall x. seq_foldl x l = x)) = ()

(*let lem_eq_is_equiv_c1_st (x:concrete_st) (l:log) (op hd:log_entry) (tl:log)
  : Lemma (requires eq (seq_foldl x (cons op l)) (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) /\
                    eq (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) (seq_foldl x (cons hd (cons op tl))))
          (ensures eq (seq_foldl x (cons op l)) (seq_foldl x (cons hd (cons op tl))))
          [SMTPat (eq (seq_foldl x (cons op l)) (seq_foldl x (cons hd (cons op tl))))]  = 
  transitive (seq_foldl x (cons op l)) 
             (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) 
             (seq_foldl x (cons hd (cons op tl)))*)

let lem_eq_is_equiv_c3_st (x:concrete_st) (l:log) (op hd:log_entry) (tl:log)
  : Lemma (requires eq (seq_foldl x (cons op l)) (seq_foldl (do x hd) (cons op tl)) /\
                    eq (seq_foldl (do x hd) (cons op tl)) (seq_foldl (do x hd) (snoc tl op)))
          (ensures eq (seq_foldl x (cons op l)) (seq_foldl (do x hd) (snoc tl op)))
          [SMTPat (eq (seq_foldl x (cons op l)) (seq_foldl (do x hd) (snoc tl op)))] = 
  transitive (seq_foldl x (cons op l)) 
             (seq_foldl (do x hd) (cons op tl))
             (seq_foldl (do x hd) (snoc tl op))

let lem_case1 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. seq_foldl x (cons op l) = (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl))))
          (decreases length l) = 
  let hd = head l in let tl = tail l in
  assert (is_prefix (cons op (create 1 hd)) (cons op l));
  assert (cons op l = cons op (cons hd tl));
  assert (cons op (cons hd tl) = cons op (append (create 1 hd) tl)); 
  append_assoc (create 1 op) (create 1 hd) tl;
  assert (cons op (append (create 1 hd) tl) = (cons op (create 1 hd)) ++ tl);
  assert ((cons op (cons hd tl)) = (cons op (create 1 hd)) ++ tl); 
  assert (cons op l = (cons op (create 1 hd)) ++ tl);

  lem_is_diff ((cons op (create 1 hd)) ++ tl) (cons op (create 1 hd)) tl;  
  assert (tl = diff (cons op l) (cons op (create 1 hd)));
  split_prefix_forall (cons op (create 1 hd)) (cons op l)
  
let lem_case3 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. seq_foldl x (cons hd (cons op tl)) = (seq_foldl (do x hd) (cons op tl)))))
                   (decreases length l) = 
  let hd = head l in let tl = tail l in
  assert (head (cons hd (cons op tl)) = hd); 
  lemma_tl hd (cons op tl);
  assert (tail (cons hd (cons op tl)) = (cons op tl));
  lem_seq_foldl_forall (cons hd (cons op tl))

let lem_case4 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. seq_foldl (do x hd) (snoc tl op) = (seq_foldl x (snoc l op)))))
          (decreases length l) = 
  let hd = head l in let tl = tail l in
  assert (head (cons hd (snoc tl op)) = hd);
  lemma_tl hd (snoc tl op);
  lemma_tail_snoc (cons hd tl) op;
  assert (tail (cons hd (snoc tl op)) = (snoc tl op));
  lem_seq_foldl_forall (cons hd (snoc tl op))

let rec lem_equiv_st_foldl_st (a b:concrete_st) (l:log)
  : Lemma (requires eq a b) 
          (ensures eq (seq_foldl a l) (seq_foldl b l))
          (decreases length l)
          [SMTPat (eq (seq_foldl a l) (seq_foldl b l))] =
  match length l with
  |0 -> ()
  |_ -> lem_do a b (head l);
       lem_equiv_st_foldl_st (do a (head l)) (do b (head l)) (tail l)
                         
let lem_equiv_st_foldl (a b:log) (l:log)
  : Lemma (ensures (forall x. eq (seq_foldl x a) (seq_foldl x b) ==>
                         eq (seq_foldl (seq_foldl x a) l) (seq_foldl (seq_foldl x b) l))) = ()
                         
#push-options "--z3rlimit 400"
let lem_case2_help (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. eq (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) 
                             (seq_foldl (seq_foldl x (cons hd (create 1 op))) tl))))
          (decreases length l) = 
  let hd = head l in let tl = tail l in
  commutative_prop op hd;
  assert (forall x. eq (seq_foldl x (cons op (create 1 hd))) (seq_foldl x (cons hd (create 1 op))));
  lem_equiv_st_foldl (cons op (create 1 hd)) (cons hd (create 1 op)) tl

let lem_case2_help1 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. eq (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) 
                             (seq_foldl (seq_foldl x (cons hd (create 1 op))) tl))))
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. seq_foldl (seq_foldl x (cons hd (create 1 op))) tl =
                          seq_foldl x (cons hd (cons op tl))))) = 
  let hd = head l in let tl = tail l in
  assert (is_prefix (cons hd (create 1 op)) (cons hd (cons op tl)));
  append_assoc (create 1 hd) (create 1 op) tl;
  assert (cons hd (cons op tl) = (cons hd (create 1 op) ++ tl));
  lem_is_diff (cons hd (cons op tl)) (cons hd (create 1 op)) tl;
  assert (tl = diff (cons hd (cons op tl)) (cons hd (create 1 op)));
  split_prefix_forall (cons hd (create 1 op)) (cons hd (cons op tl));
  ()

let lem_case2 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. eq (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) 
                             (seq_foldl (seq_foldl x (cons hd (create 1 op))) tl) /\
                          seq_foldl (seq_foldl x (cons hd (create 1 op))) tl =
                          seq_foldl x (cons hd (cons op tl)))))
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. eq (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) (seq_foldl x (cons hd (cons op tl)))))) = ()

let rec lem_foldl_comm (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l)
          (ensures (forall x. eq (seq_foldl x (cons op l)) (seq_foldl x (snoc l op)))) (decreases length l) =
  match length l with
  |0 -> lemma_empty l; 
       append_empty_r (create 1 op); 
       append_empty_l (create 1 op);
       assert (forall x. seq_foldl x (cons op l) = seq_foldl x (snoc l op));
       lem_eq_is_equiv (cons op l) (snoc l op)
      
  |_ -> let hd = head l in let tl = tail l in
       assert (commutative_seq op (tail l) /\ distinct_ops (tail l));
       lem_foldl_comm tl op;  
       lem_case1 l op; // eq (seq_foldl x (cons op l)) (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl))
       lem_case2_help l op;
       lem_case2_help1 l op;
       lem_case2 l op; // eq (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) (seq_foldl x (cons hd (cons op tl))));      
       lem_case3 l op; // eq (seq_foldl x (cons hd (cons op tl))) (seq_foldl (do x hd) (cons op tl)))       
       assert (forall x. eq (seq_foldl (do x hd) (cons op tl)) (seq_foldl (do x hd) (snoc tl op))); // from IH       
       lem_case4 l op // eq (seq_foldl (do x hd) (snoc tl op)) (seq_foldl x (snoc l op)));

let lem_seq_foldl_split (x:concrete_st) (p:log) (s:log)
  : Lemma (ensures seq_foldl (seq_foldl x p) s = (seq_foldl x (p ++ s)))
          (decreases length p) =
  lem_is_diff (p ++ s) p s;
  split_prefix x p (p ++ s)

#push-options "--z3rlimit 300"
let lem_seq_foldl_op (x:concrete_st) (l:log) (op:log_entry)
  : Lemma (requires distinct_ops l /\ mem op l /\
                    (let _, s = pre_suf l op in commutative_seq op s))
          (ensures (let p,s = pre_suf l op in
                      eq (seq_foldl x l) (do (seq_foldl x (p ++ s)) op)))
          (decreases length l) = 
  let pre, suf = pre_suf l op in
  assert (commutative_seq op suf);
  lem_foldl_comm suf op;
  assert (forall x. eq (seq_foldl x (cons op suf)) (seq_foldl x (snoc suf op)));
  split_prefix x pre l;
  pre_suf_prop l op;
  append_assoc pre (create 1 op) suf;
  assert (l = (snoc pre op) ++ suf /\ l = pre ++ (cons op suf)); 
  lem_is_diff l pre (cons op suf);

  pre_suf_prop l op;
  assert (distinct_ops (pre ++ suf));
  assert (not (mem_id (fst op) (pre ++ suf)));
  distinct_append pre suf;
  distinct_append (pre ++ suf) (create 1 op);
  append_assoc pre suf (create 1 op);
  assert (distinct_ops (pre ++ (snoc suf op)));

  append_assoc pre suf (create 1 op); 
  lem_is_diff (snoc (pre ++ suf) op) (pre ++ suf) (create 1 op);
  assert (is_prefix (pre ++ suf) (snoc (pre ++ suf) op));
  split_prefix x (pre ++ suf) (snoc (pre ++ suf) op); 
  assert (length (snoc (pre ++ suf) op) > 0);
  lem_seq_foldl x (snoc (pre ++ suf) op);
  lem_last (snoc (pre ++ suf) op); 
  un_snoc_snoc (pre ++ suf) op;
  
  assert (seq_foldl x l = seq_foldl (seq_foldl x pre) (cons op suf));
  assert (eq (seq_foldl x l) (seq_foldl (seq_foldl x pre) (snoc suf op))); 
  lem_seq_foldl_split x pre (snoc suf op);

  assert (seq_foldl x (snoc (pre ++ suf) op) = do (seq_foldl x (pre ++ suf)) op);
  assert (seq_foldl x (snoc (pre ++ suf) op) = seq_foldl x (pre ++ (snoc suf op)));
  assert (seq_foldl x (pre ++ (snoc suf op)) = seq_foldl (seq_foldl x pre) (snoc suf op));
  
  assert (seq_foldl (seq_foldl x pre) (snoc suf op) = do (seq_foldl x (pre ++ suf)) op);
  
  eq_is_equiv (seq_foldl (seq_foldl x pre) (snoc suf op)) (do (seq_foldl x (pre ++ suf)) op);
  transitive (seq_foldl x l) (seq_foldl (seq_foldl x pre) (snoc suf op)) (do (seq_foldl x (pre ++ suf)) op)

// returns the inverse state by undoing operation op in (ops_of s)
let inverse_st_op (s:st) (op:log_entry{mem op (ops_of s) /\ 
                           (let _, suf = pre_suf (ops_of s) op in
                            commutative_seq op suf)})
  : GTot (i:st{(let (pre,suf) = pre_suf (ops_of s) op in
               eq (v_of s) (do (v_of i) op) /\
               (ops_of i = (pre ++ suf)) /\
               (ops_of s = (Seq.snoc pre op) ++ suf) /\
               is_prefix pre (ops_of s) /\ is_prefix pre (ops_of i) /\
               length (ops_of i) = length (ops_of s) - 1 /\
               (forall id. (mem_id id (ops_of i) \/ id = fst op) <==> mem_id id (ops_of s)) /\
               (forall id. mem_id id (ops_of i) <==> (mem_id id (ops_of s) /\ id <> fst op)))}) = 
  let pre, suf = pre_suf (ops_of s) op in
  pre_suf_prop (ops_of s) op;
  lem_seq_foldl_op init_st (ops_of s) op;
  let v_i = seq_foldl init_st (pre ++ suf) in
  assert (eq (v_of s) (do v_i op));
  (v_i, hide (pre ++ suf))

let lem_inverse (lca s1:log)
  : Lemma (requires is_prefix lca s1 /\
                    Seq.length s1 > Seq.length lca)
          (ensures (is_prefix lca (fst (un_snoc s1)))) 
  = lemma_split (fst (un_snoc s1)) (length lca)

let lem_inverse_op (lca s1:log) (op:log_entry)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\
                    (let _, suf = pre_suf s1 op in
                     let _, sufd = pre_suf (diff s1 lca) op in
                     suf = sufd))
          (ensures (let pre, suf = pre_suf s1 op in
                   (is_prefix lca (pre ++ suf)) /\
                   (let pred, sufd = pre_suf (diff s1 lca) op in
                     (pre ++ suf = lca ++ (pred ++ sufd)))))
  = let pre, suf = pre_suf s1 op in 
    let pred, sufd = pre_suf (diff s1 lca) op in
    assert ((snoc pre op) ++ suf = lca ++ ((snoc pred op) ++ sufd));  
    append_assoc lca pred sufd;
    append_assoc lca (snoc pred op) sufd;
    assert ((snoc pre op) ++ suf = (lca ++ snoc pred op) ++ sufd);  
    append_assoc lca pred (create 1 op);
    assert (snoc pre op ++ suf = snoc (lca ++ pred) op ++ sufd);    
    lemma_snoc_inj pre (lca ++ pred) op op;
    assert (pre = lca ++ pred);
    ()

let lem_equal_distinct (a b:log)
  : Lemma (requires distinct_ops a /\ a = b)
          (ensures distinct_ops b) = ()

let rec mem_ele_id (op:log_entry) (l:log)
  : Lemma (requires mem op l)
          (ensures mem_id (fst op) l) (decreases length l) =
  if head l = op then ()
    else mem_ele_id op (tail l)

(*let rec not_id_not_ele (op:log_entry) (l:log)
  : Lemma (requires not (mem_id (fst op) l))
          (ensures not (mem op l)) (decreases length l) =
  if length l = 0 then ()
    else if head l = op then ()
      else not_id_not_ele op (tail l)*)

let rec lem_count_1 (a a1 b b1:log) (op:log_entry)
  : Lemma (requires (snoc a op ++ a1 = snoc b op ++ b1) /\ 
                     not (mem_id (fst op) a) /\ not (mem_id (fst op) a1) /\
                     not (mem_id (fst op) b) /\ not (mem_id (fst op) b1) /\
                     count_id (fst op) (snoc a op ++ a1) = 1)
          (ensures length a1 = length b1) (decreases length a) =
  match length a with
  |0 -> lemma_empty a;
       append_assoc a (create 1 op) a1;
       append_empty_l (cons op a1);
       lemma_append_inj (snoc a op) a1 (snoc b op) b1
  |_ -> lemma_eq_intro (tail (snoc a op ++ a1)) (snoc (tail a) op ++ a1); 
       lemma_eq_intro (tail (snoc b op ++ b1)) (snoc (tail b) op ++ b1); 
       lem_count_1 (tail a) a1 (tail b) b1 op

let append_cons_snoc1 (u: log) (x:log_entry) (v:log)
    : Lemma (equal (u ++ (snoc v x)) (snoc (u ++ v) x)) = ()

let rec count_1 (l:log)
  : Lemma (requires distinct_ops l)
          (ensures (forall id. mem_id id l ==> count_id id l = 1)) (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> count_1 (tail l)

let not_mem_id (a:log) (op:log_entry)
  : Lemma (requires (forall id. mem_id id a ==> not (mem_id id (create 1 op))))
          (ensures not (mem_id (fst op) a)) = ()

let lemma_mem_snoc1 (l:log) (op:log_entry)
  : Lemma (ensures (forall id. mem_id id (snoc l op) <==> mem_id id l \/ id = fst op)) = 
  lemma_append_count_id l (Seq.create 1 op)

let not_mem_id1 (a:log) (op:log_entry) (b:log)
  : Lemma (requires (forall id. mem_id id (snoc a op) ==> not (mem_id id b)))
          (ensures  not (mem_id (fst op) b)) =
  lemma_append_count_id a (Seq.create 1 op)

let lem_not_append (a b:log) (id:nat)
  : Lemma (requires not (mem_id id a) /\ not (mem_id id b) /\ distinct_ops a /\ distinct_ops b)
          (ensures not (mem_id id (a ++ b))) =
 lemma_append_count_id a b          

#push-options "--z3rlimit 200"
let lem_suf_equal1 (lca s1:log) (op:log_entry)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\ distinct_ops s1)
          (ensures (let pre, suf = pre_suf s1 op in
                    not (mem_id (fst op) pre) /\
                    not (mem_id (fst op) suf))) =
  let pre, suf = pre_suf s1 op in
  pre_suf_prop s1 op;
  distinct_invert_append (snoc pre op) suf;
  distinct_invert_append pre (create 1 op);
  not_mem_id pre op;
  lemma_mem_snoc1 pre op

let lem_suf_equal2 (lca s1:log) (op:log_entry)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\ distinct_ops s1)
          (ensures (let pred, sufd = pre_suf (diff s1 lca) op in
                    not (mem_id (fst op) pred) /\
                    not (mem_id (fst op) sufd) /\
                    not (mem_id (fst op) lca) /\
                    not (mem_id (fst op) (lca ++ pred)))) =
    distinct_invert_append lca (diff s1 lca);
    mem_ele_id op (diff s1 lca);
    lem_diff s1 lca;
    let pred, sufd = pre_suf (diff s1 lca) op in
    pre_suf_prop (diff s1 lca) op;
    distinct_invert_append (snoc pred op) sufd;
    distinct_invert_append pred (create 1 op);
    not_mem_id pred op;
    lemma_mem_snoc1 pred op;
    lem_not_append lca pred (fst op)

let lem_suf_equal2_last (lca s1:log)
  : Lemma (requires is_prefix lca s1 /\ length (diff s1 lca) > 0 /\ distinct_ops s1)
          (ensures (let _, lastop = un_snoc s1 in
                    not (mem_id (fst lastop) lca))) =
    distinct_invert_append lca (diff s1 lca); 
    let pre, lst = un_snoc s1 in
    lem_diff s1 lca;
    mem_ele_id lst (diff s1 lca)

let lem_suf_equal3 (lca s1:log) (op:log_entry)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\ distinct_ops s1)
          (ensures (let pre, suf = pre_suf s1 op in 
                    let pred, sufd = pre_suf (diff s1 lca) op in
                    count_id (fst op) (snoc pre op ++ suf) = 1 /\
                    snoc pre op ++ suf = snoc (lca ++ pred) op ++ sufd)) =
  count_1 s1;
  let pre, suf = pre_suf s1 op in
  let pred, sufd = pre_suf (diff s1 lca) op in
  pre_suf_prop s1 op;
  pre_suf_prop (diff s1 lca) op;
  assert (snoc pre op ++ suf = lca ++ ((snoc pred op) ++ sufd)); 
  append_assoc lca (snoc pred op) sufd;
  assert (lca ++ ((snoc pred op) ++ sufd) = (lca ++ snoc pred op) ++ sufd);  
  append_cons_snoc1 lca op pred; 
  lemma_eq_elim (lca ++ (snoc pred op)) (snoc (lca ++ pred) op);
  assert ((lca ++ (snoc pred op)) = (snoc (lca ++ pred) op));
  assert (lca ++ ((snoc pred op) ++ sufd) = snoc (lca ++ pred) op ++ sufd); 
  assert (snoc pre op ++ suf = snoc (lca ++ pred) op ++ sufd);  
  ()

let lem_suf_equal (lca s1:log) (op:log_entry)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\ distinct_ops s1)
          (ensures (let pre, suf = pre_suf s1 op in
                    let pred, sufd = pre_suf (diff s1 lca) op in
                    suf = sufd /\
                    pre = lca ++ pred))
  = let pre, suf = pre_suf s1 op in
    let pred, sufd = pre_suf (diff s1 lca) op in
    lem_suf_equal1 lca s1 op;
    lem_suf_equal2 lca s1 op;
    lem_suf_equal3 lca s1 op;
    lem_count_1 pre suf (lca ++ pred) sufd op;
    lemma_append_inj (snoc pre op) suf (snoc (lca ++ pred) op) sufd;
    un_snoc_snoc pre op;
    un_snoc_snoc (lca ++ pred) op

let lem_suf_equal4 (s1:log) (op:log_entry)
  : Lemma (requires mem op s1 /\ distinct_ops s1)
          (ensures (let pre, suf = pre_suf s1 op in
                    not (mem_id (fst op) pre) /\
                    not (mem_id (fst op) suf))) =
  let pre, suf = pre_suf s1 op in
  pre_suf_prop s1 op;
  distinct_invert_append (snoc pre op) suf;
  distinct_invert_append pre (create 1 op);
  not_mem_id pre op;
  lemma_mem_snoc1 pre op

let lem_id_not_snoc (l l1:log) (op op1:log_entry)
  : Lemma (requires not (mem_id (fst op) l) /\ mem_id (fst op1) l /\
                    not (mem_id (fst op1) l1))
          (ensures fst op1 <> fst op /\
                   not (mem_id (fst op1) (snoc l1 op))) = 
  assert (fst op1 <> fst op); 
  assert (not (mem_id (fst op1) (create 1 op))); 
  lemma_mem_snoc1 l1 op

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

let lem_id_s2' (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (let b',lastop = un_snoc b in
                    not (mem_id (fst lastop) l) /\
                    not (mem_id (fst lastop) a) /\
                    not (mem_id (fst lastop) b'))) = 
  let b', lastop = un_snoc b in
  lemma_append_count_id b' (create 1 lastop);
  distinct_invert_append b' (create 1 lastop);
  //assert (not (mem_id (fst lastop) b'));
  lem_suf_equal2_last l b;
  //assert (not (mem_id (fst lastop) l) );
  lem_diff a l;
  lastop_diff l b;
  //assert (not (mem_id (fst lastop) a));
  ()

let lem_id_s1' (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (let a',lastop = un_snoc a in
                    not (mem_id (fst lastop) l) /\
                    not (mem_id (fst lastop) a') /\
                    not (mem_id (fst lastop) b))) = 
  let a', lastop = un_snoc a in
  lemma_append_count_id a' (create 1 lastop);
  distinct_invert_append a' (create 1 lastop);
  //assert (not (mem_id (fst lastop) a')); 
  lem_suf_equal2_last l a;
  //assert (not (mem_id (fst lastop) l) );
  lem_diff b l;
  lastop_diff l a;
  //assert (not (mem_id (fst lastop) b));
  () 
  
let inverse_diff_id (l a b:log)
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

let inverse_diff_id1 (l a b:log)
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

let inverse_diff_id2 (l a b:log)
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

let inverse_diff_id_last2 (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (let pre2, last2 = un_snoc b in
                    let pre1, last1 = un_snoc a in
                    not (mem_id (fst last2) l) /\
                    not (mem_id (fst last2) pre1) /\
                    not (mem_id (fst last2) a) /\
                    not (mem_id (fst last2) pre2))) =
  let pre2, last2 = un_snoc b in
  let pre1, last1 = un_snoc a in
  lt_is_neq l b; 
  assert (forall id. mem_id id l ==> not (mem_id id (diff b l))); 
  lastop_diff l b;
  assert (not (mem_id (fst last2) l)); 
  lem_diff a l;
  assert (not (mem_id (fst last2) (diff a l)));
  assert (not (mem_id (fst last2) a)); 
  lemma_split a (length a - 1); 
  lemma_mem_snoc1 pre1 last1;
  assert (not (mem_id (fst last2) pre1));
  lemma_split b (length b - 1); 
  lemma_append_count_id pre2 (create 1 last2);
  distinct_invert_append pre2 (create 1 last2);
  not_mem_id pre2 last2;
  assert (not (mem_id (fst last2) pre2)); ()

let inverse_diff_id_last1 (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (let pre2, last2 = un_snoc b in
                    let pre1, last1 = un_snoc a in
                    not (mem_id (fst last1) l) /\
                    not (mem_id (fst last1) pre2) /\
                    not (mem_id (fst last1) b) /\
                    not (mem_id (fst last1) pre1))) =
  let pre2, last2 = un_snoc b in
  let pre1, last1 = un_snoc a in
  lt_is_neq l a; 
  assert (forall id. mem_id id l ==> not (mem_id id (diff a l))); 
  lastop_diff l a;
  assert (not (mem_id (fst last1) l)); 
  lem_diff b l;
  assert (not (mem_id (fst last1) (diff b l)));
  assert (not (mem_id (fst last1) b)); 
  lemma_split b (length b - 1); 
  lemma_mem_snoc1 pre2 last2;
  assert (not (mem_id (fst last1) pre2));
  lemma_split a (length a - 1); 
  lemma_append_count_id pre1 (create 1 last1);
  distinct_invert_append pre1 (create 1 last1);
  not_mem_id pre1 last1;
  assert (not (mem_id (fst last1) pre1)); ()

let inverse_diff_id_inv1' (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))) /\
                    (let _, last2 = un_snoc b in
                    exists_triple last2 (diff a l)))
          (ensures (let _, last2 = un_snoc b in
                    let (pre1, op1, suf1) = find_triple last2 (diff a l) in
                    not (mem_id (fst op1) l) /\
                    not (mem_id (fst op1) (pre1 ++ suf1)) /\
                    not (mem_id (fst op1) b))) = 
  let _, last2 = un_snoc b in
  let (pre1, op1, suf1) = find_triple last2 (diff a l) in
  pre_suf_prop (diff a l) op1; 
  assert (not (mem_id (fst op1) (pre1 ++ suf1))); 
  lem_suf_equal2 l a op1;
  assert (not (mem_id (fst op1) l));
  lem_diff b l;
  mem_ele_id op1 (diff a l);
  assert (not (mem_id (fst op1) (diff b l)));
  assert (not (mem_id (fst op1) b));
  ()
                    
let inverse_diff_id_inv2' (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))) /\
                    (let _, last1 = un_snoc a in
                    exists_triple last1 (diff b l)))
          (ensures (let _, last1 = un_snoc a in
                    let (pre2, op2, suf2) = find_triple last1 (diff b l) in
                    not (mem_id (fst op2) l) /\
                    not (mem_id (fst op2) (pre2 ++ suf2)) /\
                    not (mem_id (fst op2) a))) = 
  let _, last1 = un_snoc a in
  let (pre2, op2, suf2) = find_triple last1 (diff b l) in
  pre_suf_prop (diff b l) op2; 
  assert (not (mem_id (fst op2) (pre2 ++ suf2))); 
  lem_suf_equal2 l b op2;
  assert (not (mem_id (fst op2) l));
  lem_diff a l;
  mem_ele_id op2 (diff b l);
  assert (not (mem_id (fst op2) (diff a l)));
  assert (not (mem_id (fst op2) a));
  ()
                    
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

// l is an interleaving of s1 - lca and s2 - lca
let interleaving_predicate (l:log) (lca s1:st)
  (s2:st{is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2)}) =
  is_interleaving l (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) /\
  eq (seq_foldl (v_of lca) l)
     (concrete_merge (v_of lca) (v_of s1) (v_of s2))

let common_pre (lca s1 s2:st) =
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
  Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))

let id_not_eq (l l1:log) (id id1:nat)
  : Lemma (requires (forall id. mem_id id l ==> not (mem_id id l1)) /\
                    mem_id id l /\ mem_id id1 l1)
          (ensures id <> id1) = ()

val lem_trans_merge_s1' (lca s1 s2 s1':concrete_st)
  : Lemma (requires eq s1 s1')
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1' s2))

val lem_trans_merge_s2' (lca s1 s2 s2':concrete_st)
  : Lemma (requires eq s2 s2')
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1 s2'))
                      
// branch s1 does not see new operations
val linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

// branch s2 does not see new operations
val linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

val linearizable_gt0_s1'_op (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\
                     (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                      suf2 = snd (pre_suf (ops_of s2) op2))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let s2' = inverse_st_op s2 op2 in
                       eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) op2)
                          (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') op2))))

val linearizable_gt0_s2'_op (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     exists_triple last2 (diff (ops_of s1) (ops_of lca)) /\
                     (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                      suf1 = snd (pre_suf (ops_of s1) op1))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let (pre1, op1, suf2) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    let s1' = inverse_st_op s1 op1 in
                       eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) op1)
                          (concrete_merge (v_of lca) (do (v_of s1') op1) (v_of s2))))

val linearizable_gt0_s1' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last1 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))

val linearizable_gt0_s2' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) <> last1 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))


(*// convergence theorem
val convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ eq s1' (do s1 o) /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures eq (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1'))*)

