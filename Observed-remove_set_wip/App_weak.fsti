module App_weak

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

// concrete do pre-condition
val concrete_do_pre (_:concrete_st) (_:log_entry) : prop

// apply an operation to a state
val do (s:concrete_st) (o:log_entry{concrete_do_pre s o}) : concrete_st

val lem_do (a b:concrete_st) (op:log_entry)
   : Lemma (requires concrete_do_pre a op /\ eq a b)
           (ensures concrete_do_pre b op /\ eq (do a op) (do b op))

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
  : Lemma (requires eq_sm st_s st /\ concrete_do_pre st op)
          (ensures eq_sm (do_s st_s op) (do st op))

////////////////////////////////////////////////////////////////

// concrete_do_pre is maintained in fold_left
let rec foldl_prop (x:concrete_st) (l:log) : Tot prop (decreases length l) =
  match length l with
  |0 -> True
  |1 -> concrete_do_pre x (head l)
  |_ -> concrete_do_pre x (head l) /\ foldl_prop (do x (head l)) (tail l)

// applying a log of operations to a concrete state
let rec seq_foldl (x:concrete_st) (l:log{foldl_prop x l}) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |1 -> do x (head l)
  |_ -> seq_foldl (do x (head l)) (tail l)                   

// property of seq_foldl
let rec lem_seq_foldl (x:concrete_st) (l:log)
  : Lemma (requires foldl_prop x l)
          (ensures (length l > 0 ==> foldl_prop x (fst (un_snoc l)) /\ 
                   concrete_do_pre (seq_foldl x (fst (un_snoc l))) (last l) /\
                   (seq_foldl x l = do (seq_foldl x (fst (un_snoc l))) (last l))))
          (decreases length l) =
  match length l with
  |0 -> ()
  |1 -> ()
  |_ -> lem_seq_foldl (do x (head l)) (tail l)

// valid state
let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  foldl_prop init_st (ops_of s) /\
  (v_of s = seq_foldl init_st (ops_of s))

type st = s:st0{valid_st s}

//operations x and y are commutative
val commutative (x y:log_entry) :  bool

val comm_symmetric (x y:log_entry) 
  : Lemma (requires commutative x y)
          (ensures commutative y x)
          [SMTPat (commutative x y)]
          
// if x and y are commutative ops, applying them in any order should give equivalent results
val commutative_prop (x y:log_entry) 
  : Lemma (requires commutative x y /\ (forall s. foldl_prop s (cons x (cons y empty)) /\
                                            foldl_prop s (cons y (cons x empty))))
          (ensures (forall s. eq (seq_foldl s (cons x (cons y empty))) (seq_foldl s (cons y (cons x empty)))))

let rec forallb (#a:eqtype) (f:a -> bool) (l:seq a)
  : Tot (b:bool{(forall e. mem e l ==> f e) <==> b = true}) (decreases length l) =
  match length l with
  |0 -> true
  |_ -> if f (head l) then forallb f (tail l) else false

//commutativity for a sequence of operation
let commutative_seq (x:log_entry) (l:log) : bool =
  forallb (fun e -> commutative x e) l

let rec foldl_comm_prop (x:log_entry) (l:log{commutative_seq x l}) : Tot prop (decreases length l) =
  match length l with
  |0 -> True
  |1 -> (forall s. foldl_prop s (cons x (cons (head l) empty)) /\
             foldl_prop s (cons (head l) (cons x empty)))
  |_ -> commutative_seq (head l) (tail l) /\ foldl_comm_prop (head l) (tail l)

#push-options "--z3rlimit 200"
let rec lem_seq_foldl_op1 (x:concrete_st) (suf:log) (op:log_entry)
  : Lemma (requires //distinct_ops suf /\ distinct_ops (cons op suf) /\ distinct_ops (snoc suf op) /\
                    foldl_prop x (cons op suf) /\ foldl_prop x (snoc suf op) /\
                    commutative_seq op suf /\
                    foldl_comm_prop op suf)
          (ensures (eq (seq_foldl x (cons op suf)) (seq_foldl x (snoc suf op))))
          (decreases length suf) = admit();
  match length suf with
  |0 -> lemma_empty suf; append_empty_r suf; append_empty_l suf;
       assume (cons op suf = create 1 op);
       assume (snoc suf op = create 1 op);
       eq_is_equiv (seq_foldl x (cons op suf)) (seq_foldl x (snoc suf op))
  |1 -> assume (commutative op (head suf) /\ commutative (head suf) op);
       commutative_prop op (head suf); admit()
  |_ -> lem_seq_foldl_op1 x (tail suf) op

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
val resolve_conflict (x y:log_entry) : (l:log{Seq.length l = 1 \/ Seq.length l = 2})

// returns true if there exists an operation op in log l such that
// 1. last_op and op are non-commutative
// 2. op is commutative with all the operations in the suffix of l
// 3. op should be applied after last_op according to resolve_conflict
let exists_triple (last_op:log_entry) (l:log)
  : (b:bool{b = true <==> (exists op. mem op l /\
                         (let pre,suf = pre_suf l op in
                          not (commutative last_op op) /\
                          last (resolve_conflict last_op op) = op /\
                          commutative_seq op suf))}) =
  existsb (fun (op:log_entry) -> mem op l && 
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
                   (exists op. mem op l /\ mem op l1 /\ not (commutative last_op op) /\
                          last (resolve_conflict last_op op) = op /\
                          (let _, suf = pre_suf l1 op in
                          commutative_seq op suf)))
         (ensures (fun op -> mem op l /\ mem op l1 /\ not (commutative last_op op) /\
                          last (resolve_conflict last_op op) = op /\
                          (let _, suf = pre_suf l1 op in
                          commutative_seq op suf))) (decreases length l) =

 match length l with
  |1 -> last l
  |_ -> let pre, op = un_snoc l in
       if (mem op l1 && not (commutative last_op op) &&
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
  (Seq.length l1 = 0 ==> l = l2)

  /\

  // similarly for l2 being empty
  ((Seq.length l1 > 0  /\ Seq.length l2 = 0) ==> l = l1)

  /\

  // if both are non-empty

  ((Seq.length l1 > 0 /\ Seq.length l2 > 0) ==>

    (let prefix1, last1 = un_snoc l1 in
     let prefix2, last2 = un_snoc l2 in
     
     (exists_triple last1 l2 /\
       (let (p2, op2, s2) = find_triple last1 l2 in
       (exists l'.
           is_interleaving l' l1 (p2 ++ s2) /\
           l = Seq.snoc l' op2)))

      \/

      (exists_triple last2 l1 /\
       (let (p1, op1, s1) = find_triple last2 l1 in
       (exists l'.
           is_interleaving l' (p1 ++ s1) l2 /\
           l = Seq.snoc l' op1)))

      \/

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
          
// concrete merge pre-condition
val concrete_merge_pre (lca a b:concrete_st) : prop

// concrete merge operation
val concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) : concrete_st

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

let lem_diff (s1 l:log)
  : Lemma (requires distinct_ops s1 /\ is_prefix l s1)
          (ensures distinct_ops (diff s1 l) /\ (forall id. mem_id id (diff s1 l) <==> mem_id id s1 /\ not (mem_id id l)) /\
                   (Seq.length s1 > Seq.length l ==> last s1 = last (diff s1 l) /\ Seq.length (diff s1 l) > 0))
  = let s = snd (split s1 (length l)) in
    lemma_split s1 (length l);
    lemma_append_count_id l s
    
let rec split_prefix (s:concrete_st) (l:log) (a:log)
  : Lemma (requires is_prefix l a /\ foldl_prop s a)
          (ensures foldl_prop s l /\ foldl_prop (seq_foldl s l) (diff a l) /\
                   (seq_foldl s a = seq_foldl (seq_foldl s l) (diff a l)) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) = (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |1 -> ()
    |_ -> split_prefix (do s (head l)) (tail l) (tail a)

// returns the inverse state by undoing the last operation
#push-options "--z3rlimit 50"
let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{(concrete_do_pre (v_of i) (last (ops_of s))) /\
               (v_of s = do (v_of i) (last (ops_of s))) /\
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

let rec inverse_helper (s:concrete_st) (l':log) (op:log_entry)
  : Lemma 
    (requires (foldl_prop s l' /\ concrete_do_pre (seq_foldl s l') op))
    (ensures (let l = Seq.snoc l' op in 
              foldl_prop s l /\
              (seq_foldl s l = do (seq_foldl s l') op))) (decreases length l')
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |_ ->  inverse_helper (do s (head l')) (tail l') op
    
#push-options "--z3rlimit 150"
val lem_seq_foldl_op (x:concrete_st) (l:log) (op:log_entry)
  : Lemma (requires distinct_ops l /\ mem op l /\ foldl_prop x l /\
                    (let _, suf = pre_suf l op in commutative_seq op suf))
          (ensures (let p,s = pre_suf l op in
                      foldl_prop x (p ++ s) /\ 
                      concrete_do_pre (seq_foldl x (p ++ s)) op /\                 
                      eq (seq_foldl x l) (do (seq_foldl x (p ++ s)) op)))
          (decreases length l)

// returns the inverse state by undoing operation op in (ops_of s)
let inverse_st_op (s:st) (op:log_entry{mem op (ops_of s) /\ 
                           (let _, suf = pre_suf (ops_of s) op in
                            commutative_seq op suf)})
  : GTot (i:st{(let (pre,suf) = pre_suf (ops_of s) op in
               (concrete_do_pre (v_of i) op) /\
               eq (v_of s) (do (v_of i) op) /\
               (ops_of i = (pre ++ suf)) /\
               (ops_of s = (Seq.snoc pre op) ++ suf) /\
               is_prefix pre (ops_of s) /\ is_prefix pre (ops_of i) /\
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

let lem_suf_equal2_last (lca s1:log) (op:log_entry)
  : Lemma (requires is_prefix lca s1 /\ length (diff s1 lca) > 0 /\ distinct_ops s1)
          (ensures (let _, last = un_snoc s1 in
                    not (mem_id (fst last) lca))) =
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
          (ensures (let _, suf = pre_suf s1 op in
                    let _, sufd = pre_suf (diff s1 lca) op in
                    suf = sufd))
  = let pre, suf = pre_suf s1 op in
    let pred, sufd = pre_suf (diff s1 lca) op in
    lem_suf_equal1 lca s1 op;
    lem_suf_equal2 lca s1 op;
    lem_suf_equal3 lca s1 op;
    lem_count_1 pre suf (lca ++ pred) sufd op;
    lemma_append_inj (snoc pre op) suf (snoc (lca ++ pred) op) sufd
                     
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

let inverse_diff_id (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))))
          (ensures (forall id. mem_id id (diff (fst (un_snoc a)) l) ==> not (mem_id id (diff b l))))
  = un_snoc_prop a;
    lem_diff a l; 
    lem_inverse l a;
    lem_diff (fst (un_snoc a)) l
    
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
  (s2:st{concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\ 
         is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2)}) =
  is_interleaving l (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) /\
  foldl_prop (v_of lca) l /\
  eq (seq_foldl (v_of lca) l)
     (concrete_merge (v_of lca) (v_of s1) (v_of s2))

type common_pre (lca s1 s2:st) =
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
  Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
  concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))

let id_not_eq (l l1:log) (id id1:nat)
  : Lemma (requires (forall id. mem_id id l ==> not (mem_id id l1)) /\
                    mem_id id l /\ mem_id id1 l1)
          (ensures id <> id1) = ()

// concrete_merge_pre is true after performing inverse
#push-options "--z3rlimit 100"
val merge_inv_prop (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2)
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==> 
                      (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                        suf2 = snd (pre_suf (ops_of s2) op2) /\
                        (let inv2 = inverse_st_op s2 op2 in
                        concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)))) /\
                        
                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==> 
                      (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                        suf1 = snd (pre_suf (ops_of s1) op1) /\
                        (let inv1 = inverse_st_op s1 op1 in
                        concrete_merge_pre (v_of lca) (v_of (inverse_st_op s1 op1)) (v_of s2)))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))))

// branch s1 does not see new operations
val linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

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

// branch s2 does not see new operations
val linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    ops_of s2 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

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

// taking inverse on any one branch and applying the operation again is equivalent to
// concrete merge
val linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                     (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                        suf2 = snd (pre_suf (ops_of s2) op2) /\
                        (let inv2 = inverse_st_op s2 op2 in
                        concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)))) /\

                      ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                        exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                        suf1 = snd (pre_suf (ops_of s1) op1) /\
                        (let inv1 = inverse_st_op s1 op1 in
                        concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2)))) /\

                     ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                     (last (resolve_conflict last1 last2) = last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                           concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                           
                     (last (resolve_conflict last1 last2) <> last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                           concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                       (let inv2 = inverse_st_op s2 op2 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2 /\
                       
                       eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)
                          (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (pre1, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                       (let inv1 = inverse_st_op s1 op1 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1 /\
                       eq (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
                          (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                    
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                      eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))) /\
                       
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                      eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))))))

let interleaving_helper_inv2_comm (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s1 > 0 /\ is_prefix lca s1 /\ is_prefix lca s2 /\
                Seq.length (diff s1 lca) > 0 /\ Seq.length (diff s2 lca) > 0 /\
                exists_triple (snd (un_snoc s1)) (diff s2 lca) /\
                (let (pre2, op2, suf2) = find_triple (snd (un_snoc s1)) (diff s2 lca) in
                is_interleaving l' (diff s1 lca) (pre2 ++ suf2)))
      (ensures (let (_, op2, _) = find_triple (snd (un_snoc s1)) (diff s2 lca) in
                is_interleaving (Seq.snoc l' op2) (diff s1 lca) (diff s2 lca)))
  = let (_, op2, _) = find_triple (snd (un_snoc (diff s1 lca))) (diff s2 lca) in
    let l = Seq.snoc l' op2 in
    ()

let interleaving_helper_inv1_comm (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s2 > 0 /\ is_prefix lca s1 /\ is_prefix lca s2 /\
                Seq.length (diff s1 lca) > 0 /\ Seq.length (diff s2 lca) > 0 /\
                not (exists_triple (snd (un_snoc s1)) (diff s2 lca)) /\
                exists_triple (snd (un_snoc s2)) (diff s1 lca) /\
                (let (pre1, op1, suf1) = find_triple (snd (un_snoc s2)) (diff s1 lca) in
                is_interleaving l' (pre1 ++ suf1) (diff s2 lca)))
      (ensures (let (_, op1, _) = find_triple (snd (un_snoc s2)) (diff s1 lca) in
                is_interleaving (Seq.snoc l' op1) (diff s1 lca) (diff s2 lca)))
  = let (_, op1, _) = find_triple (snd (un_snoc (diff s2 lca))) (diff s1 lca) in
    let l = Seq.snoc l' op1 in
    ()
  
let interleaving_helper_inv1 (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s1 > 0 /\ is_prefix lca s1 /\ is_prefix lca s2 /\
                Seq.length (diff s1 lca) > 0 /\ Seq.length (diff s2 lca) > 0 /\
                not (exists_triple (snd (un_snoc s1)) (diff s2 lca)) /\
                not (exists_triple (snd (un_snoc s2)) (diff s1 lca)) /\
                is_interleaving l' (diff (fst (Seq.un_snoc s1)) lca) (diff s2 lca))
      (ensures (let _, last1 = un_snoc s1 in
                is_interleaving (Seq.snoc l' last1) (diff s1 lca) (diff s2 lca)))
  = let prefix1, last1 = Seq.un_snoc (diff s1 lca) in
    let l = Seq.snoc l' last1 in
    introduce exists l'. is_interleaving l' prefix1 (diff s2 lca) /\
                    l = Seq.snoc l' last1
    with l'
    and ()
    
let interleaving_helper_inv2 (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s2 > 0 /\ is_prefix lca s1 /\ is_prefix lca s2 /\
                Seq.length (diff s1 lca) > 0 /\ Seq.length (diff s2 lca) > 0 /\
                not (exists_triple (snd (un_snoc s1)) (diff s2 lca)) /\
                not (exists_triple (snd (un_snoc s2)) (diff s1 lca)) /\
                is_interleaving l' (diff s1 lca) (diff (fst (Seq.un_snoc s2)) lca))
      (ensures (let _, last2 = un_snoc s2 in
                is_interleaving (Seq.snoc l' last2) (diff s1 lca) (diff s2 lca)))
  = let prefix2, last2 = Seq.un_snoc (diff s2 lca) in
    let l = Seq.snoc l' last2 in
    introduce exists l'. is_interleaving l' (diff s1 lca) prefix2 /\
                    l = Seq.snoc l' last2
    with l'
    and ()
  
#push-options "--z3rlimit 500"
let interleaving_s1_inv (lca s1 s2:st) (l':log)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    not (exists_triple (snd (un_snoc (ops_of s1))) (diff (ops_of s2) (ops_of lca))) /\
                    not (exists_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca))) /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                    interleaving_predicate l' lca (inverse_st s1) s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) = last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let l = Seq.snoc l' last1 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) =

  let _, last1 = un_snoc (ops_of s1) in
  let l = Seq.snoc l' last1 in
  interleaving_helper_inv1 (ops_of lca) (ops_of s1) (ops_of s2) l';
  linearizable_gt0 lca s1 s2; 
  lem_do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) (seq_foldl (v_of lca) l') last1;
  inverse_helper (v_of lca) l' last1;
  eq_is_equiv (seq_foldl (v_of lca) l) (do (seq_foldl (v_of lca) l') last1);
  transitive (seq_foldl (v_of lca) l) (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  assert (interleaving_predicate l lca s1 s2); ()

let interleaving_s2_inv (lca s1 s2:st) (l':log)
  : Lemma (requires common_pre lca s1 s2 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    not (exists_triple (snd (un_snoc (ops_of s1))) (diff (ops_of s2) (ops_of lca))) /\
                    not (exists_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    interleaving_predicate l' lca s1 (inverse_st s2) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let l = Seq.snoc l' last2 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) =
  let _, last2 = un_snoc (ops_of s2) in
  let l = Seq.snoc l' last2 in
  interleaving_helper_inv2 (ops_of lca) (ops_of s1) (ops_of s2) l'; 
  linearizable_gt0 lca s1 s2;
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) (seq_foldl (v_of lca) l') last2;
  inverse_helper (v_of lca) l' last2;
  eq_is_equiv (seq_foldl (v_of lca) l) (do (seq_foldl (v_of lca) l') last2);
  transitive (seq_foldl (v_of lca) l) (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  assert (interleaving_predicate l lca s1 s2); ()

let rec lem_app (l a b:log)
  : Lemma (requires l ++ a = l ++ b)
          (ensures a = b) (decreases length l) =
  match length l with
  |0 -> lemma_empty l; append_empty_l a; append_empty_l b
  |_ -> lemma_append_cons l a; 
       lemma_append_cons l b;
       lemma_cons_inj (head l) (head l) (tail l ++ a) (tail l ++ b);
       lem_app (tail l) a b
 
let interleaving_s2_inv_comm (lca s1 s2:st) (l':log)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\
                    (let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                     lem_suf_equal (ops_of lca) (ops_of s2) op2;
                  
                    (let inv2 = inverse_st_op s2 op2 in
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2) /\
                    interleaving_predicate l' lca s1 inv2))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let l = Seq.snoc l' op2 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in 
  lem_suf_equal (ops_of lca) (ops_of s2) op2;
  lem_inverse_op (ops_of lca) (ops_of s2) op2; 
  let inv2 = inverse_st_op s2 op2 in
  //assert (ops_of inv2 = ops_of lca ++ (pre2 ++ suf2)); 
  lem_diff (ops_of inv2) (ops_of lca);
  lem_app (ops_of lca) (pre2 ++ suf2) (diff (ops_of inv2) (ops_of lca));
  //assert (diff (ops_of inv2) (ops_of lca) = (pre2 ++ suf2)); 
  let l = Seq.snoc l' op2 in 
  assert (is_interleaving l' (diff (ops_of s1) (ops_of lca)) (pre2 ++ suf2)); 
  interleaving_helper_inv2_comm (ops_of lca) (ops_of s1) (ops_of s2) l';
  linearizable_gt0 lca s1 s2;
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) (seq_foldl (v_of lca) l') op2;
  inverse_helper (v_of lca) l' op2; 
  assert (foldl_prop (v_of lca) l); 
  eq_is_equiv (seq_foldl (v_of lca) l) (do (seq_foldl (v_of lca) l') op2);
  transitive (seq_foldl (v_of lca) l) (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  assert (interleaving_predicate l lca s1 s2); ()           

let interleaving_s1_inv_comm (lca s1 s2:st) (l':log)
  : Lemma (requires common_pre lca s1 s2 /\
                    not (exists_triple (snd (un_snoc (ops_of s1))) (diff (ops_of s2) (ops_of lca))) /\
                    exists_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca)) /\
                    (let (pre1, op1, suf1) = find_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca)) in
                    lem_suf_equal (ops_of lca) (ops_of s1) op1;
                    
                    (let inv1 = inverse_st_op s1 op1 in
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2) /\
                    interleaving_predicate l' lca inv1 s2)))
          (ensures (let (_, op1, _) = find_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca)) in
                    let l = Seq.snoc l' op1 in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) =
  let _, last2 = un_snoc (ops_of s2) in
  let (pre1, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  lem_suf_equal (ops_of lca) (ops_of s1) op1;
  lem_inverse_op (ops_of lca) (ops_of s1) op1; 
  let inv1 = inverse_st_op s1 op1 in
  //assert (ops_of inv1 = ops_of lca ++ (pre1 ++ suf1));
  lem_diff (ops_of inv1) (ops_of lca);
  lem_app (ops_of lca) (pre1 ++ suf1) (diff (ops_of inv1) (ops_of lca));
  //assert (diff (ops_of inv1) (ops_of lca) = (pre1 ++ suf1));
  let l = Seq.snoc l' op1 in 
  assert (is_interleaving l' (pre1 ++ suf1) (diff (ops_of s2) (ops_of lca)));
  interleaving_helper_inv1_comm (ops_of lca) (ops_of s1) (ops_of s2) l'; 
  linearizable_gt0 lca s1 s2;
  lem_do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) (seq_foldl (v_of lca) l') op1;
  inverse_helper (v_of lca) l' op1;
  eq_is_equiv (seq_foldl (v_of lca) l) (do (seq_foldl (v_of lca) l') op1);
  transitive (seq_foldl (v_of lca) l) (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2));
  assert (interleaving_predicate l lca s1 s2); ()
#pop-options

#push-options "--z3rlimit 500"
let linearizable_s1_gt0_pre (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last1))
          (ensures (let inv1 = inverse_st s1 in 
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))) =
  let inv1 = inverse_st s1 in 
  lem_inverse (ops_of lca) (ops_of s1);
  merge_inv_prop lca s1 s2; 
  lem_diff (ops_of inv1) (ops_of lca); 
  assert (is_prefix (ops_of lca) (ops_of inv1) /\
          concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2) /\
          (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
          (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))));
  ()

let linearizable_s2_gt0_pre (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple (snd (un_snoc (ops_of s1))) (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) <> last1))
          (ensures (let inv2 = inverse_st s2 in 
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca)))))) =
  let inv2 = inverse_st s2 in 
  lem_inverse (ops_of lca) (ops_of s2);
  merge_inv_prop lca s1 s2; 
  lem_diff (ops_of inv2) (ops_of lca); 
  assert (is_prefix (ops_of lca) (ops_of inv2) /\
          concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2) /\
          (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
          (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca)))));
  ()

let linearizable_s2_gt0_pre_comm (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    exists_triple last1 (diff (ops_of s2) (ops_of lca))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in 
                    suf2 = snd (pre_suf (ops_of s2) op2) /\
                    (let inv2 = inverse_st_op s2 op2 in 
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca))))))))
  = let _, last1 = un_snoc (ops_of s1) in
    let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in 
    lem_suf_equal (ops_of lca) (ops_of s2) op2;
    merge_inv_prop lca s1 s2;
    let inv2 = inverse_st_op s2 op2 in
    assert (concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)); 
    lem_inverse_op (ops_of lca) (ops_of s2) op2;
    assert (is_prefix (ops_of lca) (ops_of inv2));  
    lem_diff (ops_of inv2) (ops_of lca); 
    assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1);
    assert (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca))));
    ()

let linearizable_s1_gt0_pre_comm (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    not (exists_triple (snd (un_snoc (ops_of s1))) (diff (ops_of s2) (ops_of lca))) /\
                    exists_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca)))
          (ensures (let (_, op1, suf1) = find_triple (snd (un_snoc (ops_of s2))) (diff (ops_of s1) (ops_of lca)) in 
                    suf1 = snd (pre_suf (ops_of s1) op1) /\
                    (let inv1 = inverse_st_op s1 op1 in 
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))))) 
  = let _, last2 = un_snoc (ops_of s2) in
    let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in 
    lem_suf_equal (ops_of lca) (ops_of s1) op1;
    merge_inv_prop lca s1 s2;
    let inv1 = inverse_st_op s1 op1 in
    assert (concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2));
    lem_inverse_op (ops_of lca) (ops_of s1) op1;
    assert (is_prefix (ops_of lca) (ops_of inv1));
    lem_diff (ops_of inv1) (ops_of lca); 
    assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1);
    assert (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))));
    ()
#pop-options

// convergence theorem
val convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ eq s1' (do s1 o) /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures eq (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1'))
