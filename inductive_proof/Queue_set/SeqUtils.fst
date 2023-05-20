module SeqUtils

open FStar.Seq

type seq_assoc (a:eqtype) (b:Type) = seq (a & b)

let rec count_assoc_fst (#a:eqtype) (#b:Type) (id:a) (l:seq_assoc a b)
  : Tot nat (decreases Seq.length l) =

  if Seq.length l = 0 then 0
  else let tl_count = count_assoc_fst id (tail l) in
       if fst (head l) = id then 1 + tl_count 
       else tl_count

let mem_assoc_fst (#a:eqtype) (#b:Type) (id:a) (l:seq (a & b)) : bool =
  count_assoc_fst id l > 0

let distinct_assoc_fst (#a:eqtype) (#b:Type) (s:seq_assoc a b) =
  forall (id:a).{:pattern count_assoc_fst id s} count_assoc_fst id s <= 1

unfold
let ( ++ ) (#a:Type) (s1 s2:seq a) = Seq.append s1 s2

#push-options "--z3rlimit 50"
let rec lemma_append_count_assoc_fst (#a:eqtype) (#b:Type) (lo hi:seq_assoc a b)
  : Lemma
      (ensures (forall x. count_assoc_fst x (lo ++ hi) = (count_assoc_fst x lo + count_assoc_fst x hi)) /\
               (forall id. mem_assoc_fst id (lo ++ hi) <==> (mem_assoc_fst id lo \/ mem_assoc_fst id hi)))
      (decreases (length lo))
  = if length lo = 0
       then (assert (equal (lo ++ hi) hi); ())
       else (assert (equal (cons (head lo) ((tail lo) ++ hi)) (lo ++ hi));
           lemma_append_count_assoc_fst (tail lo) hi;
           let tl_l_h = (tail lo) ++ hi in
           let lh = cons (head lo) tl_l_h in
           (assert (equal (tail lh) tl_l_h); ()))
#pop-options

let distinct_invert_append (#t1:eqtype) (#t2:Type) (a b:seq_assoc t1 t2)
  : Lemma
      (requires distinct_assoc_fst (a ++ b))
      (ensures distinct_assoc_fst a /\ distinct_assoc_fst b /\ 
               (forall id. (*{:pattern (mem_assoc_fst id a ==> not (mem_assoc_fst id b))}*) mem_assoc_fst id a ==> not (mem_assoc_fst id b)))
      //[SMTPat (distinct_assoc_fst (a ++ b))]
  = lemma_append_count_assoc_fst a b

let distinct_append (#t1:eqtype) (#t2:Type) (a b:seq_assoc t1 t2)
  : Lemma (requires distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    (forall id. mem_assoc_fst id a ==> not (mem_assoc_fst id b)))
          (ensures (distinct_assoc_fst (a ++ b)) /\
                   (forall id. mem_assoc_fst id (a ++ b) <==> mem_assoc_fst id a \/ mem_assoc_fst id b)) =
  lemma_append_count_assoc_fst a b
  
// p is a prefix of l
let is_prefix (#a:Type) (p l:Seq.seq a) =
  Seq.length l >= Seq.length p /\ Seq.equal p (Seq.slice l 0 (Seq.length p))

// s is a suffix of l
let is_suffix (#a:Type) (s l:Seq.seq a) =
  Seq.length l >= Seq.length s /\ Seq.equal s (Seq.slice l (Seq.length l - Seq.length s) (Seq.length l))

let rec forallb (#a:eqtype) (f:a -> bool) (l:seq a)
  : Tot (b:bool{(forall e. mem e l ==> f e) <==> b = true}) (decreases length l) =
  match length l with
  |0 -> true
  |_ -> if f (head l) then forallb f (tail l) else false

let rec existsb (#a:eqtype) (f:a -> bool) (l:seq a)
  : Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true}) (decreases length l) =
  match length l with
  |0 -> false
  |_ -> if f (head l) then true else existsb f (tail l)

// returns position of op in a log of operations
let rec idx (#a:eqtype) (x:a) (l:seq a{mem x l}) : Tot (n:nat{n >= 0 /\ n < length l})
    (decreases length l) =
  match length l with
  |1 -> 0
  |_ -> if head l = x then 0 else 1 + idx x (tail l)
  
let diff (#a:eqtype) (s1:Seq.seq a) (lca:Seq.seq a{is_prefix lca s1}) 
  : Tot (l:seq a{(length s1 == length lca + length l) /\ (s1 == lca ++ l) /\
                 (forall e. mem e s1 <==> (mem e lca \/ mem e l)) /\
                 (forall op. mem op l ==> length s1 > length lca) /\
                 is_suffix l s1}) =
  let s = snd (split s1 (length lca)) in
  lemma_split s1 (length lca);
  lemma_mem_append lca s;
  s

let diff_suf (#t1 #t2:eqtype) (s1:seq_assoc t1 t2) (lca:seq_assoc t1 t2{is_suffix lca s1})
  : Tot (d:seq_assoc t1 t2{(s1 == d ++ lca) /\ is_prefix d s1 /\
                           (length s1 == length lca + length d) /\
                           (forall id. mem_assoc_fst id s1 <==> mem_assoc_fst id d \/ mem_assoc_fst id lca)}) =
  let s = fst (split s1 (length s1 - length lca)) in
  lemma_split s1 (length s1 - length lca);
  lemma_mem_append s lca;
  lemma_append_count_assoc_fst s lca;
  s
  
let lem_inverse (#a:eqtype) (lca s1:Seq.seq a)
  : Lemma (requires is_prefix lca s1 /\
                    Seq.length s1 > Seq.length lca)
          (ensures (is_prefix lca (fst (un_snoc s1)))) 
  = lemma_split (fst (un_snoc s1)) (length lca)

let rec mem_ele_id (#t1 #t2:eqtype) (op:(t1 & t2)) (l:seq_assoc t1 t2)
  : Lemma (requires mem op l)
          (ensures mem_assoc_fst (fst op) l) (decreases length l) =
  if head l = op then ()
    else mem_ele_id op (tail l)
    
let rec lem_un_snoc_id (#t1 #t2:eqtype) (a b:seq_assoc t1 t2)
  : Lemma (requires length b > 0 /\ a == fst (un_snoc b))
          (ensures (forall id. mem_assoc_fst id a ==> mem_assoc_fst id b)) (decreases length a) =
  match length a with
  |0 -> ()
  |_ -> lem_un_snoc_id (tail a) (tail b)

let one_is_unique (#t1 #t2:eqtype) (s:(t1 & t2))
  : Lemma (ensures distinct_assoc_fst (create 1 s)) = ()

let lem_diff (#t1 #t2:eqtype) (s1 l:seq_assoc t1 t2)
  : Lemma (requires distinct_assoc_fst s1 /\ is_prefix l s1)
          (ensures distinct_assoc_fst (diff s1 l) /\ 
                   (forall id. mem_assoc_fst id (diff s1 l) <==> mem_assoc_fst id s1 /\ not (mem_assoc_fst id l)) /\
                   (forall id. mem_assoc_fst id s1 <==> mem_assoc_fst id l \/ mem_assoc_fst id (diff s1 l)) /\
                   (Seq.length s1 > Seq.length l ==> (last s1 == last (diff s1 l) /\ Seq.length (diff s1 l) > 0) /\
                    mem_assoc_fst (fst (last s1)) (diff s1 l) /\
                     (let _, l1 = un_snoc s1 in
                      let _, ld = un_snoc (diff s1 l) in
                      l1 = ld) /\
                     (let s1',lastop = un_snoc s1 in 
                       diff s1' l == fst (un_snoc (diff s1 l)))))
  = lemma_append_count_assoc_fst l (diff s1 l);
    if (length s1 > length l) then
      (let pre1, last1 = un_snoc (diff s1 l) in
      lemma_append_count_assoc_fst pre1 (create 1 last1))

let lem_diff_suf (#t1 #t2:eqtype) (s1 l:seq_assoc t1 t2)
  : Lemma (requires is_suffix l s1)
          (ensures (forall id. mem_assoc_fst id s1 <==> mem_assoc_fst id l \/ mem_assoc_fst id (diff_suf s1 l)) /\
                   (Seq.length s1 > Seq.length l ==> (head s1 == head (diff_suf s1 l) /\ Seq.length (diff_suf s1 l) > 0) /\
                     (let h1 = head s1 in
                      let hd = head (diff_suf s1 l) in
                      h1 = hd) /\
                     (let s1' = tail s1 in 
                       is_suffix l s1' /\
                       diff_suf s1' l == tail (diff_suf s1 l))))
  = lemma_append_count_assoc_fst (diff_suf s1 l) l

let lem_diff_suf_uni (#t1 #t2:eqtype) (s1 l:seq_assoc t1 t2)
  : Lemma (requires (distinct_assoc_fst s1 /\ is_suffix l s1))
          (ensures distinct_assoc_fst (diff_suf s1 l) /\ 
                   (forall id. mem_assoc_fst id (diff_suf s1 l) <==> mem_assoc_fst id s1 /\ not (mem_assoc_fst id l))) 
  = lemma_append_count_assoc_fst (diff_suf s1 l) l

let lem_diff_lastop (#t1 #t2:eqtype) (s1 l:seq_assoc t1 t2)
  : Lemma (requires distinct_assoc_fst s1 /\ is_prefix l s1 /\ length s1 > length l)
          (ensures (let s1',lastop = un_snoc s1 in 
                    mem_assoc_fst (fst lastop) (diff s1 l))) =
  lem_diff s1 l;
  let ds1',lastop = un_snoc (diff s1 l) in 
  lemma_mem_append ds1' (create 1 lastop);
  mem_ele_id lastop (diff s1 l)

let un_snoc_prop (#t1 #t2:eqtype) (a:seq_assoc t1 t2)
  : Lemma (requires distinct_assoc_fst a /\ length a > 0)
          (ensures (forall id. mem_assoc_fst id a <==> mem_assoc_fst id (fst (un_snoc a)) \/ id == fst (last a)) /\
                   (forall id. mem_assoc_fst id a /\ id <> fst (last a) <==> mem_assoc_fst id (fst (un_snoc a))) /\
                   (let _, l = un_snoc a in 
                    mem_assoc_fst (fst l) a) /\ distinct_assoc_fst (fst (un_snoc a))) =
  let p, l = un_snoc a in
  lemma_split a (length a - 1);
  lemma_append_count_assoc_fst p (snd (split a (length a - 1)));
  distinct_invert_append p (snd (split a (length a - 1)))
  
let lem_lt_lastop_id_lca (#t:eqtype) (lca s1:seq_assoc pos t)
  : Lemma (requires is_prefix lca s1 /\ length (diff s1 lca) > 0 /\ distinct_assoc_fst s1 /\
                    (forall id id1. mem_assoc_fst id lca /\ mem_assoc_fst id1 (diff s1 lca) ==> id < id1))
          (ensures (let _, lastop = un_snoc s1 in
                    (forall id. mem_assoc_fst id lca ==> id < (fst lastop)))) =
    distinct_invert_append lca (diff s1 lca); 
    let pre, lst = un_snoc s1 in
    lem_diff s1 lca;
    mem_ele_id lst (diff s1 lca)

let lastop_diff (#t:eqtype) (l a:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ is_prefix l a /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> id < id1) /\
                    length a > length l)
          (ensures (length (diff a l) > 0) /\
                   (let p, last = un_snoc a in
                   mem_assoc_fst (fst last) a /\ mem_assoc_fst (fst last) (diff a l) /\
                   (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff p l) ==> id < id1)))
  = un_snoc_prop a;
    lem_diff a l;
    un_snoc_prop (diff a l);
    lem_inverse l a

let inverse_diff_id_s1' (#t:eqtype) (l a b:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ 
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> id < id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> id < id1) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (forall id. mem_assoc_fst id (diff (fst (un_snoc a)) l) ==> not (mem_assoc_fst id (diff b l))))
  = un_snoc_prop a;
    lem_diff a l; 
    lem_inverse l a;
    lem_diff (fst (un_snoc a)) l

let inverse_diff_id_s2' (#t:eqtype) (l a b:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    is_prefix l a /\ is_prefix l b /\
                    length b > length l /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> id < id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> id < id1) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff (fst (un_snoc b)) l))))
  = un_snoc_prop b;
    lem_diff b l; 
    lem_inverse l b;
    lem_diff (fst (un_snoc b)) l

let inverse_diff_id_s1'_s2' (#t:eqtype) (l a b:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> id < id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> id < id1) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (forall id. mem_assoc_fst id (diff (fst (un_snoc a)) l) ==> not (mem_assoc_fst id (diff (fst (un_snoc b)) l))))
  = un_snoc_prop a;
    lem_diff a l; 
    lem_inverse l a;
    lem_diff (fst (un_snoc a)) l;
    un_snoc_prop b;
    lem_diff b l; 
    lem_inverse l b;
    lem_diff (fst (un_snoc b)) l
    
let lastop_neq (#t:eqtype) (l a b:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> id < id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> id < id1) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (let p, la = un_snoc a in
                    let _, lb = un_snoc b in
                    fst la <> fst lb)) =
  lastop_diff l a;
  lastop_diff l b

// l = (snoc (fst ps) op) ++ snd ps
let pre_suf1 (#a:eqtype) (l:seq a) (x:a{mem x l})
  : Tot (ps:(seq a & seq a){is_prefix (fst ps) l /\ is_suffix (snd ps) l /\ 
                    length l = length (fst ps) + 1 + length (snd ps)}) = 
    assert (length l >= 1);
    assert (idx x l + 1 <= length l);
    let r = (fst (split l (idx x l)), snd (split l (idx x l + 1))) in
    lemma_split l (length (fst r));
    lemma_count_slice l (idx x l);
    assert (is_prefix (fst r) l /\ is_suffix (snd r) l /\ length l = length (fst r) + 1 + length (snd r)); 
    assert (is_prefix (fst r) (Seq.snoc (fst r) x));
    lemma_split (Seq.snoc (fst r) x) (length (fst r)); 
    lemma_count_slice l (idx x l + 1);
    lemma_split l (length (fst r) + 1);
    r

#push-options "--z3rlimit 50"
let rec pre_suf_prop1 (#a:eqtype) (l:seq a) (x:a)      ////!!!CHECK
  : Lemma (requires mem x l)
          (ensures (let ps = pre_suf1 l x in
                    Seq.equal l (Seq.snoc (fst ps) x ++ (snd ps)))) (decreases length l) =
  match length l with
  |1 -> ()
  |_ -> if head l = x then () 
          else pre_suf_prop1 (tail l) x
#pop-options

let pre_suf_prop2 (#a:eqtype) (l:seq a) (x:a)
  : Lemma (requires mem x l)
          (ensures (let ps = pre_suf1 l x in
                    (forall e. mem e l <==> mem e (fst ps) \/ e = x \/ mem e (snd ps)))) =
  let ps = pre_suf1 l x in
  pre_suf_prop1 l x;
  lemma_mem_snoc (fst ps) x;
  lemma_mem_append (snoc (fst ps) x) (snd ps)

let rec not_id_not_ele (#t1 #t2:eqtype) (x:(t1 & t2)) (l:seq_assoc t1 t2)
  : Lemma (requires not (mem_assoc_fst (fst x) l))
          (ensures not (mem x l)) (decreases length l) =
  if length l = 0 then ()
    else if head l = x then ()
      else not_id_not_ele x (tail l)

let lemma_mem_snoc_id (#t1 #t2:eqtype) (l:seq_assoc t1 t2) (x:(t1 & t2))
  : Lemma (requires distinct_assoc_fst l /\ not (mem_assoc_fst (fst x) l))
          (ensures (forall id. mem_assoc_fst id (snoc l x) <==> mem_assoc_fst id l \/ id = fst x) /\
                   (forall id. mem_assoc_fst id l <==> mem_assoc_fst id (snoc l x) /\ id <> fst x)) =
  lemma_append_count_assoc_fst l (Seq.create 1 x)

// l = Seq.snoc (fst ps) op ++ (snd ps)
let pre_suf (#a:eqtype) (l:seq a) (x:a{mem x l})
  : Tot (ps:(seq a & seq a){ps = pre_suf1 l x /\
                    is_prefix (fst ps) l /\ is_suffix (snd ps) l /\ 
                    length l = length (fst ps) + 1 + length (snd ps) /\
                    Seq.equal l (Seq.snoc (fst ps) x ++ (snd ps)) /\
                    l = (Seq.snoc (fst ps) x ++ (snd ps)) /\
                    (forall e. mem e l <==> mem e (fst ps) \/ e = x \/ mem e (snd ps))}) =
    let r =  pre_suf1 l x in
    pre_suf_prop1 l x;
    pre_suf_prop2 l x;
    r

let lem_id (#t1 #t2:eqtype) (l p s:seq_assoc t1 t2) (o_id:t1)
  : Lemma (requires distinct_assoc_fst p /\ distinct_assoc_fst s /\ distinct_assoc_fst (p ++ s) /\ distinct_assoc_fst l /\
                    (forall id. mem_assoc_fst id l <==> mem_assoc_fst id p \/ id = o_id \/ mem_assoc_fst id s) /\
                    (forall id. mem_assoc_fst id (p ++ s) <==> mem_assoc_fst id p \/ mem_assoc_fst id s) /\
                    not (mem_assoc_fst o_id (p ++ s)))
          (ensures (forall id. mem_assoc_fst id (p ++ s) <==> mem_assoc_fst id l /\ id <> o_id))
   = ()

let pre_suf_prop (#t1 #t2:eqtype) (l:seq_assoc t1 t2) (x:(t1 & t2))
  : Lemma (requires distinct_assoc_fst l /\ mem x l)
          (ensures (let ps = pre_suf l x in
                    distinct_assoc_fst (fst ps) /\ distinct_assoc_fst (snd ps) /\ 
                    (forall id. mem_assoc_fst id (fst ps) ==> not (mem_assoc_fst id (snd ps))) /\
                    distinct_assoc_fst (fst ps ++ snd ps) /\
                    (forall id. mem_assoc_fst id l <==> mem_assoc_fst id (fst ps) \/ id = fst x \/ mem_assoc_fst id (snd ps)) /\
                    (forall id. mem_assoc_fst id (fst ps ++ snd ps) <==> mem_assoc_fst id l /\ id <> fst x))) =
  let ps = pre_suf l x in
  distinct_invert_append (snoc (fst ps) x) (snd ps); 
  distinct_invert_append (fst ps) (create 1 x);
  lemma_mem_snoc_id (fst ps) x;
  distinct_append (fst ps) (snd ps);
  lemma_append_count_assoc_fst (fst ps) (create 1 x); 
  lemma_append_count_assoc_fst (snoc (fst ps) x) (snd ps);
  lem_id l (fst ps) (snd ps) (fst x)

let lt_is_neq (#t:eqtype) (lca s1:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst s1 /\ is_prefix lca s1 /\ 
                    (forall id id1. mem_assoc_fst id lca /\ mem_assoc_fst id1 (diff s1 lca) ==> id < id1))
          (ensures (forall id. mem_assoc_fst id lca ==> not (mem_assoc_fst id (diff s1 lca)))) (decreases length lca) =
  let s = snd (split s1 (length lca)) in
  lemma_split s1 (length lca);
  lemma_append_count_assoc_fst lca s

let lem_is_diff  (#t:eqtype) (s1 lca d:seq_assoc pos t)
  : Lemma (requires s1 == lca ++ d)
          (ensures is_prefix lca s1 /\ d == diff s1 lca) =
  lemma_split s1 (length lca);
  lemma_mem_append lca d;
  lemma_append_count lca d;
  assert (is_suffix d s1);
  ()

let lem_last (#a:eqtype) (x:seq a)
  : Lemma (ensures (length x > 0 ==> 
                      (let _, lst = un_snoc x in 
                       last x == lst))) = ()

let lem_inverse_op (#a:eqtype) (lca s1:seq a) (op:a)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\
                    (let _, suf = pre_suf s1 op in
                     let _, sufd = pre_suf (diff s1 lca) op in
                     suf == sufd))
          (ensures (let pre, suf = pre_suf s1 op in
                   (is_prefix lca (pre ++ suf)) /\
                   (let pred, sufd = pre_suf (diff s1 lca) op in
                     (pre ++ suf = lca ++ (pred ++ sufd)))))
  = let pre, suf = pre_suf s1 op in 
    let pred, sufd = pre_suf (diff s1 lca) op in
    assert ((snoc pre op) ++ suf == lca ++ ((snoc pred op) ++ sufd));  
    append_assoc lca pred sufd;
    append_assoc lca (snoc pred op) sufd;
    assert ((snoc pre op) ++ suf == (lca ++ snoc pred op) ++ sufd);  
    append_assoc lca pred (create 1 op);
    assert (snoc pre op ++ suf == snoc (lca ++ pred) op ++ sufd);    
    lemma_snoc_inj pre (lca ++ pred) op op;
    assert (pre == lca ++ pred);
    ()

let lem_equal_distinct (#t1 #t2:eqtype) (a b:seq_assoc t1 t2)
  : Lemma (requires distinct_assoc_fst a /\ a == b)
          (ensures distinct_assoc_fst b) = ()

let rec lem_count_1 (#t1 #t2:eqtype) (a a1 b b1:seq_assoc t1 t2) (op:(t1 & t2))
  : Lemma (requires (snoc a op ++ a1 == snoc b op ++ b1) /\ 
                     not (mem_assoc_fst (fst op) a) /\ not (mem_assoc_fst (fst op) a1) /\
                     not (mem_assoc_fst (fst op) b) /\ not (mem_assoc_fst (fst op) b1) /\
                     count_assoc_fst (fst op) (snoc a op ++ a1) = 1)
          (ensures length a1 = length b1) (decreases length a) =
  match length a with
  |0 -> lemma_empty a;
       append_assoc a (create 1 op) a1;
       append_empty_l (cons op a1);
       lemma_append_inj (snoc a op) a1 (snoc b op) b1
  |_ -> lemma_eq_intro (tail (snoc a op ++ a1)) (snoc (tail a) op ++ a1); 
       lemma_eq_intro (tail (snoc b op ++ b1)) (snoc (tail b) op ++ b1); 
       lem_count_1 (tail a) a1 (tail b) b1 op

let append_cons_snoc1 (#a:eqtype) (u:seq a) (x:a) (v:seq a)
    : Lemma (equal (u ++ (snoc v x)) (snoc (u ++ v) x)) = ()

let rec count_1 (#t1 #t2:eqtype) (l:seq_assoc t1 t2)
  : Lemma (requires distinct_assoc_fst l)
          (ensures (forall id. mem_assoc_fst id l ==> count_assoc_fst id l = 1)) (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> let hd = head l in
       let tl = tail l in
       assert (l == cons hd tl);
       distinct_invert_append (create 1 hd) tl; count_1 tl

let not_mem_id (#t1 #t2:eqtype) (a:seq_assoc t1 t2) (op:t1 & t2)
  : Lemma (requires (forall id. mem_assoc_fst id a ==> not (mem_assoc_fst id (create 1 op))))
          (ensures not (mem_assoc_fst (fst op) a)) = ()

let lemma_mem_snoc1 (#t1 #t2:eqtype) (l:seq_assoc t1 t2) (op:t1 & t2)
  : Lemma (ensures (forall id. mem_assoc_fst id (snoc l op) <==> mem_assoc_fst id l \/ id = fst op)) = 
  lemma_append_count_assoc_fst l (Seq.create 1 op)

let not_mem_id1 (#t1 #t2:eqtype) (a:seq_assoc t1 t2) (op:t1 & t2) (b:seq_assoc t1 t2)
  : Lemma (requires (forall id. mem_assoc_fst id (snoc a op) ==> not (mem_assoc_fst id b)))
          (ensures  not (mem_assoc_fst (fst op) b)) =
  lemma_append_count_assoc_fst a (Seq.create 1 op)

let lem_not_append (#t:eqtype) (a b:seq_assoc pos t) (id:pos)
  : Lemma (requires not (mem_assoc_fst id a) /\ not (mem_assoc_fst id b) /\ 
                    distinct_assoc_fst a /\ distinct_assoc_fst b)
          (ensures not (mem_assoc_fst id (a ++ b))) =
 lemma_append_count_assoc_fst a b      

let lem_suf_equal1 (#t1 #t2:eqtype) (lca s1:seq_assoc t1 t2) (op:t1 & t2)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\ distinct_assoc_fst s1)
          (ensures (let pre, suf = pre_suf s1 op in
                    not (mem_assoc_fst (fst op) pre) /\
                    not (mem_assoc_fst (fst op) suf))) =
  let pre, suf = pre_suf s1 op in
  pre_suf_prop s1 op;
  distinct_invert_append (snoc pre op) suf;
  distinct_invert_append pre (create 1 op);
  not_mem_id pre op;
  lemma_mem_snoc1 pre op

let lem_suf_equal2 (#t:eqtype) (lca s1:seq_assoc pos t) (op:pos & t)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\ distinct_assoc_fst s1)
          (ensures (let pred, sufd = pre_suf (diff s1 lca) op in
                    not (mem_assoc_fst (fst op) pred) /\
                    not (mem_assoc_fst (fst op) sufd) /\
                    not (mem_assoc_fst (fst op) lca) /\
                    not (mem_assoc_fst (fst op) (lca ++ pred)))) =
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

let lem_suf_equal2_last (#t1 #t2:eqtype) (lca s1:seq_assoc t1 t2)
  : Lemma (requires is_prefix lca s1 /\ length (diff s1 lca) > 0 /\ distinct_assoc_fst s1)
          (ensures (let _, lastop = un_snoc s1 in
                    not (mem_assoc_fst (fst lastop) lca))) =
    distinct_invert_append lca (diff s1 lca); 
    let pre, lst = un_snoc s1 in
    lem_diff s1 lca;
    mem_ele_id lst (diff s1 lca)

let lem_suf_equal3 (#t1 #t2:eqtype) (lca s1:seq_assoc t1 t2) (op:t1 & t2)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\ distinct_assoc_fst s1)
          (ensures (let pre, suf = pre_suf s1 op in 
                    let pred, sufd = pre_suf (diff s1 lca) op in
                    count_assoc_fst (fst op) (snoc pre op ++ suf) = 1 /\
                    snoc pre op ++ suf == snoc (lca ++ pred) op ++ sufd)) =
  count_1 s1; 
  let pre, suf = pre_suf s1 op in
  let pred, sufd = pre_suf (diff s1 lca) op in
  pre_suf_prop s1 op; 
  lem_diff s1 lca;
  pre_suf_prop (diff s1 lca) op;
  assert (snoc pre op ++ suf == lca ++ ((snoc pred op) ++ sufd)); 
  append_assoc lca (snoc pred op) sufd;
  assert (lca ++ ((snoc pred op) ++ sufd) == (lca ++ snoc pred op) ++ sufd);  
  append_cons_snoc1 lca op pred; 
  lemma_eq_elim (lca ++ (snoc pred op)) (snoc (lca ++ pred) op);
  assert ((lca ++ (snoc pred op)) == (snoc (lca ++ pred) op));
  assert (lca ++ ((snoc pred op) ++ sufd) == snoc (lca ++ pred) op ++ sufd); 
  assert (snoc pre op ++ suf == snoc (lca ++ pred) op ++ sufd);  
  ()

let lem_suf_equal (#t:eqtype) (lca s1:seq_assoc pos t) (op:pos & t)
  : Lemma (requires is_prefix lca s1 /\ mem op (diff s1 lca) /\ distinct_assoc_fst s1)
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

let lem_suf_equal4 (#t1 #t2:eqtype) (s1:seq_assoc t1 t2) (op:t1 & t2)
  : Lemma (requires mem op s1 /\ distinct_assoc_fst s1)
          (ensures (let pre, suf = pre_suf s1 op in
                    not (mem_assoc_fst (fst op) pre) /\
                    not (mem_assoc_fst (fst op) suf))) =
  let pre, suf = pre_suf s1 op in
  pre_suf_prop s1 op;
  distinct_invert_append (snoc pre op) suf;
  distinct_invert_append pre (create 1 op);
  not_mem_id pre op;
  lemma_mem_snoc1 pre op

let lem_id_not_snoc (#t1 #t2:eqtype) (l l1:seq_assoc t1 t2) (op op1:t1 & t2)
  : Lemma (requires not (mem_assoc_fst (fst op) l) /\ mem_assoc_fst (fst op1) l /\
                    not (mem_assoc_fst (fst op1) l1))
          (ensures fst op1 <> fst op /\
                   not (mem_assoc_fst (fst op1) (snoc l1 op))) = 
  assert (fst op1 <> fst op); 
  assert (not (mem_assoc_fst (fst op1) (create 1 op))); 
  lemma_mem_snoc1 l1 op

let lem_id_s2' (#t:eqtype) (l a b:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    is_prefix l a /\ is_prefix l b /\
                    length b > length l /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> id < id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> id < id1) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (let b',lastop = un_snoc b in
                    not (mem_assoc_fst (fst lastop) l) /\
                    not (mem_assoc_fst (fst lastop) a) /\
                    not (mem_assoc_fst (fst lastop) b'))) = 
  let b', lastop = un_snoc b in
  lemma_append_count_assoc_fst b' (create 1 lastop);
  distinct_invert_append b' (create 1 lastop);
  assert (not (mem_assoc_fst (fst lastop) b'));
  lem_suf_equal2_last l b;
  assert (not (mem_assoc_fst (fst lastop) l) );
  lem_diff a l;
  lastop_diff l b;
  assert (not (mem_assoc_fst (fst lastop) a));
  ()

let lem_id_s1' (#t:eqtype) (l a b:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> id < id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> id < id1) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (let a',lastop = un_snoc a in
                    not (mem_assoc_fst (fst lastop) l) /\
                    not (mem_assoc_fst (fst lastop) a') /\
                    not (mem_assoc_fst (fst lastop) b))) = 
  let a', lastop = un_snoc a in
  lemma_append_count_assoc_fst a' (create 1 lastop);
  distinct_invert_append a' (create 1 lastop);
  assert (not (mem_assoc_fst (fst lastop) a')); 
  lem_suf_equal2_last l a;
  assert (not (mem_assoc_fst (fst lastop) l) );
  lem_diff b l;
  lastop_diff l a;
  assert (not (mem_assoc_fst (fst lastop) b));
  () 

let inverse_diff_id_last2 (#t:eqtype) (l a b:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> id < id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> id < id1) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (let pre2, last2 = un_snoc b in
                    let pre1, last1 = un_snoc a in
                    not (mem_assoc_fst (fst last2) l) /\
                    not (mem_assoc_fst (fst last2) pre1) /\
                    not (mem_assoc_fst (fst last2) a) /\
                    not (mem_assoc_fst (fst last2) pre2))) =
  let pre2, last2 = un_snoc b in
  let pre1, last1 = un_snoc a in
  lt_is_neq l b; 
  assert (forall id. mem_assoc_fst id l ==> not (mem_assoc_fst id (diff b l))); 
  lastop_diff l b;
  assert (not (mem_assoc_fst (fst last2) l)); 
  lem_diff a l;
  assert (not (mem_assoc_fst (fst last2) (diff a l)));
  assert (not (mem_assoc_fst (fst last2) a)); 
  lemma_split a (length a - 1); 
  lemma_mem_snoc1 pre1 last1;
  assert (not (mem_assoc_fst (fst last2) pre1));
  lemma_split b (length b - 1); 
  lemma_append_count_assoc_fst pre2 (create 1 last2);
  distinct_invert_append pre2 (create 1 last2);
  not_mem_id pre2 last2;
  assert (not (mem_assoc_fst (fst last2) pre2)); ()

let inverse_diff_id_last1 (#t:eqtype) (l a b:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> id < id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> id < id1) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (let pre2, last2 = un_snoc b in
                    let pre1, last1 = un_snoc a in
                    not (mem_assoc_fst (fst last1) l) /\
                    not (mem_assoc_fst (fst last1) pre2) /\
                    not (mem_assoc_fst (fst last1) b) /\
                    not (mem_assoc_fst (fst last1) pre1))) =
  let pre2, last2 = un_snoc b in
  let pre1, last1 = un_snoc a in
  lt_is_neq l a; 
  assert (forall id. mem_assoc_fst id l ==> not (mem_assoc_fst id (diff a l))); 
  lastop_diff l a;
  assert (not (mem_assoc_fst (fst last1) l)); 
  lem_diff b l;
  assert (not (mem_assoc_fst (fst last1) (diff b l)));
  assert (not (mem_assoc_fst (fst last1) b)); 
  lemma_split b (length b - 1); 
  lemma_mem_snoc1 pre2 last2;
  assert (not (mem_assoc_fst (fst last1) pre2));
  lemma_split a (length a - 1); 
  lemma_append_count_assoc_fst pre1 (create 1 last1);
  distinct_invert_append pre1 (create 1 last1);
  not_mem_id pre1 last1;
  assert (not (mem_assoc_fst (fst last1) pre1)); ()

let id_not_eq (#t:eqtype) (l l1:seq_assoc pos t) (id id1:pos)
  : Lemma (requires (forall id. mem_assoc_fst id l ==> not (mem_assoc_fst id l1)) /\
                    mem_assoc_fst id l /\ mem_assoc_fst id1 l1)
          (ensures id <> id1) = ()

let rec lem_not_id (#t1 #t2:eqtype) (l:seq_assoc t1 t2) (op:t1 & t2)
  : Lemma (requires distinct_assoc_fst l /\ 
                    not (mem_assoc_fst (fst op) l))
          (ensures not (mem op l)) (decreases length l) = 
  match length l with
  |0 -> ()
  |_ -> let hd = head l in
       let tl = tail l in
       assert (l = cons hd tl);
       distinct_invert_append (create 1 hd) tl; 
       lem_not_id (tail l) op

let rec lem_count_id_ele (#t1 #t2:eqtype) (l:seq_assoc t1 t2) (op:t1 & t2)
  : Lemma (requires count_assoc_fst (fst op) l = 1 /\ mem op l /\ distinct_assoc_fst l)
          (ensures count op l = 1) (decreases length l) =
  match length l with
  |1 -> ()
  |_ -> if (fst (head l) = fst op) 
         then (assert (not (mem_assoc_fst (fst op) (tail l))); 
               assert (l = cons (head l) (tail l));
               distinct_invert_append (create 1 (head l)) (tail l); 
               lem_not_id (tail l) op)
          else (lemma_tl (head l) (tail l);
                lemma_append_count_assoc_fst (create 1 (head l)) (tail l);
                distinct_invert_append (create 1 (head l)) (tail l);
                lem_count_id_ele (tail l) op)

let lem_lastop_suf_0_help (#t1 #t2:eqtype) (l:seq_assoc t1 t2) (op:t1 & t2)
  : Lemma (requires last (cons op l) = op /\
                    count op (cons op l) = 1)
          (ensures not (mem op l) /\ length l = 0) =
  lemma_mem_append (create 1 op) l;
  lemma_append_count (create 1 op) l

let lem_lastop_suf_0 (#t1 #t2:eqtype) (l l1 l2:seq_assoc t1 t2) (op:t1 & t2)
  : Lemma (requires distinct_assoc_fst l /\ mem op l /\
                    l = snoc l1 op ++ l2 /\
                    (lemma_mem_append (snoc l1 op) l2;
                    last l = op))
          (ensures length l2 = 0) =
  lemma_mem_append (snoc l1 op) l2;
  lemma_append_count (snoc l1 op) l2;
  mem_ele_id op l;
  count_1 l;
  lem_count_id_ele l op;
  assert (count op l = 1); 
  append_assoc l1 (create 1 op) l2;
  assert (l = l1 ++ cons op l2);

  lemma_mem_append l1 (cons op l2);
  lemma_append_count l1 (cons op l2);
  lemma_mem_append (create 1 op) l2;
  lemma_append_count (create 1 op) l2;
  assert (mem op (cons op l2)); 
  assert (count op (cons op l2) = 1); 
  assert (last l = last (cons op l2));
  lem_lastop_suf_0_help l2 op

let diff_inv (#t1 #t2:eqtype) (a l:seq_assoc t1 t2)
  : Lemma (requires length a > 0 /\ distinct_assoc_fst a /\ distinct_assoc_fst l /\
                    is_prefix l a /\ is_prefix l (fst (un_snoc a)))
          (ensures (let a',_ = un_snoc a in
                        (forall e. mem e (diff a' l) ==> mem e (diff a l)))) = 
  let a', last1 = un_snoc a in
  lemma_mem_snoc a' last1;
  lemma_mem_snoc (diff a' l) last1

#push-options "--z3rlimit 50"
let rec remove_id (#t1 #t2:eqtype) (a:seq_assoc t1 t2) (id:t1)
  : Tot (r:seq_assoc t1 t2 {(forall id1. mem_assoc_fst id1 r <==> mem_assoc_fst id1 a /\ id <> id1) /\
                           count_assoc_fst id r = 0 /\
                           (forall id1. id1 <> id ==> count_assoc_fst id1 a = count_assoc_fst id1 r)})
        (decreases length a) =
  match length a with
  |0 -> a
  |_ -> if fst (head a) = id then 
         (if (not (mem_assoc_fst id (tail a))) then tail a
         else remove_id (tail a) id)
       else (let rl = remove_id (tail a) id in
             mem_cons (head a) rl;
             lemma_append_count_assoc_fst (create 1 (head a)) rl;
             cons (head a) (remove_id (tail a) id))

let rec remove_is_uni (#t1 #t2:eqtype) (a:seq_assoc t1 t2) (id:t1)
  : Lemma (requires mem_assoc_fst id a /\ distinct_assoc_fst a)
          (ensures length (remove_id a id) = length a - 1 /\ distinct_assoc_fst (remove_id a id))
          (decreases length a) = 
  match length a with
  |0 -> ()
  |_ -> if fst (head a) = id then
          (mem_cons (head a) (tail a);
           lemma_append_count_assoc_fst (create 1 (head a)) (tail a);
           distinct_invert_append (create 1 (head a)) (tail a))
        else (let rl = remove_id (tail a) id in 
              mem_cons (head a) (tail a);
              lemma_append_count_assoc_fst (create 1 (head a)) (tail a);
              distinct_invert_append (create 1 (head a)) (tail a);
              assert (distinct_assoc_fst (tail a));
              assert (mem_assoc_fst id (tail a));
              remove_is_uni (tail a) id)

let rec lem_not_mem_id (#t1 #t2:eqtype) (a b al bl:seq_assoc t1 t2)
  : Lemma (requires (forall id. mem_assoc_fst id a <==> mem_assoc_fst id al) /\
                    (forall id. mem_assoc_fst id b <==> mem_assoc_fst id bl) /\
                    (forall id. mem_assoc_fst id al ==> not (mem_assoc_fst id bl)) /\
                    distinct_assoc_fst al /\ distinct_assoc_fst bl /\
                    distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    length al = length a /\
                    length bl = length b)
          (ensures (forall id. mem_assoc_fst id a ==> not (mem_assoc_fst id b)))
          (decreases %[length al]) =
  match length al with
  |0 -> ()
  |_ -> remove_is_uni a (fst (head al));
       remove_is_uni al (fst (head al));
       let ras = (remove_id a (fst (head al))) in
       let ra = (remove_id al (fst (head al))) in
       lem_not_mem_id ras b ra bl

let distinct_snoc_inv (#t1 #t2:eqtype) (l:seq_assoc t1 t2) (op:(t1 & t2))
  : Lemma (requires distinct_assoc_fst (snoc l op) /\ length l > 0)
          (ensures (let l',_ = un_snoc l in
                    distinct_assoc_fst (snoc l' op))) =
  let l',lastop = un_snoc l in
  lemma_append_count_assoc_fst l (create 1 op);
  lemma_append_count_assoc_fst l' (create 1 lastop);
  distinct_append l' (create 1 op)

let lt_snoc (#t:eqtype) (l a:seq_assoc pos t) (op:(pos & t))
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst (snoc a op) /\
                    length a > length l /\
                    is_prefix l a /\
                    is_prefix l (snoc a op) /\
                    is_prefix l (snoc (fst (un_snoc a)) op) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff (snoc a op) l) ==> id < id1))
          (ensures (let a',_ = un_snoc a in
                   (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff (snoc a' op) l) ==> id < id1))) = 
  let a',lastop = un_snoc a in
  lemma_append_count_assoc_fst a' (create 1 lastop);
  lastop_diff l (snoc a op);
  assert (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (fst (un_snoc (diff (snoc a op) l))) ==> id < id1);
  assume (fst (un_snoc (diff (snoc a op) l)) == (diff (snoc a' op) l) ); //todo
  ()

let s1s2'_snoc (#t1 #t2:eqtype) (l a b:seq_assoc t1 t2) (op2:(t1 & t2))
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    distinct_assoc_fst (snoc b op2) /\
                    length b > length l /\
                    is_prefix l a /\ is_prefix l b /\ is_prefix l (snoc b op2) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff (snoc b op2) l))))
          (ensures (let b',_ = un_snoc b in
                   (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff (snoc b' op2) l))))) =
  let b',lastop = un_snoc b in
  lemma_append_count_assoc_fst b' (create 1 lastop);
  un_snoc_prop (snoc b op2);
  lem_diff (snoc b op2) l; 
  lem_inverse l (snoc b op2);
  lem_diff (fst (un_snoc (snoc b op2))) l;
  assume (fst (un_snoc (diff (snoc b op2) l)) == (diff (snoc b' op2) l) ); //todo
  ()

let s1's2_snoc (#t1 #t2:eqtype) (l a b:seq_assoc t1 t2) (op1:(t1 & t2))
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    distinct_assoc_fst (snoc a op1) /\
                    length a > length l /\
                    is_prefix l a /\ is_prefix l b /\ is_prefix l (snoc a op1) /\
                    (forall id. mem_assoc_fst id (diff (snoc a op1) l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (let a',_ = un_snoc a in
                   (forall id. mem_assoc_fst id (diff (snoc a' op1) l) ==> not (mem_assoc_fst id (diff b l))))) =
  let a',lastop = un_snoc a in
  lemma_append_count_assoc_fst a' (create 1 lastop);
  un_snoc_prop (snoc a op1);
  lem_diff (snoc a op1) l; 
  lem_inverse l (snoc a op1);
  lem_diff (fst (un_snoc (snoc a op1))) l;
  assume (fst (un_snoc (diff (snoc a op1) l)) == (diff (snoc a' op1) l) ); //todo
  ()

(*#push-options "--z3rlimit 50"
let s1's2'_snoc (#t1 #t2:eqtype) (l a b:seq_assoc t1 t2) (op1 op2:(t1 & t2))
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    distinct_assoc_fst (snoc a op1) /\ distinct_assoc_fst (snoc b op2) /\
                    length a > length l /\ length b > length l /\
                    is_prefix l a /\ is_prefix l b /\ is_prefix l (snoc a op1) /\ is_prefix l (snoc b op2) /\
                    (forall id. mem_assoc_fst id (diff (snoc a op1) l) ==> not (mem_assoc_fst id (diff (snoc b op2) l))))
          (ensures (let a',_ = un_snoc a in
                    let b',_ = un_snoc b in
                   (forall id. mem_assoc_fst id (diff (snoc a' op1) l) ==> not (mem_assoc_fst id (diff (snoc b' op2) l))))) =
  let a',lastop1 = un_snoc a in  
  let b',lastop2 = un_snoc b in
  lemma_append_count_assoc_fst a' (create 1 lastop1);
  lemma_append_count_assoc_fst b' (create 1 lastop2);
  un_snoc_prop (snoc a op1); un_snoc_prop (snoc b op2);
  lem_diff (snoc a op1) l; lem_diff (snoc b op2) l; 
  lem_inverse l (snoc a op1); lem_inverse l (snoc b op2);
  lem_diff (fst (un_snoc (snoc a op1))) l; lem_diff (fst (un_snoc (snoc b op2))) l;
  assume (fst (un_snoc (diff (snoc a op1) l)) == (diff (snoc a' op1) l) ); //todo
  assume (fst (un_snoc (diff (snoc b op2) l)) == (diff (snoc b' op2) l) ); //todo
  ()
#pop-options*)
