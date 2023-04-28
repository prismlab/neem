module SeqUtils

open FStar.Seq

let lt (a b:nat) : bool = a < b

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
                     (let _, l1 = un_snoc s1 in
                      let _, ld = un_snoc (diff s1 l) in
                      l1 = ld) /\
                     (let s1',lastop = un_snoc s1 in 
                       diff s1' l == fst (un_snoc (diff s1 l)))))
  = lemma_append_count_assoc_fst l (diff s1 l)

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
                    (forall id id1. mem_assoc_fst id lca /\ mem_assoc_fst id1 (diff s1 lca) ==> lt id id1))
          (ensures (let _, lastop = un_snoc s1 in
                    (forall id. mem_assoc_fst id lca ==> lt id (fst lastop)))) =
    distinct_invert_append lca (diff s1 lca); 
    let pre, lst = un_snoc s1 in
    lem_diff s1 lca;
    mem_ele_id lst (diff s1 lca)

let lastop_diff (#t:eqtype) (l a:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ is_prefix l a /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> lt id id1) /\
                    length a > length l)
          (ensures (length (diff a l) > 0) /\
                   (let p, last = un_snoc a in
                   mem_assoc_fst (fst last) a /\ mem_assoc_fst (fst last) (diff a l) /\
                   (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff p l) ==> lt id id1)))
  = un_snoc_prop a;
    lem_diff a l;
    un_snoc_prop (diff a l);
    lem_inverse l a

let inverse_diff_id_s1' (#t:eqtype) (l a b:seq_assoc pos t)
  : Lemma (requires distinct_assoc_fst l /\ distinct_assoc_fst a /\ distinct_assoc_fst b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ 
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> lt id id1) /\
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
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> lt id id1) /\
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
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> lt id id1) /\
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
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_assoc_fst id (diff a l) ==> not (mem_assoc_fst id (diff b l))))
          (ensures (let p, la = un_snoc a in
                    let _, lb = un_snoc b in
                    fst la <> fst lb)) =
  lastop_diff l a;
  lastop_diff l b

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
                    (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff (snoc a op) l) ==> lt id id1))
          (ensures (let a',_ = un_snoc a in
                   (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (diff (snoc a' op) l) ==> lt id id1))) = 
  let a',lastop = un_snoc a in
  lemma_append_count_assoc_fst a' (create 1 lastop);
  lastop_diff l (snoc a op);
  assert (forall id id1. mem_assoc_fst id l /\ mem_assoc_fst id1 (fst (un_snoc (diff (snoc a op) l))) ==> lt id id1);
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
