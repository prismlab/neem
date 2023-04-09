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

let lem_inverse (#a:eqtype) (lca s1:Seq.seq a)
  : Lemma (requires is_prefix lca s1 /\
                    Seq.length s1 > Seq.length lca)
          (ensures (is_prefix lca (fst (un_snoc s1)))) 
  = lemma_split (fst (un_snoc s1)) (length lca)
