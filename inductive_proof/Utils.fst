module Utils

open FStar.Seq
open FStar.Ghost
open App
open SeqUtils

let rec inverse_helper (s:concrete_st) (l':log) (op:op_t)
  : Lemma (ensures (let l = Seq.snoc l' op in 
                   (apply_log s l == do (apply_log s l') op))) 
          (decreases length l')
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |1 -> ()
    |_ -> inverse_helper (do s (head l')) (tail l') op

let rec lem_un_snoc_id (a b:log)
  : Lemma (requires length b > 0 /\ a == fst (un_snoc b))
          (ensures (forall id. mem_id id a ==> mem_id id b)) (decreases length a) =
  match length a with
  |0 -> ()
  |_ -> lem_un_snoc_id (tail a) (tail b)
    
let lem_diff (s1 l:log)
  : Lemma (requires distinct_ops s1 /\ is_prefix l s1)
          (ensures distinct_ops (diff s1 l) /\ (forall id. mem_id id (diff s1 l) <==> mem_id id s1 /\ not (mem_id id l)) /\
                   (forall id. mem_id id s1 <==> mem_id id l \/ mem_id id (diff s1 l)) /\
                   (Seq.length s1 > Seq.length l ==> (last s1 == last (diff s1 l) /\ Seq.length (diff s1 l) > 0) /\
                     (let _, l1 = un_snoc s1 in
                      let _, ld = un_snoc (diff s1 l) in
                      l1 = ld) /\
                     (let s1',lastop = un_snoc s1 in 
                       diff s1' l == fst (un_snoc (diff s1 l)))))
  = let s = snd (split s1 (length l)) in
    lemma_split s1 (length l);
    lemma_append_count_assoc_fst l s

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
          (ensures (apply_log s a == apply_log (apply_log s l) (diff a l)) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) == (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |1 -> ()
    |_ -> split_prefix (do s (head l)) (tail l) (tail a)

let un_snoc_prop (a:log)
  : Lemma (requires distinct_ops a /\ length a > 0)
          (ensures (forall id. mem_id id a <==> mem_id id (fst (un_snoc a)) \/ id == fst (last a)) /\
                   (forall id. mem_id id a /\ id <> fst (last a) <==> mem_id id (fst (un_snoc a))) /\
                   (let _, l = un_snoc a in 
                    mem_id (fst l) a) /\ distinct_ops (fst (un_snoc a))) =
  let p, l = un_snoc a in
  lemma_split a (length a - 1);
  lemma_append_count_assoc_fst p (snd (split a (length a - 1)));
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
