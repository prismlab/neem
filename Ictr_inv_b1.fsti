module Ictr_inv_b1

open FStar.Seq
open FStar.Ghost

#set-options "--query_stats"

// the concrete state type
val concrete_st : Type0

// init state
val init_st : concrete_st

// operation type
val op_t : Type0

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

let le (a b:timestamp_t) : bool = a < b
  
#push-options "--z3rlimit 50"
let rec lemma_append_count_id (lo:log) (hi:log)
  : Lemma
      (ensures (forall x. count_id x (lo ++ hi) = (count_id x lo + count_id x hi)))
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
val do (s:concrete_st) (_:log_entry) : concrete_st

let rec seq_foldl (f:concrete_st -> log_entry -> concrete_st) (x:concrete_st) (s:log)
  : Tot concrete_st (decreases Seq.length s) =

  if Seq.length s = 0
  then x
  else let hd, tl = Seq.head s, Seq.tail s in
    seq_foldl f (f x hd) tl

let rec linearized_merge (x:concrete_st) (l:log) 
  : Tot (r:concrete_st{(length l > 0 ==> r == do (seq_foldl do x (fst (un_snoc l))) (last l)) /\
                       (r == seq_foldl do x l)}) (decreases length l) = 
  match length l with
  |0 -> x
  |1 -> do x (head l)
  |_ -> linearized_merge (do x (head l)) (tail l)

let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  v_of s == linearized_merge init_st (ops_of s)

type st = s:st0{valid_st s}

//conflict resolution
val resolve_conflict (x y:log_entry) : log

// l is interleaving of l1 and l2
let rec is_interleaving (l l1 l2:log)
  : Tot Type0 (decreases %[Seq.length l1; Seq.length l2]) =

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
val concrete_merge (lca:concrete_st) (cst1:concrete_st) (cst2:concrete_st{concrete_merge_pre lca cst1 cst2}) : concrete_st

let is_prefix (p:log) (l:log) : Tot prop =
  Seq.length l >= Seq.length p /\ Seq.equal p (Seq.slice l 0 (Seq.length p))

let diff (s1:log) (lca:log{is_prefix lca s1}) 
  : Tot (l:log{(length s1 = length lca + length l) /\ (s1 == lca ++ l)}) =
  let s = snd (split s1 (length lca)) in
  lemma_split s1 (length lca);
  s

#push-options "--z3rlimit 100"
let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{(v_of s == do (v_of i) (last (ops_of s))) /\
               (ops_of i == fst (un_snoc (ops_of s))) /\
               (ops_of s == snoc (ops_of i) (last (ops_of s))) /\
               is_prefix (ops_of i) (ops_of s) /\
               (forall id. mem_id id (ops_of i) <==> mem_id id (ops_of s) /\ id <> fst (last (ops_of s)))}) = 
  let p, l = un_snoc (ops_of s) in
  let r = seq_foldl do init_st p in
  lemma_split (ops_of s) (length (ops_of s) - 1);
  lemma_append_count_id p (snd (split (ops_of s) (length (ops_of s) - 1)));
  distinct_invert_append p (snd (split (ops_of s) (length (ops_of s) - 1)));
  (r, hide p)

let lem_inverse (lca:st) (s1:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    length (diff (ops_of s1) (ops_of lca)) > 0)
          (ensures (is_prefix (ops_of lca) (ops_of (inverse_st s1)))) 
  = lemma_split (ops_of (inverse_st s1)) (length (ops_of lca))
#pop-options

let interleaving_predicate (l:log) (lca s1:st)
  (s2:st{concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\ 
         is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2)}) =
  is_interleaving l (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) /\
  linearized_merge (v_of lca) l ==
  concrete_merge (v_of lca) (v_of s1) (v_of s2)

val merge_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (ops_of s2))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))

val merge_inv_s1_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (diff (ops_of s1) (ops_of lca)) > 0)
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2))

val linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (diff (ops_of s1) (ops_of lca)) = 0)
          (ensures concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
                   seq_foldl do (v_of lca) (diff (ops_of s2) (ops_of lca)))

let linearizable_s1_01 (lca s1 s2:st)
  : Lemma (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (diff (ops_of s1) (ops_of lca)) = 0) 
          (ensures (exists l. interleaving_predicate l lca s1 s2)) =
  assert (is_interleaving (diff (ops_of s2) (ops_of lca)) (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)));
  linearizable_s1_0 lca s1 s2

val linearizable_s1_gt0 (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (diff (ops_of s1) (ops_of lca)) > 0 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                    interleaving_predicate l' lca (inverse_st s1) s2)
          (ensures (let l = Seq.snoc l' (last (ops_of s1)) in
                   linearized_merge (v_of lca) l == 
                   concrete_merge (v_of lca) (v_of s1) (v_of s2)))

let interleaving_helper (lca s1 s2 l':log)
  : Lemma
      (requires Seq.length s1 > 0 /\
                is_prefix lca (fst (un_snoc s1)) /\ is_prefix lca s2 /\
                is_interleaving l' (diff (fst (un_snoc s1)) lca) (diff s2 lca) )
      (ensures (let prefix1, last1 = un_snoc s1 in
               is_interleaving (Seq.snoc l' last1) (diff s1 lca) (diff s2 lca)))
  = assert (is_interleaving l' (fst (un_snoc (diff s1 lca))) (diff s2 lca) );
    let prefix1, last1 = un_snoc (diff s1 lca) in
    let l = Seq.snoc l' last1 in
    introduce exists l'. is_interleaving l' prefix1 (diff s2 lca) /\
                    l == Seq.snoc l' last1
    with l'
    and ()

#push-options "--z3rlimit 50"
let interleaving_s1_inv (lca s1 s2:st) (l':log)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (diff (ops_of s1) (ops_of lca)) > 0 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                    interleaving_predicate l' lca (inverse_st s1) s2)
          (ensures (let l = Seq.snoc l' (last (ops_of s1)) in
                    interleaving_predicate l lca s1 s2 /\
                    (exists l. interleaving_predicate l lca s1 s2))) =
  interleaving_helper (ops_of lca) (ops_of s1) (ops_of s2) l'; 
  linearizable_s1_gt0 lca s1 s2 l'
#pop-options
  
let lem_diff (s1:log) (l:log{is_prefix l s1})
      : Lemma (requires distinct_ops s1)
              (ensures distinct_ops (diff s1 l) /\ (forall id. mem_id id (diff s1 l) <==> mem_id id s1 /\ not (mem_id id l)))
  = let s = snd (split s1 (length l)) in
    lemma_split s1 (length l);
    lemma_append_count_id l s

#push-options "--z3rlimit 100"
let linearizable_s1_gt0_pre (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> le id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> le id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    Seq.length (diff (ops_of s1) (ops_of lca)) > 0 /\ Seq.length (ops_of s1) > 0 /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures (let prefix1, last1 = un_snoc (ops_of s1) in
                    let inv1 = inverse_st s1 in 
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> le id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))) =
  let prefix1, last1 = un_snoc (ops_of s1) in
  let inv1 = inverse_st s1 in 
  lem_inverse lca s1;
  merge_inv_s1_prop lca s1 s2; 
  lemma_split (ops_of inv1) (length (ops_of lca));
  lem_diff (ops_of inv1) (ops_of lca); 
  lem_diff (ops_of s1) (ops_of lca)
#pop-options

#set-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let rec linearizable (lca s1 s2:st)
  : Lemma 
      (requires 
         is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2) /\
         (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> le id id1) /\
         (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> le id id1) /\
         (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
      (ensures 
         concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
         (exists l. interleaving_predicate l lca s1 s2))
      (decreases length (ops_of s1))

  = merge_prop lca s1 s2;

    if Seq.length (diff (ops_of s1) (ops_of lca)) = 0
    then begin 
      linearizable_s1_01 lca s1 s2
    end
    else begin 
        let prefix1, last1 = un_snoc (ops_of s1) in
        let inv1 = inverse_st s1 in 

        linearizable_s1_gt0_pre lca s1 s2;

        linearizable lca inv1 s2;

        eliminate exists l'. interleaving_predicate l' lca inv1 s2
        returns exists l. interleaving_predicate l lca s1 s2
        with _. begin
          let l = Seq.snoc l' last1 in
          introduce exists l. interleaving_predicate l lca s1 s2
          with l
          and begin
            interleaving_s1_inv lca s1 s2 l'
          end
        end
      end

