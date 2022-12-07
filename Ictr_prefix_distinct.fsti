module Ictr_prefix_distinct

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

let distinct_ops (l:log) : prop = forall (id:nat). count_id id l <= 1

let le (a b:timestamp_t) : bool = a < b

//let sorted_ops (l:log) : bool = Seq.sorted (fun x y -> le (fst x) (fst y)) l

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
      (*)[SMTPat (distinct_ops (a ++ b))]*)
= lemma_append_count_id a b

(*)let rec lem_sorted_invert_append (lo:log) (hi:log)
  : Lemma (requires true)
          (ensures (~ (sorted_ops hi) ==> ~ (sorted_ops (lo ++ hi))) /\
                   (~ (sorted_ops lo) ==> ~ (sorted_ops (lo ++ hi))))
          (decreases length lo)
    = if length lo = 0
         then cut (equal (lo ++ hi) hi)
         else (cut (equal (cons (head lo) ((tail lo) ++ hi)) (lo ++ hi));
              lem_sorted_invert_append (tail lo) hi;
              let tl_l_h = (tail lo) ++ hi in
              let lh = cons (head lo) tl_l_h in
              cut (equal (tail lh) tl_l_h))

let sorted_invert_append (lo:log) (hi:log)
  : Lemma (requires sorted_ops (lo ++ hi))
          (ensures sorted_ops hi /\ sorted_ops lo) =
  lem_sorted_invert_append lo hi*)

type st0 = concrete_st & erased (concrete_st & log)

let v_of (s:st0) : concrete_st = fst s
let init_of (s:st0) : GTot concrete_st = fst (snd s)
let ops_of (s:st0) : GTot log = snd (snd s)

// apply an operation to a state
val do (s:concrete_st) (_:log_entry) : concrete_st

let rec seq_foldl (f:concrete_st -> log_entry -> concrete_st) (x:concrete_st) (s:log)
  : Tot concrete_st (decreases Seq.length s) =

  if Seq.length s = 0
  then x
  else let hd, tl = Seq.head s, Seq.tail s in
    seq_foldl f (f x hd) tl

let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
 // sorted_ops (ops_of s) /\
  v_of s == seq_foldl do (init_of s) (ops_of s)

type st = s:st0{valid_st s}

let linearized_merge (s:concrete_st) (l:log) : concrete_st = seq_foldl do s l

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
  : Tot (l:log{(length s1 = length lca + length l) /\ (Seq.equal s1 (lca ++ l)) /\
               (forall id. mem_id id s1 <==> mem_id id lca \/ mem_id id l)}) =
  let s = snd (split s1 (length lca)) in
  lemma_split s1 (length lca);
  lemma_append_count_id lca s;
  s

let inverse_st (s:st{Seq.length (ops_of s) > 0}) : GTot st = 
  let p, l = un_snoc (ops_of s) in
  let r = seq_foldl do (init_of s) p in
  lemma_split (ops_of s) (length p);
  lemma_append_count_id p (snd (split (ops_of s) (length (ops_of s) - 1)));
  //sorted_invert_append p (snd (split (ops_of s) (length (ops_of s) - 1)));
  (r, hide (init_of s, p))

val merge_prop (lca s1 s2:st)
    : Lemma (requires init_of lca == init_st /\
                      init_of lca == init_of s1 /\
                      init_of lca == init_of s2 /\ 
                      is_prefix (ops_of lca) (ops_of s1) /\ 
                      is_prefix (ops_of lca) (ops_of s2))
            (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))

val merge_inv_prop (lca s1 s2:st)
    : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\ 
                      is_prefix (ops_of lca) (ops_of s2) /\
                      length (diff (ops_of s1) (ops_of lca)) > 0 /\ 
                      length (diff (ops_of s2) (ops_of lca)) > 0 /\
                      init_of lca == init_st /\
                      init_of lca == init_of s1 /\
                      init_of lca == init_of s2)
            (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))

let rec inverse_st_props (s:st)
  : Lemma (requires length (ops_of s) > 0)
          (ensures (let inv = inverse_st s in
                    v_of s == do (v_of inv) (last (ops_of s)) /\
                    ops_of inv == Seq.slice (ops_of s) 0 (Seq.length (ops_of s) - 1) /\
                    ops_of s == snoc (ops_of inv) (last (ops_of s)) /\
                    is_prefix (ops_of inv) (ops_of s) /\
                    init_of s == init_of inv))
           (decreases length (ops_of s)) =
  match length (ops_of s) with
  |0 -> ()
  |1 -> ()
  |_ -> lemma_split (ops_of s) (length (ops_of s) - 1);
       inverse_st_props (seq_foldl do (do (init_of s) (head (ops_of s))) (tail (ops_of s)),
                         hide ((do (init_of s) (head (ops_of s)), (tail (ops_of s)))))

#push-options "--z3rlimit 200"
let rec inverse_st_props1 (s:st)
  : Lemma (requires length (ops_of s) > 0)
          (ensures (let inv = inverse_st s in
                    forall id. mem_id id (ops_of inv) <==> mem_id id (ops_of s) /\ id <> fst (last (ops_of s))))
           (decreases length (ops_of s)) =
  match length (ops_of s) with
  |0 -> ()
  |1 -> ()
  |_ -> lemma_split (ops_of s) (length (ops_of s) - 1);
       distinct_invert_append (ops_of (inverse_st s)) (snd (split (ops_of s) (length (ops_of s) - 1)));
       assert (distinct_ops (tail (ops_of s)));
       inverse_st_props1 (seq_foldl do (do (init_of s) (head (ops_of s))) (tail (ops_of s)),
                         hide ((do (init_of s) (head (ops_of s)), (tail (ops_of s)))))


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

val linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires 
             init_of lca == init_st /\
             init_of lca == init_of s1 /\
             init_of lca == init_of s2 /\ 
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             is_prefix (ops_of lca) (ops_of s1) /\
             is_prefix (ops_of lca) (ops_of s2) /\
             Seq.length (diff (ops_of s1) (ops_of lca)) = 0) 
          (ensures 
             concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
             seq_foldl do (v_of lca) (diff (ops_of s2) (ops_of lca)) /\
             interleaving_predicate (diff (ops_of s2) (ops_of lca)) lca s1 s2 /\
               (exists l. interleaving_predicate l lca s1 s2))

val linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires 
             init_of lca == init_st /\
             init_of lca == init_of s1 /\
             init_of lca == init_of s2 /\ 
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             is_prefix (ops_of lca) (ops_of s1) /\
             is_prefix (ops_of lca) (ops_of s2) /\
             Seq.length (diff (ops_of s2) (ops_of lca)) = 0)
          (ensures 
             concrete_merge (v_of lca) (v_of s1) (v_of s2) == 
             seq_foldl do (v_of lca) (diff (ops_of s1) (ops_of lca)) /\
             interleaving_predicate (diff (ops_of s1) (ops_of lca)) lca s1 s2 /\
               (exists l. interleaving_predicate l lca s1 s2))

#set-options "--z3rlimit 50"
val linearizable_s1s2_gt0 (lca s1 s2:st) (l':log)
  : Lemma (requires 
             init_of lca == init_st /\
             init_of lca == init_of s1 /\
             init_of lca == init_of s2 /\ 
             is_prefix (ops_of lca) (ops_of s1) /\
             is_prefix (ops_of lca) (ops_of s2) /\
             Seq.length (diff (ops_of s1) (ops_of lca)) > 0 /\
             Seq.length (diff (ops_of s2) (ops_of lca)) > 0 /\
             is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
             is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
             concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
             concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)) /\
             interleaving_predicate l' lca (inverse_st s1) (inverse_st s2))
          (ensures
           (let l = Seq.append l' (resolve_conflict (last (ops_of s1)) (last (ops_of s2))) in
               linearized_merge (v_of lca) l == 
               linearized_merge (linearized_merge (v_of lca) l')
                 (resolve_conflict (last (ops_of s1)) (last (ops_of s2)))) /\

               concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
               linearized_merge (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
                 (resolve_conflict (last (ops_of s1)) (last (ops_of s2))))

let interleaving_helper (lca l1 l2 l':log)
  : Lemma
      (requires
         Seq.length l1 > 0 /\ Seq.length l2 > 0 /\
        (let prefix1, last1 = un_snoc l1 in
         let prefix2, last2 = un_snoc l2 in
         is_interleaving l' prefix1 prefix2))
      (ensures 
         (let prefix1, last1 = un_snoc l1 in
          let prefix2, last2 = un_snoc l2 in
          is_interleaving (Seq.append l' (resolve_conflict last1 last2)) l1 l2))
  = let prefix1, last1 = un_snoc l1 in
    let prefix2, last2 = un_snoc l2 in
    let l = Seq.append l' (resolve_conflict last1 last2) in
    introduce exists l'. is_interleaving l' prefix1 prefix2 /\
              l == Seq.append l' (resolve_conflict last1 last2)
  with l'
  and ()

#push-options "--z3rlimit 200"
let inverse_helper (lca s1 s2:log)
  : Lemma 
      (requires 
            is_prefix lca s1 /\
            is_prefix lca s2 /\
            Seq.length (diff s1 lca) > 0 && Seq.length (diff s2 lca) > 0 /\
            is_prefix lca (fst (un_snoc s1)) /\
            is_prefix lca (fst (un_snoc s2)) /\
            //sorted_ops s1 /\ sorted_ops s2 /\ sorted_ops lca /\
            //sorted_ops (fst (un_snoc s1)) /\ sorted_ops (fst (un_snoc s2)) /\
            distinct_ops s1 /\ distinct_ops s2 /\ distinct_ops lca /\ 
            distinct_ops (fst (un_snoc s1)) /\ distinct_ops (fst (un_snoc s2)) /\
            (forall id. mem_id id lca ==> not (mem_id id (diff s1 lca))) /\
            (forall id. mem_id id lca ==> not (mem_id id (diff s2 lca))) /\
            (forall id id1. mem_id id lca /\ mem_id id1 (diff s1 lca) ==> le id id1) /\
            (forall id id1. mem_id id lca /\ mem_id id1 (diff s2 lca) ==> le id id1) /\
            (forall id. mem_id id (diff s1 lca) ==> not (mem_id id (diff s2 lca))) /\
            (forall id. mem_id id (fst (un_snoc s1)) <==> mem_id id s1 /\ id <> fst (last s1)) /\
            (forall id. mem_id id (fst (un_snoc s2)) <==> mem_id id s2 /\ id <> fst (last s2)))
      (ensures
         (forall id. mem_id id lca ==> not (mem_id id (diff (fst (un_snoc s1)) lca))) /\
         (forall id. mem_id id lca ==> not (mem_id id (diff (fst (un_snoc s2)) lca))) /\
         (forall id id1. mem_id id lca /\ mem_id id1 (diff (fst (un_snoc s1)) lca) ==> le id id1) /\
         (forall id id1. mem_id id lca /\ mem_id id1 (diff (fst (un_snoc s2)) lca) ==> le id id1) /\ 
         (forall id. mem_id id (diff (fst (un_snoc s1)) lca) ==> not (mem_id id (diff (fst (un_snoc s2)) lca))))
  = lemma_split (fst (un_snoc s1)) (length lca); 
    lemma_split (fst (un_snoc s2)) (length lca);
    lemma_split s1 (length lca);
    distinct_invert_append lca (diff (fst (un_snoc s1)) lca);
    assert (forall id. mem_id id lca ==> not (mem_id id (diff (fst (un_snoc s1)) lca))); 
    lemma_split s2 (length lca);
    distinct_invert_append lca (diff (fst (un_snoc s2)) lca);
    assert (forall id. mem_id id lca ==> not (mem_id id (diff (fst (un_snoc s2)) lca))); ()
#pop-options

#set-options "--z3rlimit 1200 --fuel 2 --ifuel 2"
let rec linearizable (lca s1 s2:st)
  : Lemma 
      (requires 
         init_of lca == init_st /\
         init_of lca == init_of s1 /\
         init_of lca == init_of s2 /\ 
         is_prefix (ops_of lca) (ops_of s1) /\
         is_prefix (ops_of lca) (ops_of s2) /\
         (forall id. mem_id id (ops_of lca) ==> not (mem_id id (diff (ops_of s1) (ops_of lca)))) /\
         (forall id. mem_id id (ops_of lca) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
         (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> le id id1) /\
         (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> le id id1) /\
         (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
      (ensures 
         concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
         (exists l. interleaving_predicate l lca s1 s2))
      (decreases %[length (ops_of s1); length (ops_of s2)])

  = merge_prop lca s1 s2;

    if Seq.length (diff (ops_of s1) (ops_of lca)) = 0
    then begin
      linearizable_s1_0 lca s1 s2
    end
    else begin 
      if Seq.length (diff (ops_of s2) (ops_of lca)) = 0
      then begin
        linearizable_s2_0 lca s1 s2
        end
      else begin
        assert (length (diff (ops_of s1) (ops_of lca)) > 0 /\ length (diff (ops_of s2) (ops_of lca)) > 0); 
        assert (length (ops_of s1) > 0 /\ length (ops_of s2) > 0);
        let prefix1, last1 = un_snoc (ops_of s1) in
        let prefix2, last2 = un_snoc (ops_of s2) in

        let inv1 = inverse_st s1 in
        let inv2 = inverse_st s2 in

        inverse_st_props s1; inverse_st_props s2; 
        inverse_st_props1 s1; inverse_st_props1 s2; 
        lem_inverse lca s1; lem_inverse lca s2; 

        merge_inv_prop lca s1 s2; 
        lemma_split (ops_of inv1) (length (ops_of lca));
        lemma_split (ops_of inv2) (length (ops_of lca));

        inverse_helper (ops_of lca) (ops_of s1) (ops_of s2);
        linearizable lca inv1 inv2;

        eliminate exists l'. interleaving_predicate l' lca inv1 inv2
        returns exists l. interleaving_predicate l lca s1 s2
        with _. begin
          let l = Seq.append l' (resolve_conflict last1 last2) in
          introduce exists l. interleaving_predicate l lca s1 s2
          with l
          and begin 
            interleaving_helper (ops_of lca) (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) l';
            linearizable_s1s2_gt0 lca s1 s2 l'
          end
        end
      end
    end



(*
  type order (l:log) = 
    (forall id. mem_id id l ==> ~ (le id id)) /\
    (forall id id1 id2. mem_id id l /\ mem_id id1 l /\ mem_id id2 l /\ le id id1 /\ le id1 id2 ==> le id id2) /\
    (forall id id1. mem_id id l /\ mem_id id1 l /\ le id id1 ==> ~ (le id1 id)) (*)/\
    (forall i j. i < length l /\ i < j ==> fst (index l i) < fst (index l j)*)*)
