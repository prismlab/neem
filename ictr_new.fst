module Ictr_new

open FStar.Seq
open FStar.Ghost

// the concrete state type
// e.g. for the increment only counter (icounter), concrete_st = nat
type concrete_st = nat

// operation type
// (the only operation is increment, so unit is fine)
type op_t = unit

type timestamp_t = nat

type log_entry = timestamp_t & op_t

type log = seq log_entry

unfold
let ( ++ ) (l1 l2:log) = Seq.append l1 l2

let distinct_ops (l:log) : prop = forall (e:log_entry). count e l <= 1

let distinct_invert_append (a b:log)
  : Lemma
      (requires distinct_ops (a ++ b))
      (ensures distinct_ops a /\ distinct_ops b)
      [SMTPat (distinct_ops (a ++ b))]
  = lemma_append_count a b

type st0 = concrete_st & erased (concrete_st & log)

let v_of (s:st0) : concrete_st = fst s
let init_of (s:st0) : GTot concrete_st = fst (snd s)
let ops_of (s:st0) : GTot log = snd (snd s)

let rec seq_foldl (f:concrete_st -> log_entry -> concrete_st) (x:concrete_st) (s:seq log_entry)
  : Tot concrete_st (decreases Seq.length s)
  = if Seq.length s = 0 then x
       else let hd, tl = Seq.head s, Seq.tail s in
            seq_foldl f (f x hd) tl

// apply an operation to a state
let do (s:concrete_st) (_:log_entry) : concrete_st = s + 1

let valid_st (s:st0) : prop =
  (*)distinct_ops (ops_of s) /\*)
  v_of s == seq_foldl do (init_of s) (ops_of s)

type st = s:st0{valid_st s}

let rec lem_foldl (s:concrete_st) (l:log) 
  : Lemma (ensures (seq_foldl do s l) = s + length l) (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

let st_inv (s:st)
  : Lemma (v_of s == init_of s + Seq.length (snd (snd s))) = admit ()

let linearized_merge (s:concrete_st) (l:log) : st = seq_foldl do s l, hide (s,l)

let linearized_merge_spec (s:concrete_st) (l:log)
  : Lemma (v_of (linearized_merge s l) == s + Seq.length l) = admit ()

//conflict resolution
let resolve_conflict (x y:log_entry) : log =
  cons x (cons y empty)

let resolve_conflict_len (x y:log_entry)
  : Lemma (Seq.length (resolve_conflict x y) = 2)
  = ()

let is_x_or_y (#a:Type) (s:seq a{Seq.length s == 1}) (x y : a) =
  Seq.index s 0 == x \/ Seq.index s 0 == y

let is_x_and_y (#a:Type) (s:seq a{Seq.length s == 2}) (x y : a) =
  (Seq.index s 0 == x /\ Seq.index s 1 == y) \/
  (Seq.index s 0 == y /\ Seq.index s 1 == x)

let resolve_conflict_mem (x y:log_entry)
  : Lemma (resolve_conflict_len x y;
           let s = resolve_conflict x y in
           (Seq.length s == 1 ==> is_x_or_y s x y) /\
           (Seq.length s == 2 ==> is_x_and_y s x y))
  = ()

irreducible let pat (l:log) : unit = ()

#set-options "--query_stats"
// l is interleaving of l1 and l2
let rec is_interleaving (l l1 l2:log) 
  : Tot Type0 (decreases %[Seq.length l1; Seq.length l2]) =

  // // l1 and l2 are empty
  //   ((Seq.length l1 == 0 /\ Seq.length l2 == 0) ==> l == empty) 

  //   /\

  // if l1 is empty, then l == l2
  (Seq.length l1 == 0 ==> l == l2)

  /\

  // similarly for l2 being empty
  (Seq.length l2 == 0 ==> l == l1)

  /\

  // // length of l1 and l2 = 1
  // ((Seq.length l1 = 1 /\ Seq.length l2 = 1) ==>

  //   l == (resolve_conflict (last l1) (last l2)))

  // /\

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

let interleaving_helper (l1 l2 l':log)
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

         
              

// concrete merge pre-condition
let concrete_merge_pre (lca a b:concrete_st) : prop
  = a >= lca /\ b >= lca

// concrete merge operation
let concrete_merge (lca:concrete_st) (cst1:concrete_st) (cst2:concrete_st{concrete_merge_pre lca cst1 cst2}) 
  : concrete_st = cst1 + cst2 - lca

let inverse (s:st{length (ops_of s) > 0}) : GTot concrete_st
          // : GTot (r:concrete_st{let p, l = un_snoc (ops_of s) in
          //             (r == seq_foldl do (init_of s) p)})
    = let p, l = un_snoc (ops_of s) in
      let r = seq_foldl do (init_of s) p in
      r

let rec lem_inverse (s:st)
  : Lemma (requires length (ops_of s) > 0)
          (ensures (v_of s == do (inverse s) (last (ops_of s))) /\
                   (inverse s >= init_of s) /\ (v_of s = init_of s + length (ops_of s)))
          (decreases length (ops_of s))
  = match length (ops_of s) with
    |0 -> ()
    |1 -> ()
    |_ -> lem_inverse (seq_foldl do (do (init_of s) (head (ops_of s))) (tail (ops_of s)),
                     (hide (do (init_of s) (head (ops_of s)), (tail (ops_of s)))))


let inverse_st (s:st{Seq.length (ops_of s) > 0}) : st = admit ()

let inverse_st_props (s:st{Seq.length (ops_of s) > 0})
  : Lemma (let inv = inverse_st s in
           init_of inv == init_of s /\
           v_of s == do (v_of inv) (last (ops_of s)) /\
           ops_of inv == Seq.slice (ops_of s) 0 (Seq.length (ops_of s) - 1))
  = admit ()

// length of both branches is > 0
// #set-options "--z3rlimit 1000"
let linearizable_ab_gt0 (lca a b:st)
  : Lemma
      (requires 
          length (ops_of a) > 0 /\ length (ops_of b) > 0 /\
          v_of lca == init_of a /\
          init_of a == init_of b)
      (ensures 
         concrete_merge_pre (v_of lca) (v_of a) (v_of b) /\
         concrete_merge_pre (v_of lca) (inverse a) (inverse b) /\
         (let inv = concrete_merge (v_of lca) (inverse a) (inverse b) in
          concrete_merge (v_of lca) (v_of a) (v_of b) =
          seq_foldl do inv (resolve_conflict (last (ops_of a)) (last (ops_of b))) /\
          (exists l. is_interleaving l (cons (last (ops_of a)) empty ) (cons (last (ops_of b)) empty) /\
                v_of (linearized_merge inv l) == concrete_merge (v_of lca) (v_of a) (v_of b))))
  = lem_inverse a;
    lem_inverse b;
    assert (length (cons (last (ops_of a)) empty) = 1 /\ length (cons (last (ops_of b)) empty) = 1);
    assert (is_interleaving (resolve_conflict (last (cons (last (ops_of a)) empty)) 
                                              (last (cons (last (ops_of b)) empty)))
                            (cons (last (ops_of a)) empty) (cons (last (ops_of b)) empty));()


// length of branch a is > 0 and branch b is 0
let linearizable_a_gt0 (lca a b:st)
  : Lemma
      (requires 
         length (ops_of a) <> 0 /\ length (ops_of b) = 0 /\
         v_of lca == init_of a /\
         init_of a == init_of b)
      (ensures 
         concrete_merge_pre (v_of lca) (v_of a) (v_of b) /\
         concrete_merge (v_of lca) (v_of a) (v_of b) =
         seq_foldl do (v_of lca) (ops_of a) /\
         (exists l. is_interleaving l (ops_of a) (ops_of b) /\
               v_of (linearized_merge (v_of lca) l) == concrete_merge (v_of lca) (v_of a) (v_of b)))
  = lem_inverse a;
    assert (is_interleaving (ops_of a) (ops_of a) (ops_of b)); ()


// length of branch b is > 0 and branch a is 0
let linearizable_b_gt0 (lca a b:st)
  : Lemma
      (requires 
         length (ops_of a) = 0 /\ length (ops_of b) <> 0 /\
         v_of lca == init_of a /\
         init_of a == init_of b)
      (ensures 
         concrete_merge_pre (v_of lca) (v_of a) (v_of b) /\
         concrete_merge (v_of lca) (v_of a) (v_of b) =
         seq_foldl do (v_of lca) (ops_of b) /\
         (exists l. is_interleaving l (ops_of a) (ops_of b) /\
               v_of (linearized_merge (v_of lca) l) == concrete_merge (v_of lca) (v_of a) (v_of b)))
  = lem_inverse b;
    assert (is_interleaving (ops_of b) (ops_of a) (ops_of b)); ()


// length of both branches is 0
#push-options "--z3rlimit 20"
let linearizable_ab_0 (lca a b:st)
  : Lemma
      (requires 
         length (ops_of a) = 0 /\ length (ops_of b) = 0 /\
         v_of lca == init_of a /\
         init_of a == init_of b)
      (ensures 
         concrete_merge (v_of lca) (v_of a) (v_of b) = v_of lca /\
         (exists l. is_interleaving l (ops_of a) (ops_of b) /\
               v_of (linearized_merge (v_of lca) l) == concrete_merge (v_of lca) (v_of a) (v_of b)))
  = assert (is_interleaving empty (ops_of a) (ops_of b)); ()
#pop-options

// #set-options "--initial_fuel 0 --max_fuel 2 --initial_ifuel 0 --max_ifuel 2 --z3rlimit 2000"

let interleaving_predicate (l:log) (lca s1:st)
  (s2:st{concrete_merge_pre (v_of lca) (v_of s1) (v_of s2)}) =
  is_interleaving l (ops_of s1) (ops_of s2) /\
  v_of (linearized_merge (v_of lca) l) ==
  concrete_merge (v_of lca) (v_of s1) (v_of s2)

#set-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let rec linearizable (lca s1 s2:st)
  : Lemma 
      (requires 
         v_of lca == init_of s1 /\
         init_of s1 == init_of s2)
      (ensures
         concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
         (exists l. interleaving_predicate l lca s1 s2))
      (decreases %[length (ops_of s1); length (ops_of s2)])

  = st_inv lca; st_inv s1; st_inv s2;
    assert (concrete_merge_pre (v_of lca) (v_of s1) (v_of s2));
    
    if Seq.length (ops_of s1) = 0
    then begin
      linearized_merge_spec (v_of lca) (ops_of s2);
      introduce exists l. interleaving_predicate l lca s1 s2
      with (ops_of s2)
      and ()
    end
    else begin
      if Seq.length (ops_of s2) = 0
      then begin
        linearized_merge_spec (v_of lca) (ops_of s1);
        introduce exists l. interleaving_predicate l lca s1 s2
        with (ops_of s1)
        and ()
      end
      else begin
        let prefix1, hd1 = un_snoc (ops_of s1) in
        let prefix2, hd2 = un_snoc (ops_of s2) in
  
        let inv1 = inverse_st s1 in
        let inv2 = inverse_st s2 in

        inverse_st_props s1;
        inverse_st_props s2;

        linearizable lca inv1 inv2;
        eliminate exists l'. interleaving_predicate l' lca inv1 inv2
        returns exists l. interleaving_predicate l lca s1 s2
        with _. begin
          let l = Seq.append l' (resolve_conflict hd1 hd2) in
          introduce exists l. interleaving_predicate l lca s1 s2
          with l
          and interleaving_helper (ops_of s1) (ops_of s2) l';
              admit ()
        end
      end
    end
