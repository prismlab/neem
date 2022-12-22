module App

open FStar.Seq
open FStar.Ghost
module L = FStar.List.Tot

let rec unique_s (l:list nat) =
  match l with
  |[] -> true
  |id::xs -> not (L.mem id xs) && unique_s xs
  
// the concrete state type
// It is a list of unique elements
type concrete_st = l:list nat{unique_s l}

//initial state
let init_st = []

// operation type
// (the only operation is Add, so nat is fine)
type op_t = nat

// concrete do pre-condition
let concrete_do_pre _ _ = true

// apply an operation to a state
let do (s:concrete_st) (op:log_entry) : concrete_st = 
  if (L.mem (snd op) s) then s else (snd op)::s

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = list nat

// init state 
let init_st_s = []

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:log_entry) : concrete_st_s = snd op::s

//equivalence relation between the concrete states of sequential type and MRDT
let eq (st_s:concrete_st_s) (st:concrete_st) = 
  (forall e. L.mem e st_s <==> L.mem e st)

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq st_s st)
          (ensures eq (do_s st_s op) (do st op)) 
  = ()

////////////////////////////////////////////////////////////////

let rec mem_ele (e:nat) (l:log) : Tot bool (decreases length l) =
  match length l with
  |0 -> false
  |_ -> snd (head l) = e || mem_ele e (tail l)
  
let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires foldl_prop s l)
          (ensures (length l = 0 ==> s = seq_foldl s l) /\
                   (forall e. L.mem e (seq_foldl s l) <==> L.mem e s \/ mem_ele e l))
          (decreases length l)
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

//conflict resolution
let resolve_conflict (x y:log_entry) : log =
  cons x (cons y empty)

// concrete merge pre-condition
let concrete_merge_pre lca a b : prop = 
  (forall e. L.mem e lca ==> L.mem e a /\ L.mem e b)

let rec concrete_merge1 (lca:concrete_st) (s1:concrete_st) (s2:concrete_st) 
  : Pure concrete_st (requires concrete_merge_pre lca s1 s2)
                     (ensures (fun r -> (forall e. L.mem e r <==> L.mem e s1 \/ L.mem e s2)))
                     (decreases %[lca; s1; s2]) = 
  match lca, s1, s2 with
    |[],[],[] -> []
    |x::xs,_,_ -> concrete_merge1 xs s1 s2
    |[],x::xs,_ -> if L.mem x s2 then (concrete_merge1 [] xs s2) 
                    else x::(concrete_merge1 [] xs s2)
    |[],[],_ -> s2

// concrete merge operation
let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) : concrete_st =
  concrete_merge1 lca s1 s2

let merge_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (ops_of s2))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2)) = 
  lem_foldl init_st (ops_of s1); 
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))

let merge_inv_s1_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s1) > length (ops_of lca))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) =
  lem_foldl init_st (ops_of s2); 
  lem_foldl init_st (ops_of (inverse_st s1));
  lem_inverse (ops_of lca) (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of (inverse_st s1));
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of (inverse_st s1)) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))

let merge_inv_s2_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) =
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of (inverse_st s2));
  lem_inverse (ops_of lca) (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of (inverse_st s2));
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of (inverse_st s2)) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

let linearizable_s1_01 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                ops_of s1 = ops_of lca /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
      (ensures (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                     L.mem e (seq_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))))) =
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))
  
let linearizable_s2_01 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                ops_of s2 = ops_of lca /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
      (ensures (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                     L.mem e (seq_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))))) =
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

let rec inverse_helper1 (s:concrete_st) (l':log) (op:log_entry)
  : Lemma (requires foldl_prop s l' /\ concrete_do_pre (seq_foldl s l') op)
          (ensures (let l = Seq.snoc l' op in
                    foldl_prop s l /\
                    seq_foldl s l == do (seq_foldl s l') op /\
                    (forall e. L.mem e (seq_foldl s l) <==> L.mem e (seq_foldl s l') \/ e = snd op)))
          (decreases length l')
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |1 -> ()
    |_ -> inverse_helper1 (do s (head l')) (tail l') op

let lem_do (s:concrete_st) (op:log_entry)
  : Lemma (ensures (forall e. L.mem e (do s op) <==> L.mem e s \/ e = snd op))
  = ()
  
#push-options "--z3rlimit 200"
let linearizable_s1_gt01 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) = last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                  concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                  (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                        L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)))) =
  let p1, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  inverse_helper1 init_st p1 last1;
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  assert (concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1);
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) \/ e = snd last1);
  lem_do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1;
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1));
  ()

let linearizable_s2_gt01 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                   (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                         L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  inverse_helper1 init_st p2 last2;
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of s2);
  assert (concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2); 
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) \/ e = snd last2);
  lem_do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2;
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2));
  ()
#pop-options
