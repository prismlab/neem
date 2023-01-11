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

(*let (==) (a b:concrete_st) =
  (forall e. L.mem e a <==> L.mem e b)

let commutative (a b:concrete_st) 
  : Lemma (requires a == b)
          (ensures b == a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires (a == b) /\ (b == c))
          (ensures (a == c)) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a = b)
          (ensures a == b) = ()*)
          
// operation type
// (the only operation is Add, so nat is fine)
type op_t = nat

// concrete do pre-condition
let concrete_do_pre _ _ = true

// apply an operation to a state
let do (s:concrete_st) (op:log_entry) 
  : (r:concrete_st{(forall e. L.mem e r <==> L.mem e s \/ e = snd op) /\
                   (L.mem (snd op) s <==> r = s) /\
                   (not (L.mem (snd op) s) <==> r = (snd op)::s)}) = 
  if (L.mem (snd op) s) then s else (snd op)::s
  
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = l:list nat{unique_s l}

// init state 
let init_st_s = []

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:log_entry) : concrete_st_s = 
  if (L.mem (snd op) s) then s else (snd op)::s

//equivalence relation between the concrete states of sequential type and MRDT
let eq (st_s:concrete_st_s) (st:concrete_st) = st_s == st

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

let resolve_conflict_prop (x y:log_entry)
  : Lemma (requires fst x <> fst y)
          (ensures last (resolve_conflict x y) <> x)
  = ()
  
// concrete merge pre-condition
let concrete_merge_pre lca a b : prop = 
  (forall e. L.mem e lca ==> L.mem e a /\ L.mem e b)

// concrete merge operation
let rec concrete_merge1 (lca:concrete_st) (s1:concrete_st) (s2:concrete_st) 
  : Pure concrete_st (requires concrete_merge_pre lca s1 s2)
                     (ensures (fun r -> (forall e. L.mem e r <==> L.mem e s1 \/ L.mem e s2)))
                     (decreases %[lca;s1;s2]) =
  match lca, s1, s2 with
  |[],[],[] -> []
  |x::xs,_,_ -> concrete_merge1 xs s1 s2
  |[],x::xs,_ -> if L.mem x s2 then concrete_merge1 [] xs s2 else x::(concrete_merge1 [] xs s2)
  |[],[],x::xs -> x::concrete_merge1 [] [] xs

let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2})
  : (r:concrete_st{(forall e. L.mem e r <==> L.mem e lca \/ L.mem e s1 \/ L.mem e s2)})=
  concrete_merge1 lca s1 s2
                    
#push-options "--z3rlimit 200"
let merge_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\ 
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of s2)) =
  lem_foldl init_st (ops_of s1); 
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))

let merge_inv_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of (inverse_st s2));
  lem_inverse (ops_of lca) (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of (inverse_st s2));
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of (inverse_st s2)) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma 
      (requires is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                ops_of s1 = ops_of lca /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
      (ensures v_of s2 == concrete_merge (v_of lca) (v_of s1) (v_of s2)) =
  ()
  
let linearizable_s2_0 (lca s1 s2:st)
  : Lemma 
      (requires is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                ops_of s2 = ops_of lca /\
                concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
      (ensures v_of s1 == concrete_merge (v_of lca) (v_of s1) (v_of s2)) =
  ()

let linearizable_s2_gt0 (lca s1 s2:st)
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
                   (concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  inverse_helper init_st p2 last2;
  assume (concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2);
  assume (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) \/ e = snd last2);
  assume (forall e. L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2) <==>
               L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) \/ e = snd last2);
  assume (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2));
  ()

let linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     (last (resolve_conflict last1 last2) = last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                           concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                     (last (resolve_conflict last1 last2) <> last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                           concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                      (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1) ==
                       concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                      (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2) ==
                       concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _,last1 = un_snoc (ops_of s1) in
  let p2,last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  linearizable_s2_gt0 lca s1 s2

(*let lem_concrete_do_pre (a b:concrete_st) (op:log_entry)
  : Lemma (requires concrete_do_pre a op /\ (a == b))
          (ensures concrete_do_pre b op) = ()

let lem_do (s a b:concrete_st) (op:log_entry)
  : Lemma (requires (concrete_do_pre a op /\ s == do a op /\ a == b /\ concrete_do_pre b op))
          (ensures s == do b op) = ()*)
          
let convergence1 (lca s1 s2 s1':concrete_st)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures concrete_merge lca s1' s2 == concrete_merge s1 (concrete_merge lca s1 s2) s1') = ()
#pop-options 

