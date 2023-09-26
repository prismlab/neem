module App

//module L = FStar.List.Tot
open List_extended
module L = FStar.List.Tot

// the concrete state type
// It is a sequence of pairs of timestamp and message.
// As the sequence is sorted based on timestamps we ignore the message
type concrete_st = l:list nat{sorted (fun (x y:nat) -> x >= y) l}

// init state
let init_st = []

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  a == b

// few properties of equivalence relation
let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b) = ()

// operation type
// (the only operation is append, so unit is fine)
type app_op_t:eqtype = unit

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : (r:concrete_st{(forall e. L.mem e r <==> L.mem e s \/ e = fst op)}) =
  let l = fst op::s in
  quicksort (fun (x y:nat) -> x >= y) l

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()
           
//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : (l:log{(forall e. mem e l <==> (e == x \/ e == y))}) =
  if lt (fst y) (fst x)
    then cons y (cons x empty)
      else cons x (cons y empty)

let resolve_conflict_prop (x y:op_t)
  : Lemma (requires fst x <> fst y)
          (ensures (lt (fst y) (fst x) <==> last (resolve_conflict x y) = x) /\
                   (last (resolve_conflict x y) <> x <==> lt (fst x) (fst y)))
  = ()

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (forall e. L.mem e s ==> L.mem e (apply_log s l)))
          (decreases length l)
          [SMTPat (apply_log s l)]
  = match length l with
    |0 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

let lem_foldl_forall (s:concrete_st) 
  : Lemma (ensures (forall l. (forall e. L.mem e s ==> L.mem e (apply_log s l)))) = ()

let filter (a:concrete_st) (f:nat -> bool) : (r:concrete_st{(forall e. L.mem e r <==> L.mem e a /\ f e)}) = admit()

#push-options "--z3rlimit 50"
let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun m -> (forall e. L.mem e m <==> L.mem e lca \/ L.mem e s1 \/ L.mem e s2))) =
  assert (forall e. L.mem e lca ==> L.mem e s1); 
  assert (forall e. L.mem e lca ==> L.mem e s2);
  let ds1 = filter s1 (fun e -> not (L.mem e lca)) in
  let ds2 = filter s2 (fun e -> not (L.mem e lca)) in
  assert (forall e. L.mem e ds1 <==> L.mem e s1 /\ not (L.mem e lca));
  assert (forall e. L.mem e ds2 <==> L.mem e s2 /\ not (L.mem e lca));
  let l = L.append ds1 ds2 in 
  let l1 = quicksort (fun (x y:nat) -> x >= y) l in 
  assume (forall e. L.mem e l1 <==> L.mem e l);
  L.append l1 lca

let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

#push-options "--z3rlimit 50"
let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    is_prefix (ops_of l') (ops_of s1') /\ 
                    is_prefix (ops_of l') (ops_of s2'') /\
                    is_prefix (ops_of l') (snoc (ops_of s2'') last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s1') (ops_of l')) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s2'') (ops_of l')) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of l')) ==> not (mem_id id (diff (ops_of s2'') (ops_of l')))) /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()
#pop-options

let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 == ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let inv2 = inverse_st s2' in
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    is_prefix (ops_of lca) (snoc (ops_of inv2) last2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca)))) /\
                    (exists l2. do (v_of inv2) last2 == apply_log (v_of lca) l2) /\
                    (exists l2. do (v_of s2') last2 == apply_log (v_of lca) l2) /\  
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (exists l2. (v_of s2) == apply_log (v_of lca) l2) /\
                    (exists l1. (v_of s1) == apply_log (v_of lca) l1))
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_s2_0''_base_base (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' == ops_of lca /\ ops_of s2 == ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()

#push-options "--z3rlimit 50"
let linearizable_s2_0''_base_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' == ops_of lca /\ ops_of s2 == ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let l' = inverse_st lca in
                    let s1'' = inverse_st s1' in
                    let s2' = inverse_st s2 in
                    is_prefix (ops_of l') (ops_of s1'') /\ 
                    is_prefix (ops_of l') (ops_of s2') /\
                    is_prefix (ops_of l') (snoc (ops_of s1'') last1) /\
                    ops_of s1'' = ops_of l' /\ ops_of s2' = ops_of l' /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s1'') (ops_of l')) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s2') (ops_of l')) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1'') (ops_of l')) ==> not (mem_id id (diff (ops_of s2') (ops_of l')))) /\
                    eq (do (v_of s1'') last1) (concrete_merge (v_of l') (do (v_of s1'') last1) (v_of s2'))))

          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()
#pop-options

let linearizable_s2_0''_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s2 == ops_of lca /\
                    length (ops_of s1') > length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let inv1 = inverse_st s1' in
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    is_prefix (ops_of lca) (snoc (ops_of inv1) last1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (exists l1. (do (v_of inv1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l1. (do (v_of s1') last1 == apply_log (v_of lca) l1)) /\
                    eq (do (v_of inv1) last1) (concrete_merge (v_of lca) (do (v_of inv1) last1) (v_of s2))))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()

#push-options "--z3rlimit 50"
let linearizable_gt0_base_last1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    last (resolve_conflict last1 last2) = last1 /\
                      
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  assert (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 ==
          cons (fst last1) (cons (fst last2) (v_of lca)));
  lemma_mem_append (create 1 (fst last2)) (v_of lca);
  append_assoc (create 1 (fst last1)) (create 1 (fst last2)) (v_of lca);
  assert (cons (fst last1) (cons (fst last2) (v_of lca)) ==
          Seq.append (cons (fst last1) (cons (fst last2) empty)) (v_of lca));
  ()

let linearizable_gt0_base_last2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    last (resolve_conflict last1 last2) <> last1 /\
                      
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
         
          (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  assert (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 ==
          cons (fst last2) (cons (fst last1) (v_of lca)));
  lemma_mem_append (create 1 (fst last1)) (v_of lca);
  append_assoc (create 1 (fst last2)) (create 1 (fst last1)) (v_of lca);
  assert (cons (fst last2) (cons (fst last1) (v_of lca)) ==
          Seq.append (cons (fst last2) (cons (fst last1) empty)) (v_of lca));
  ()
  
let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                      
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
         
          (ensures (last (resolve_conflict last1 last2) = last1 ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (last (resolve_conflict last1 last2) <> last1 ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) =
  if last (resolve_conflict last1 last2) = last1 then
    linearizable_gt0_base_last1 lca s1 s2 last1 last2
  else linearizable_gt0_base_last2 lca s1 s2 last1 last2

(*let lem_last (a:log)
  : Lemma (ensures (length a > 0 ==> 
                      (let _, lst = un_snoc a in 
                       last a == lst))) = ()

let rec lem_help (a a' b l:concrete_st) (op:nat)
  : Lemma (requires (a == cons op a' /\ is_suffix_s l a /\ is_suffix_s l b /\ is_suffix_s l a' /\
                     length b > 0 /\ op > (head b) /\ head a = op /\ head (diff_s a l) = op))
          (ensures (union_s (diff_s a l) (diff_s b l) ==
                    cons op (union_s (diff_s a' l) (diff_s b l))))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> admit()


#push-options "--z3rlimit 100"
let linearizable_gt0_last1 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))) /\
                    (exists l1. (v_of (inverse_st s1)) == apply_log (v_of lca) l1) /\
                    (exists l2. (v_of s2) == apply_log (v_of lca) l2) /\  
                    (exists l1. (v_of s1) == apply_log (v_of lca) l1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in 
  //lem_last (ops_of s1);
  let s1' = inverse_st s1 in
  assert (v_of s1 == cons (fst last1) (v_of s1'));
 // assume (diff_s (v_of s1) (v_of lca) == cons (fst last1) (diff_s (v_of s1') (v_of lca)) );
  assume (head (diff_s (v_of s1) (v_of lca)) = fst last1);
  assume (head (v_of s1) = fst last1);
  assert (union_s (diff_s (v_of s1) (v_of lca)) (diff_s (v_of s2) (v_of lca)) ==
          cons (fst last1) (union_s (diff_s (v_of s1') (v_of lca)) (diff_s (v_of s2) (v_of lca)))); admit();

  assert (concrete_merge (v_of lca) (v_of s1') (v_of s2) ==
          Seq.append (union_s (diff_s (v_of s1') (v_of lca)) (diff_s (v_of s2) (v_of lca))) (v_of lca));

  assert (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last1 ==
          cons (fst last1) (concrete_merge (v_of lca) (v_of s1') (v_of s2)));
  append_assoc (create 1 (fst last1)) (union_s (diff_s (v_of s1') (v_of lca)) (diff_s (v_of s2) (v_of lca))) (v_of lca);
  
  assert (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last1 ==
          Seq.append (cons (fst last1) (union_s (diff_s (v_of s1') (v_of lca)) (diff_s (v_of s2) (v_of lca)))) 
                     (v_of lca));
  assert (concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
          Seq.append (union_s (diff_s (v_of s1) (v_of lca)) (diff_s (v_of s2) (v_of lca))) (v_of lca));
  ()*)
                        
#push-options "--z3rlimit 100"
let rec linearizable_gt0_ind_last1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (let s2' = inverse_st s2 in
                    (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2)) /\
                    (exists l2. (v_of s2' == apply_log (v_of lca) l2)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)) /\
                      
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca))))))
       
          (ensures (forall e. mem e (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1) ==>
                         mem e (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))
                        
          (*ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))*) 
          (decreases length (ops_of s1)) =()


let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (let s2' = inverse_st s2 in
                    (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2)) /\
                    (exists l2. (v_of s2' == apply_log (v_of lca) l2)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                      
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca))))))
       
          (ensures (let s2' = inverse_st s2 in
                   ((last (resolve_conflict last1 last2) = last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()

let linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (let s1' = inverse_st s1 in
                    (exists l1. (do (v_of s1') last1 == apply_log (v_of lca) l1)) /\
                    (exists l1. (v_of s1' == apply_log (v_of lca) l1)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                   
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))))
        
          (ensures (let s1' = inverse_st s1 in
                   ((ops_of s2 = ops_of lca /\
                   last (resolve_conflict last1 last2) = last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   ((last (resolve_conflict last1 last2) <> last1 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()









let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    is_prefix (ops_of l') (ops_of s1') /\ 
                    is_prefix (ops_of l') (ops_of s2'') /\
                    is_prefix (ops_of l') (snoc (ops_of s2'') last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s1') (ops_of l')) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s2'') (ops_of l')) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of l')) ==> not (mem_id id (diff (ops_of s2'') (ops_of l')))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    concrete_merge_pre (v_of l') (v_of s1') (do (v_of s2'') last2) /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()
          
let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 == ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let inv2 = inverse_st s2' in
                    is_prefix (ops_of lca) (ops_of inv2) /\
                    is_prefix (ops_of lca) (snoc (ops_of inv2) last2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of inv2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of inv2) last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()
          
let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_s2_0''_base_pre (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' == ops_of lca /\ ops_of s2 == ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    length (ops_of lca) > 0)
         
          (ensures (let l' = inverse_st lca in
                    let s1'' = inverse_st s1' in
                    let s2' = inverse_st s2 in
                    concrete_merge_pre (v_of l') (do (v_of s1'') last1) (v_of s2'))) = ()

let linearizable_s2_0''_base_base (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' == ops_of lca /\ ops_of s2 == ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()

#push-options "--z3rlimit 50"
let linearizable_s2_0''_pre (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s2 == ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    length (ops_of s1') > length (ops_of lca))
         
          (ensures (let inv1 = inverse_st s1' in
                    concrete_merge_pre (v_of lca) (do (v_of inv1) last1) (v_of s2))) = admit()

let linearizable_s2_0''_base_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' == ops_of lca /\ ops_of s2 == ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let l' = inverse_st lca in
                    let s1'' = inverse_st s1' in
                    let s2' = inverse_st s2 in
                    is_prefix (ops_of l') (ops_of s1'') /\ 
                    is_prefix (ops_of l') (ops_of s2') /\
                    is_prefix (ops_of l') (snoc (ops_of s1'') last1) /\
                    ops_of s1'' = ops_of l' /\ ops_of s2' = ops_of l' /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s1'') (ops_of l')) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of l') /\ mem_id id1 (diff (ops_of s2') (ops_of l')) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1'') (ops_of l')) ==> not (mem_id id (diff (ops_of s2') (ops_of l')))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    concrete_merge_pre (v_of l') (do (v_of s1'') last1) (v_of s2') /\
                    eq (do (v_of s1'') last1) (concrete_merge (v_of l') (do (v_of s1'') last1) (v_of s2'))))

          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()
          
let linearizable_s2_0''_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1') /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s2 == ops_of lca /\
                    length (ops_of s1') > length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let inv1 = inverse_st s1' in
                    is_prefix (ops_of lca) (ops_of inv1) /\
                    is_prefix (ops_of lca) (snoc (ops_of inv1) last1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of inv1) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of inv1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (do (v_of inv1) last1) (v_of s2) /\
                    eq (do (v_of inv1) last1) (concrete_merge (v_of lca) (do (v_of inv1) last1) (v_of s2))))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()

let linearizable_gt0_s2'_s10_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 == ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    length (ops_of s2) > length (ops_of lca))
         
          (ensures (let s2' = inverse_st s2 in
                   concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                   concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2'))) = admit()

let linearizable_gt0_s2'_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\ 
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca))
         
          (ensures (let s1' = inverse_st s1 in
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2))) = admit()

let linearizable_gt0_s1'_s20_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 == ops_of lca /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    length (ops_of s1) > length (ops_of lca))
        
          (ensures (let s1' = inverse_st s1 in
                    concrete_merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1') (do (v_of s2) last2))) = admit()

let linearizable_gt0_s1'_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) = last1 /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    length (ops_of s2) > length (ops_of lca))
       
          (ensures (let s2' = inverse_st s2 in
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))) = admit()

let union_single (a b:concrete_st) (op1 op2:nat)
  : Lemma (requires a == cons op1 empty /\
                    b == cons op2 empty /\
                    op1 > op2)
          (ensures union_s a b == cons op1 (cons op2 empty)) = ()

let lem_app (op1 op2:nat) (a:concrete_st)
  : Lemma (ensures Seq.append (cons op1 (cons op2 empty)) a ==
                   (cons op1 (cons op2 a))) = admit()
                   
let linearizable_gt0_base_last1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    last (resolve_conflict last1 last2) = last1 /\
                    concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                      
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = 
  assert (fst last1 > fst last2);
  assert (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 =
         (cons (fst last1) (cons (fst last2) (v_of lca))));
  assert ((do (v_of s1) last1) = cons (fst last1) (v_of lca));
  let s = fst (split (cons (fst last1) (v_of lca)) (length (cons (fst last1) (v_of lca)) - length (v_of lca))) in
  lemma_split (cons (fst last1) (v_of lca)) (length (cons (fst last1) (v_of lca)) - length (v_of lca));
  lemma_mem_append s (v_of lca);
  assert (diff_s (cons (fst last1) (v_of lca)) (v_of lca) == cons (fst last1) empty);
  assert ((do (v_of s2) last2) = cons (fst last2) (v_of lca));
  let s = fst (split (cons (fst last2) (v_of lca)) (length (cons (fst last2) (v_of lca)) - length (v_of lca))) in
  lemma_split (cons (fst last2) (v_of lca)) (length (cons (fst last2) (v_of lca)) - length (v_of lca));
  lemma_mem_append s (v_of lca);
  assert (diff_s (cons (fst last2) (v_of lca)) (v_of lca) == cons (fst last2) empty); 
  union_single (cons (fst last1) empty) (cons (fst last2) empty) (fst last1) (fst last2);
  let u = union_s (cons (fst last1) empty) (cons (fst last2) empty) in
  lem_app (fst last1) (fst last2) (v_of lca);
  assert (Seq.append u (v_of lca) == (cons (fst last1) (cons (fst last2) (v_of lca)))); 
  assert (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) ==
          (cons (fst last1) (cons (fst last2) (v_of lca)))); ()

let linearizable_gt0_base_last2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                      
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
         
          (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) = 
  assert (fst last1 < fst last2);
  assert (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 =
         (cons (fst last2) (cons (fst last1) (v_of lca))));
  assert ((do (v_of s1) last1) = cons (fst last1) (v_of lca));
  let s = fst (split (cons (fst last1) (v_of lca)) (length (cons (fst last1) (v_of lca)) - length (v_of lca))) in
  lemma_split (cons (fst last1) (v_of lca)) (length (cons (fst last1) (v_of lca)) - length (v_of lca));
  lemma_mem_append s (v_of lca);
  assert (diff_s (cons (fst last1) (v_of lca)) (v_of lca) == cons (fst last1) empty);
  assert ((do (v_of s2) last2) = cons (fst last2) (v_of lca));
  let s = fst (split (cons (fst last2) (v_of lca)) (length (cons (fst last2) (v_of lca)) - length (v_of lca))) in
  lemma_split (cons (fst last2) (v_of lca)) (length (cons (fst last2) (v_of lca)) - length (v_of lca));
  lemma_mem_append s (v_of lca);
  assert (diff_s (cons (fst last2) (v_of lca)) (v_of lca) == cons (fst last2) empty); 
  
  union_single (cons (fst last2) empty) (cons (fst last1) empty) (fst last2) (fst last1);
  let u = union_s (cons (fst last2) empty) (cons (fst last1) empty) in
  lem_app (fst last2) (fst last1) (v_of lca);
  assert (Seq.append u (v_of lca) == (cons (fst last2) (cons (fst last1) (v_of lca)))); 
  assert (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) ==
          (cons (fst last2) (cons (fst last1) (v_of lca)))); ()
          
let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2)) /\
                
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2)) /\
                      
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
         
          (ensures (last (resolve_conflict last1 last2) = last1 ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (last (resolve_conflict last1 last2) <> last1 ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = 
  if last (resolve_conflict last1 last2) = last1
    then linearizable_gt0_base_last1 lca s1 s2 last1 last2
  else linearizable_gt0_base_last2 lca s1 s2 last1 last2

#push-options "--z3rlimit 100"
let rec trial (s2'':concrete_st) (l1 l2 l2':nat)
  : Lemma (requires (cons l2 (union_s (cons l1 empty) s2'') ==
                     union_s (cons l1 empty) (cons l2 s2'')))
          (ensures (cons l2 (union_s (cons l1 empty) (cons l2' s2'')) ==
                    union_s (cons l1 empty) (cons l2 (cons l2' s2''))))
          (decreases length s2'') =
  if length s2'' = 0
    then ()
  else admit()

#push-options "--z3rlimit 100"
let rec linearizable_gt0_ind_last2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
          
                    (let s2' = inverse_st s2 in
                    last (resolve_conflict last1 last2) <> last1 /\
                    ops_of s1 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2') /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)) /\
                      
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca))))))
       
          (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) 
          (decreases %[length (ops_of lca); length (ops_of s1)]) = 
  if length (ops_of lca) = 0 
    then (assume (v_of lca == empty /\ v_of s1 == empty); admit())
  else (let lca' = inverse_st lca in
        let s1' = inverse_st s1 in 
        assume (is_prefix (ops_of lca') (ops_of s1') /\
                    is_prefix (ops_of lca') (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca') /\
                   
                    concrete_merge_pre (v_of lca') (do (v_of s1') last1) (do (v_of s2) last2) /\
                    (forall id id1. mem_id id (ops_of lca') /\ mem_id id1 (diff (ops_of s1') (ops_of lca')) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca') /\ mem_id id1 (diff (ops_of s2) (ops_of lca')) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca')) ==> not (mem_id id (diff (ops_of s2) (ops_of lca')))) /\
          
                    (let s2' = inverse_st s2 in
                    ops_of s1' = ops_of lca' /\
                    concrete_merge_pre (v_of lca') (do (v_of s1') last1) (v_of s2') /\
                    concrete_merge_pre (v_of lca') (do (v_of s1') last1) (do (v_of s2') last2) /\
                    concrete_merge_pre (v_of lca') (do (v_of s1') last1) (v_of s2) /\
                    eq (do (concrete_merge (v_of lca') (do (v_of s1') last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca') (do (v_of s1') last1) (do (v_of s2') last2)) /\
                      
                    is_prefix (ops_of lca') (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca') /\ mem_id id1 (diff (ops_of s2') (ops_of lca')) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca')) ==> not (mem_id id (diff (ops_of s2') (ops_of lca'))))));
        linearizable_gt0_ind_last2 lca' s1' s2 last1 last2;
        ())
                       
                        
let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
          
                    (let s2' = inverse_st s2 in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                      concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2)) /\
                   
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2') /\
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2)) /\
                      
                     is_prefix (ops_of lca) (ops_of s2') /\
                     (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                     (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca))))))
       
          (ensures (let s2' = inverse_st s2 in
                   (last (resolve_conflict last1 last2) = last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)) ==>
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   (ops_of s1 = ops_of lca /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)) ==>
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = admit ()

let linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    concrete_merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\

                    (let s1' = inverse_st s1 in
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                      concrete_merge_pre (v_of lca) (v_of s1') (do (v_of s2) last2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) /\
                   
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                      concrete_merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) /\
                   
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))))
        
          (ensures (let s1' = inverse_st s1 in
                   (ops_of s2 = ops_of lca /\
                   last (resolve_conflict last1 last2) = last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   (last (resolve_conflict last1 last2) <> last1 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = admit ()
                       
let linearizable_gt0_merge_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    last1 == last (ops_of s1) /\
                    last2 == last (ops_of s2) /\             
                    fst last1 <> fst last2 /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2))
       
          (ensures (last (resolve_conflict last1 last2) = last1 ==>
                       concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\

                   (last (resolve_conflict last1 last2) <> last1 ==>
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))) = admit()
  
                       
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = seq nat

// init state 
let init_st_s = empty

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = cons (fst op) s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) 
  = ()

////////////////////////////////////////////////////////////////
