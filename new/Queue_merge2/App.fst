module App

open SeqUtils
#set-options "--query_stats"
// the concrete state type
// It is a sequence of pairs of timestamp and element.
type concrete_st = seq (nat & nat)

// init state
let init_st = empty

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
// (the only operation is write a message)
type app_op_t:eqtype = 
  | Enqueue : nat -> app_op_t
  | Dequeue

type ret_t:eqtype = option (nat * nat)

let get_ele (o:op_t{Enqueue? (fst (snd o))}) : nat =
  match o with
  |(_, (Enqueue x,_)) -> x

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
  match op with
  |(id, (Enqueue x, _)) -> snoc s (id, x)
  |(_, (Dequeue, _)) -> if length s = 0 then s else tail s

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()

let return (s:concrete_st) (o:op_t) : ret_t =
  match o with
  |(_, (Enqueue _, _)) -> None
  |(_, (Dequeue, r)) -> if length s = 0 then None else Some (head s)

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  match x, y with
  |(_,(Enqueue _,_)), (_,(Enqueue _,_)) -> if fst x > fst y then First_then_second else Second_then_first
  |_, (_,(Dequeue,None)) -> Noop_second
  |(_,(Dequeue,None)), _ -> Noop_first
  |(_,(Dequeue,None)), (_,(Dequeue,None)) -> Noop_both
  |(_,(Enqueue _,_)), (_,(Dequeue,Some x)) -> Second_then_first
  |(_,(Dequeue,Some x)), (_,(Enqueue _,_)) -> First_then_second 
  |(_,(Dequeue,Some x)), (_,(Dequeue,Some y)) -> if x = y then First else First_then_second

#push-options "--z3rlimit 50"
let rec concrete_merge1 (l s1 s2:concrete_st) 
  : Pure concrete_st
         (requires true)
         (ensures (fun m -> true))
         (decreases %[length l; length s1; length s2]) =
  match length l, length s1, length s2 with
  |_,0,0 -> empty
  |0,0,_ -> s2
  |0,_,0 -> s1
  |0,_,_ -> if head s1 = head s2 then
              cons (head s1) (concrete_merge1 empty (tail s1) (tail s2))
           else if fst (head s1) > fst (head s2) then
             cons (head s2) (concrete_merge1 l s1 (tail s2))
           else cons (head s1) (concrete_merge1 l (tail s1) s2)
  |_,0,_ -> if fst (head l) < fst (head s2) then
              concrete_merge1 (tail l) s1 s2
           else if head l = head s2 then 
             concrete_merge1 (tail l) s1 (tail s2)
           else empty
  |_,_,0 -> if fst (head l) < fst (head s1) then
              concrete_merge1 (tail l) s1 s2
           else if head l = head s1 then
              concrete_merge1 (tail l) (tail s1) s2
           else empty
  |_,_,_ -> if head l = head s1 && head l = head s2 then
             cons (head l) (concrete_merge1 (tail l) (tail s1) (tail s2))
           else if head l = head s1 && head l <> head s2 then
             concrete_merge1 (tail l) (tail s1) s2
           else if head l = head s2 && head l <> head s1 then
             concrete_merge1 (tail l) s1 (tail s2)  
           else (assert (head l <> head s2 && head l <> head s1);
             concrete_merge1 (tail l) s1 s2)

let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  concrete_merge1 lca s1 s2
  
let rec lem_merge_l_eq_s2 (l s1 s2:concrete_st) 
  : Lemma (requires l == s2)
          (ensures (concrete_merge1 l s1 s2 == s1))
          (decreases %[length l; length s1; length s2]) = 
  match length l, length s1, length s2 with
  |0,0,0 -> lemma_empty s1; lemma_empty s2
  |_,0,0 -> ()
  |0,0,_ -> ()
  |0,_,0 -> ()
  |0,_,_ -> ()
  |_,0,_ -> if fst (head l) < fst (head s2) then ()
           else if  (head l) =  (head s2) then lem_merge_l_eq_s2 (tail l) s1 (tail s2)
           else ()
  |_,_,0 -> ()
  |_,_,_ -> if head l = head s1 && head l = head s2 then
             lem_merge_l_eq_s2 (tail l) (tail s1) (tail s2)
           else if head l = head s1 && head l <> head s2 then ()
           else if head l = head s2 && head l <> head s1 then 
             lem_merge_l_eq_s2 (tail l) s1 (tail s2)
           else if head s1 = head s2 then ()
           else ()

let rec lem_merge_l_eq_s1 (l s1 s2:concrete_st) 
  : Lemma (requires l == s1)
          (ensures (concrete_merge1 l s1 s2 == s2))
          (decreases %[length l; length s1; length s2]) = 
  match length l, length s1, length s2 with
  |0,0,0 -> lemma_empty s2
  |_,0,0 -> ()
  |0,0,_ -> ()
  |0,_,0 -> ()
  |0,_,_ -> ()
  |_,0,_ -> ()
  |_,_,0 -> if fst (head l) < fst (head s1) then ()
           else if head l = head s1 then lem_merge_l_eq_s1 (tail l) (tail s1) s2
           else ()
  |_,_,_ -> if head l = head s1 && head l = head s2 then
             lem_merge_l_eq_s1 (tail l) (tail s1) (tail s2)
           else if head l = head s1 && head l <> head s2 then
             lem_merge_l_eq_s1 (tail l) (tail s1) s2
           else if head l = head s2 && head l <> head s1 then ()
           else if head s1 = head s2 then ()
           else ()

let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0)
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) =
  lem_merge_l_eq_s1 (v_of lca) (v_of s1) (do (v_of s2') last2)

let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    consistent_branches l' s1' s2'' /\
                    is_prefix (ops_of l') (snoc (ops_of s2'') last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) =
  lem_merge_l_eq_s1 (v_of lca) (v_of s1) (do (v_of s2') last2)

let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\

                    (let inv2 = inverse_st s2' in
                    consistent_branches lca s1 inv2 /\
                    is_prefix (ops_of lca) (snoc (ops_of inv2) last2) /\
                    (exists l2. do (v_of inv2) last2 == apply_log (v_of lca) l2) /\
                    (exists l2. do (v_of s2') last2 == apply_log (v_of lca) l2) /\                    
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) =
  lem_merge_l_eq_s1 (v_of lca) (v_of s1) (do (v_of s2') last2)

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires (exists l1. v_of s1 == apply_log (v_of lca) l1) /\
                    (exists l2. v_of s2 == apply_log (v_of lca) l2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = 
  lem_merge_l_eq_s1 (v_of lca) (v_of s1) (v_of s2)

let linearizable_s2_0''_base_base (lca s1' s2:st) (last1:op_t)
  : Lemma (requires consistent_branches lca s1' s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) =
  lem_merge_l_eq_s2 (v_of lca) (do (v_of s1') last1) (v_of s2)

let linearizable_s2_0''_base_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires consistent_branches lca s1' s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    length (ops_of lca) > 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let l' = inverse_st lca in
                    let s1'' = inverse_st s1' in
                    let s2' = inverse_st s2 in
                    consistent_branches l' s1'' s2' /\
                    is_prefix (ops_of l') (snoc (ops_of s1'') last1) /\
                    ops_of s1'' = ops_of l' /\ ops_of s2' = ops_of l' /\
                    eq (do (v_of s1'') last1) (concrete_merge (v_of l') (do (v_of s1'') last1) (v_of s2'))))

          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) =
  lem_merge_l_eq_s2 (v_of lca) (do (v_of s1') last1) (v_of s2)

let linearizable_s2_0''_ind (lca s1' s2:st) (last1:op_t)
  : Lemma (requires consistent_branches_s1_gt0 lca s1' s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s2 = ops_of lca /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\

                    (let inv1 = inverse_st s1' in
                    consistent_branches lca inv1 s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of inv1) last1) /\
                    (exists l1. (do (v_of inv1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l1. (do (v_of s1') last1 == apply_log (v_of lca) l1)) /\
                    eq (do (v_of inv1) last1) (concrete_merge (v_of lca) (do (v_of inv1) last1) (v_of s2))))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) =
  lem_merge_l_eq_s2 (v_of lca) (do (v_of s1') last1) (v_of s2)

let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)))
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second_then_first? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = admit()               

let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (let s2' = inverse_st s2 in
                    (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2)) /\
                    (exists l2. (v_of s2' == apply_log (v_of lca) l2)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    consistent_branches lca s1 s2'))
       
          (ensures (let s2' = inverse_st s2 in
                   ((First_then_second? (resolve_conflict last1 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = admit()
                       
let linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches_s1_gt0 lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (let s1' = inverse_st s1 in
                    (exists l1. (do (v_of s1') last1 == apply_log (v_of lca) l1)) /\
                    (exists l1. (v_of s1' == apply_log (v_of lca) l1)) /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    consistent_branches lca s1' s2))
        
          (ensures (let s1' = inverse_st s1 in
                   ((ops_of s2 = ops_of lca /\
                   First_then_second? (resolve_conflict last1 last2) /\
                   eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   ((Second_then_first? (resolve_conflict last1 last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = admit()

let linearizable_gt0_s1's2' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     First? (resolve_conflict last1 last2) /\
                     (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                     (exists l1. (v_of (inverse_st s1) == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of (inverse_st s2) == apply_log (v_of lca) l2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2))) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = admit()
                      
let linearizable_gt0_s1'_noop (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Noop_first? (resolve_conflict last1 last2) /\
                     (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                     (exists l1. (v_of (inverse_st s1) == apply_log (v_of lca) l1)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures eq (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2))
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = 
  lem_apply_log init_st (ops_of s1);
  lem_apply_log init_st (ops_of s2)

let linearizable_gt0_s2'_noop (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Noop_second? (resolve_conflict last1 last2) /\
                     (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                     (exists l2. (v_of (inverse_st s2) == apply_log (v_of lca) l2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2))))
          (ensures eq (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2)))
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2))) =
  lem_apply_log init_st (ops_of s2)
                      
let linearizable_gt0_s1's2'_noop_both (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Noop_both? (resolve_conflict last1 last2) /\
                     (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                     (exists l1. (v_of (inverse_st s1) == apply_log (v_of lca) l1)) /\
                     (exists l2. (v_of (inverse_st s2) == apply_log (v_of lca) l2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1))))
          (ensures eq (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of (inverse_st s2)))
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = 
  lem_apply_log init_st (ops_of s1)

//////////////////////////////////////////////////////////////

let rec lem_merge_deq_l0 (l s1 s2:concrete_st)
  : Lemma (requires true)
          (ensures ((length s1 > 0 /\ length s2 > 0 /\ length l = 0 /\ head s1 = head s2) ==>
                        ((length (concrete_merge1 l s1 s2) > 0 /\
                         (tail (concrete_merge1 l s1 s2) == concrete_merge1 l (tail s1) (tail s2))))))
          (decreases %[length l; length s1; length s2]) = 
  match length l, length s1, length s2 with
  |_,0,0 -> ()
  |0,0,_ -> ()
  |0,_,0 -> ()
  |0,_,_ -> lemma_empty l; if head s1 = head s2 then
             (assert (concrete_merge1 l s1 s2 ==
                      cons (head s1) (concrete_merge1 empty (tail s1) (tail s2))); 
              lemma_tl (head s1) (concrete_merge1 empty (tail s1) (tail s2));
              assert (tail (concrete_merge1 l s1 s2) == concrete_merge1 empty (tail s1) (tail s2)); ())
           else if fst (head s1) > fst (head s2) then
              lem_merge_deq_l0 l s1 (tail s2)
           else lem_merge_deq_l0 l (tail s1) s2
  |_,0,_ -> ()
  |_,_,0 -> ()
  |_,_,_ -> ()

let lem_merge_deq_l_gt0 (l s1 s2:concrete_st)
  : Lemma (requires true)
          (ensures ((length s1 > 0 /\ length s2 > 0 /\ length l > 0 /\ head s1 = head s2 /\ head l = head s1 /\
                     length (tail s1) > 0 /\ length (tail s2) > 0 /\
                     head l <> head (tail s1) /\ head l <> head (tail s2)) ==>
                        ((length (concrete_merge1 l s1 s2) > 0 /\
                         (tail (concrete_merge1 l s1 s2) == concrete_merge1 l (tail s1) (tail s2))))))
          (decreases %[length l; length s1; length s2]) = 
  match length l, length s1, length s2 with
  |_,0,0 -> ()
  |0,0,_ -> ()
  |0,_,0 -> ()
  |0,_,_ -> ()
  |_,0,_ -> ()
  |_,_,0 -> ()
  |_,_,_ -> if head l = head s1 && head l = head s2 then
             (assert (concrete_merge1 l s1 s2 ==
                      cons (head l) (concrete_merge1 (tail l) (tail s1) (tail s2))); 
              lemma_tl (head l) (concrete_merge1 (tail l) (tail s1) (tail s2));
              assert (length (concrete_merge1 l s1 s2) > 0);
              assert (tail (concrete_merge1 l s1 s2) == concrete_merge1 (tail l) (tail s1) (tail s2)); 
              ())
           else if head l = head s1 && head l <> head s2 then ()
           else if head l = head s2 && head l <> head s1 then ()  
           else ()

let rec lem_merge_deq_l_gt0_hd_neq (l s1 s2:concrete_st)
  : Lemma (requires true)
          (ensures ((length s1 > 0 /\ length s2 > 0 /\ length l > 0 /\ head s1 = head s2 /\ head l <> head s1 /\
                     length (tail s1) > 0 /\ length (tail s2) > 0 /\
                     mem (head s1) (tail l) /\
                     not (mem (head l) s1) /\ not (mem (head l) s2)) ==>
                     //head l <> head (tail s1) /\ head l <> head (tail s2)) ==>
                        ((length (concrete_merge1 l s1 s2) > 0 /\
                         (tail (concrete_merge1 l s1 s2) == concrete_merge1 l (tail s1) (tail s2))))))
          (decreases %[length l; length s1; length s2]) = 
  match length l, length s1, length s2 with
  |_,0,0 -> ()
  |0,0,_ -> ()
  |0,_,0 -> ()
  |0,_,_ -> ()
  |_,0,_ -> ()
  |_,_,0 -> ()
  |_,_,_ -> if head l = head s1 && head l = head s2 then ()
           else if head l = head s1 && head l <> head s2 then ()
           else if head l = head s2 && head l <> head s1 then ()          
           else if head s1 = head s2 && head l <> head s1 then 
             admit() //lem_merge_deq_l_gt0_hd_neq (tail l) s1 s2
           else ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = seq nat

// init state 
let init_st_s = empty

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = 
  match op with
  |(id, (Enqueue x, _)) -> snoc s x
  |(_, (Dequeue, _)) -> if length s = 0 then s else tail s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  length st_s = length st /\
  (forall (i:nat). i < length st_s ==> index st_s i == snd (index st i))

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) =
  if Enqueue? (fst (snd op)) then () else ()
  
////////////////////////////////////////////////////////////////


(*
let rec concrete_merge1 (l s1 s2:concrete_st) 
  : Pure concrete_st
         (requires true)
         (ensures (fun m -> true))
         (decreases %[length l; length s1; length s2]) =
  match length l, length s1, length s2 with
  |_,0,0 -> empty
  |0,0,_ -> s2
  |0,_,0 -> s1
  |0,_,_ -> if fst (head s1) = fst (head s2) then
              concrete_merge1 l (tail s1) (tail s2)
           else if fst (head s1) > fst (head s2) then
             cons (head s2) (concrete_merge1 l s1 (tail s2))
           else cons (head s1) (concrete_merge1 l (tail s1) s2)
  |_,0,_ -> if fst (head l) < fst (head s2) then
              concrete_merge1 (tail l) s1 s2
           else if fst (head l) = fst (head s2) then 
             concrete_merge1 (tail l) s1 (tail s2)
           else empty
  |_,_,0 -> if fst (head l) < fst (head s1) then
              concrete_merge1 (tail l) s1 s2
           else if fst (head l) = fst (head s1) then
              concrete_merge1 (tail l) (tail s1) s2
           else empty
  |_,_,_ -> if fst (head l) = fst (head s1) && fst (head l) = fst (head s2) then
             cons (head l) (concrete_merge1 (tail l) (tail s1) (tail s2))
           else if fst (head l) = fst (head s1) && fst (head l) <> fst (head s2) then
             concrete_merge1 (tail l) (tail s1) s2
           else if fst (head l) = fst (head s2) && fst (head l) <> fst (head s1) then
             concrete_merge1 (tail l) s1 (tail s2)
           else (assert (fst (head l) <> fst (head s2) && fst (head l) <> fst (head s1));
             concrete_merge1 (tail l) s1 s2)
#pop-options

let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  concrete_merge1 lca s1 s2

let rec lem_merge1 (l s1 s2:concrete_st) 
  : Lemma (requires (forall e e1. mem e l /\ mem e1 s1 /\ fst e = fst e1 ==> e = e1) /\
                    (forall e e2. mem e l /\ mem e2 s2 /\ fst e = fst e2 ==> e = e2) /\
                    l == s2)
          (ensures (concrete_merge1 l s1 s2 == s1))
          (decreases %[length l; length s1; length s2]) = 
  match length l, length s1, length s2 with
  |0,0,0 -> lemma_empty s1; lemma_empty s2
  |_,0,0 -> ()
  |0,0,_ -> ()
  |0,_,0 -> ()
  |0,_,_ -> if fst (head s1) = fst (head s2) then
              lem_merge1 (tail l) (tail s1) (tail s2)
           else if fst (head s1) > fst (head s2) then
              lem_merge1 (tail l) s1 (tail s2)
           else lem_merge1 l (tail s1) s2
  |_,0,_ -> if fst (head l) < fst (head s2) then
              lem_merge1 (tail l) s1 (tail s2)
           else if fst (head l) = fst (head s2) then 
             lem_merge1 (tail l) s1 (tail s2)
           else ()
  |_,_,0 -> if fst (head l) < fst (head s1) then
              lem_merge1 (tail l) s1 (tail s2)
           else if fst (head l) = fst (head s1) then
              lem_merge1 (tail l) (tail s1) (tail s2)
           else ()
  |_,_,_ -> if fst (head l) = fst (head s1) && fst (head l) = fst (head s2) then
             lem_merge1 (tail l) (tail s1) (tail s2)
           else if fst (head l) = fst (head s1) && fst (head l) <> fst (head s2) then
             lem_merge1 (tail l) (tail s1) (tail s2)
           else if fst (head l) = fst (head s2) && fst (head l) <> fst (head s1) then
             lem_merge1 (tail l) s1 (tail s2)
           else lem_merge1 (tail l) s1 (tail s2)

let rec lem_merge2 (l s1 s2:concrete_st) 
  : Lemma (requires (forall e e1. mem e l /\ mem e1 s1 /\ fst e = fst e1 ==> e = e1) /\
                    (forall e e2. mem e l /\ mem e2 s2 /\ fst e = fst e2 ==> e = e2) /\
                    l == s1)
          (ensures (concrete_merge1 l s1 s2 == s2))
          (decreases %[length l; length s1; length s2]) = 
  match length l, length s1, length s2 with
  |0,0,0 -> lemma_empty s1; lemma_empty s2
  |_,0,0 -> ()
  |0,0,_ -> ()
  |0,_,0 -> ()
  |0,_,_ -> if fst (head s1) = fst (head s2) then
             lem_merge2 (tail l) (tail s1) (tail s2)
           else if fst (head s1) > fst (head s2) then
             lem_merge2 l s1 (tail s2)
           else lem_merge2 (tail l) (tail s1) s2
  |_,0,_ -> if fst (head l) < fst (head s2) then
              lem_merge2 (tail l) (tail s1) s2
           else if fst (head l) = fst (head s2) then 
              lem_merge2 (tail l) (tail s1) (tail s2)
           else ()
  |_,_,0 -> if fst (head l) < fst (head s1) then
              lem_merge2 (tail l) (tail s1) s2
           else if fst (head l) = fst (head s1) then
              lem_merge2 (tail l) (tail s1) s2
           else ()
  |_,_,_ -> if fst (head l) = fst (head s1) && fst (head l) = fst (head s2) then
             lem_merge2 (tail l) (tail s1) (tail s2)
           else if fst (head l) = fst (head s1) && fst (head l) <> fst (head s2) then
             lem_merge2 (tail l) (tail s1) s2
           else if fst (head l) = fst (head s2) && fst (head l) <> fst (head s1) then
             lem_merge2 (tail l) (tail s1) (tail s2)
           else (assert (fst (head l) <> fst (head s2) && fst (head l) <> fst (head s1));
             lem_merge2 (tail l) (tail s1) s2)

let rec lem_merge3 (l s1 s2:concrete_st) 
  : Lemma (requires //(forall e e1. mem e l /\ mem e1 s1 /\ fst e = fst e1 ==> e = e1) /\
                    //(forall e e2. mem e l /\ mem e2 s2 /\ fst e = fst e2 ==> e = e2) /\
                    unique_st l /\ unique_st s1 /\ unique_st s2 )
          (ensures (length l > 0 /\ s1 = tail l /\ s2 = tail l /\ s1 = s2) ==> (concrete_merge1 l s1 s2 = tail l))
          (decreases %[length l; length s1; length s2]) = 
  match length l, length s1, length s2 with
  |0,0,0 -> ()
  |_,0,0 -> ()
  |0,0,_ -> ()
  |0,_,0 -> ()
  |0,_,_ -> ()
  |_,0,_ -> ()
  |_,_,0 -> ()
  |_,_,_ -> if fst (head l) = fst (head s1) && fst (head l) = fst (head s2) then
             (mem_cons (head l) (tail l);
              distinct_invert_append (create 1 (head l)) (tail l))
           else if fst (head l) = fst (head s1) && fst (head l) <> fst (head s2) then ()
           else if fst (head l) = fst (head s2) && fst (head l) <> fst (head s1) then ()
           else
             (if s1 = tail l && s2 = tail l && s1 = s2 then 
               (lemma_append_count_assoc_fst (create 1 (head l)) (tail l);
                lem_merge3 (tail l) (tail s1) (tail s2))
             else ())


(*let rec sorted_union (l1 l2:concrete_st) 
  : Tot (u:concrete_st{(l1 == empty /\ l2 == empty ==> u == empty) /\
                       (l1 == empty ==> u == l2) /\
                       (l2 == empty ==> u == l1)})
  (decreases %[length l1; length l2]) =
  match length l1, length l2 with
  |0,0 -> lemma_empty l1; lemma_empty l2; empty
  |0,_ -> l2
  |_,0 -> l1
  |_,_ -> if fst (head l1) < fst (head l2) then
            cons (head l1) (sorted_union (tail l1) l2)
         else cons (head l2) (sorted_union l1 (tail l2))*)


  (*match length a, length l with
  |0,_ -> append_empty_l a; lemma_empty a; empty
  |_,0 -> append_empty_l a; assert (a == Seq.append empty a); a
  |_,_ -> if is_prefix_s l a then diff a l 
         else if fst (head l) < fst (head a) then
            (diff_s a (tail l))
         else (diff_s (tail a) (tail l))*)

let rec lem_diff_s1 (a l:concrete_st)
  : Lemma (ensures ((length a > 0 /\ not (mem_id_s (fst (last a)) l)) ==> 
                            (length (diff_s a l) > 0 /\ last (diff_s a l) = last a)) )
  (decreases %[length a; length l]) =
  lem_diff_s a l;
  match length a, length l with
  |0,_ -> append_empty_l a; lemma_empty a; ()
  |_,0 -> append_empty_l a; assert (a == Seq.append empty a);
         assert (length a > 0 ==> last a = last (diff_s a l)); ()
  |_,_ -> if fst (head l) < fst (head a) then
            (lem_diff_s1 a (tail l))
         else (admit();lem_diff_s1 (tail a) (tail l))
         
(*let rec lem_diff (a l:concrete_st)
  : Lemma (ensures is_prefix l a ==> a == Seq.append l (diff_s a l))
  (decreases %[length a; length l]) =
  match length a, length l with
  |0,_ -> ()
  |_,0 -> ()
  |_,_ -> if head l = head a then
            lem_diff (tail a) (tail l)
         else if fst (head l) < fst (head a) then
            lem_diff a (tail l)
         else lem_diff (tail a) (tail l) *) 

 let rec merge_pre (lca:st)
  : Lemma (requires true)
          (ensures (forall e e1. mem e (v_of lca) /\ mem e1 (v_of lca) /\ fst e = fst e1 ==> e = e1))
          (decreases %[length (ops_of lca)]) = admit();
  let l = ops_of lca in
  match length (ops_of lca) with
  |0 -> ()
  |_ -> merge_pre (inverse_st lca)
  
             *)
