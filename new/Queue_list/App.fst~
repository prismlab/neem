module App

open SeqUtils
#set-options "--query_stats"
// the concrete state type
// It is a sequence of pairs of timestamp and element.
type concrete_st = seq (pos & nat)

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

type ret_t:eqtype = option (pos * nat)

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

let rec intersection (l a b:concrete_st) 
  : Tot (i:concrete_st{((l == a /\ l == b) ==> i == l) /\
                        (l == a /\ is_prefix l b ==> i == l) /\
                        (l == b /\ is_prefix l a ==> i == l) /\
                        (length l > 0 /\ length a > 0 /\ length b > 0 /\ head l = head a /\ head l = head b ==>
                         length i > 0 /\ head i = head l)})
  (decreases %[length l; length a; length b]) =
  match length l, length a, length b with
  |0,_,_ |_,0,_ |_,_,0 -> empty
  |_,_,_ -> if head l = head a && head l = head b then
             cons (head l) (intersection (tail l) (tail a) (tail b))
           else if head l = head a then
             intersection (tail l) (tail a) b
           else if head l = head b then
             intersection (tail l) a (tail b)
           else intersection (tail l) a b

let rec lem_inter (l a b:concrete_st) 
  : Lemma (ensures ((length l > 0 /\ a = tail l /\ b = tail l /\
                   ((length a > 0 ==> fst (head a) <> fst (head l)) \/
                     length a = 0) /\
                   ((length b > 0 ==> fst (head b) <> fst (head l)) \/
                     length b = 0))
                     ==> intersection l a b == tail l))
          (decreases %[length l]) =
  match length l, length a, length b with
  |0,_,_ |_,0,_ |_,_,0 -> ()
  |_,_,_ -> if head l = head a && head l = head b then
             (lem_inter (tail l) (tail a) (tail b))
           else if head l = head a then
             lem_inter (tail l) (tail a) b
           else if head l = head b then
             lem_inter (tail l) a (tail b)
           else lem_inter (tail l) a b

let rec lem_inter_tail (l a b:concrete_st) 
  : Lemma (ensures ((length l > 0 /\ ((a = l /\ b = tail l) \/ (b = l /\ a = tail l))) ==> 
                            (intersection l a b == tail l)))
          (decreases %[length l]) =
  match length l, length a, length b with
  |0,_,_ |_,0,_ |_,_,0 -> ()
  |_,_,_ -> if (head l = head a && head l = head b) then
              lem_inter_tail (tail l) (tail a) (tail b)
           else lem_inter_tail (tail l) a b

let rec diff_s (a:concrete_st) (l:concrete_st)
  : Tot (d:concrete_st{(a == l ==> d = empty)  /\
                       (is_suffix a l ==> d == empty)})
        (decreases %[length a; length l]) =
  match length a, length l with
  |0,_ -> append_empty_l a; lemma_empty a; empty
  |_,0 -> append_empty_l a; assert (a == Seq.append empty a); a
  |_,_ -> if (head l) <> (head a) then
            (diff_s a (tail l))
         else (assert (head l = head a); 
               diff_s (tail a) (tail l))
 
let rec lem_diff_s (a l:concrete_st)
  : Lemma (requires true)
          (ensures (is_prefix l a ==> (is_suffix (diff_s a l) a /\ diff_s a l = diff a l /\ a == Seq.append l (diff_s a l))))
          (decreases %[length a; length l]) =
         // [SMTPat (is_prefix l a)]  =
   match length a, length l with
  |0,_ -> append_empty_l a; lemma_empty a; ()
  |_,0 -> append_empty_l a; assert (a == Seq.append empty a);
         assert (length a > 0 ==> last a = last (diff_s a l)); ()
  |_,_ -> if (head l) <> (head a) then
            (lem_diff_s a (tail l))
         else (lem_diff_s (tail a) (tail l))
         
let rec sorted_union (l1 l2:concrete_st) 
  : Tot (u:concrete_st{(l1 == empty /\ l2 == empty ==> u == empty) /\
                       (l1 == empty ==> u == l2) /\
                       (l2 == empty ==> u == l1) /\
                       (length l1 > 0 /\ length l2 > 0 /\ fst (last l1) > fst (last l2) ==> length u > 0 /\ last u = last l1) /\
                       (forall e. mem e u <==> mem e l1 \/ mem e l2)})
  (decreases %[length l1; length l2]) =
  match length l1, length l2 with
  |0,0 -> lemma_empty l1; lemma_empty l2; empty
  |0,_ -> l2
  |_,0 -> l1
  |_,_ -> let pre1, last1 = un_snoc l1 in
         let pre2, last2 = un_snoc l2 in
         lemma_mem_snoc pre1 last1;
         lemma_mem_snoc pre2 last2;
         if fst last1 >= fst last2 then
           (lemma_mem_snoc (sorted_union pre1 l2) last1;
            snoc (sorted_union pre1 l2) last1)
         else (lemma_mem_snoc (sorted_union l1 pre2) last2;
               snoc (sorted_union l1 pre2) last2)
         
let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (length l = 0 ==> (apply_log s l = s)))
          (decreases length l)
  = match length l with
    |0 -> ()
    |1 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  let i = intersection lca s1 s2 in
  let da = diff_s s1 lca in
  let db = diff_s s2 lca in 
  let union_ab = sorted_union da db in
  Seq.append i union_ab

let do_is_unique (s:concrete_st) (op:op_t) 
  : Lemma (requires distinct_assoc_fst s /\ (not (mem_assoc_fst (fst op) s)))
          (ensures distinct_assoc_fst (do s op)) =
  match op with
  |(id, (Enqueue x, _)) -> assert (distinct_assoc_fst s);
                          assert (distinct_assoc_fst (create 1 (fst op, get_ele op)));
                          distinct_append s (create 1 (fst op, get_ele op))
  |(_, (Dequeue, _)) -> if length s = 0 then () 
                          else (mem_cons (head s) (tail s);
                                distinct_invert_append (create 1 (head s)) (tail s))

#push-options "--z3rlimit 50"
let rec lem_foldl1 (s:concrete_st) (l:log)
  : Lemma (requires distinct_assoc_fst s /\ distinct_ops l /\
                    (forall id. mem_assoc_fst id s ==> not (mem_id id l)))
          (ensures distinct_assoc_fst (apply_log s l))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> mem_cons (head l) (tail l);
       distinct_invert_append (create 1 (head l)) (tail l);
       do_is_unique s (head l);
       if Enqueue? (fst (snd (head l))) then 
         (lemma_append_count_assoc_fst s (create 1 (fst (head l), get_ele (head l))))
       else ();
       lem_foldl1 (do s (head l)) (tail l)

let valid_is_unique (s:st0) 
  : Lemma (requires distinct_ops (ops_of s) /\ v_of s == apply_log init_st (ops_of s))
          (ensures distinct_assoc_fst (v_of s)) =
  lem_foldl1 init_st (ops_of s)

let last_deq (s:concrete_st) (op:op_t)
  : Lemma (requires Dequeue? (fst (snd op)) /\ Some? (ret_of op) /\ return s op == ret_of op)
          (ensures length s > 0 /\ Some (head s) == ret_of op) = ()

let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0)
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = 
  lem_diff_s (do (v_of s2') last2) (v_of lca)

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
  if Enqueue? (fst (snd last2)) then
     lem_diff_s (do (v_of s2') last2) (v_of lca)
  else (let i = intersection (v_of lca) (v_of s1) (do (v_of s2') last2) in
            (*let da = diff_s (v_of s1) (v_of lca) in
              let db = diff_s (do (v_of s2') last2) (v_of lca) in 
              let union_ab = sorted_union da db in
              assert (v_of lca == v_of s1 /\ v_of lca == v_of s2');
              assert (do (v_of s2') last2 == tail (v_of lca));*)
        lem_inter_tail (v_of lca) (v_of s1) (do (v_of s2') last2);
            (*assert (i == tail (v_of lca));
              assert (da == empty);
              assert (db == empty);*)
        append_empty_r i;
            //assert (Seq.append i union_ab == i); 
        ())
          
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
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = admit()

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires (exists l1. v_of s1 == apply_log (v_of lca) l1) /\
                    (exists l2. v_of s2 == apply_log (v_of lca) l2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = 
  lem_diff_s (v_of s1) (v_of lca);
  lem_diff_s (v_of s2) (v_of lca)

let linearizable_s2_0''_base_base (lca s1' s2:st) (last1:op_t)
  : Lemma (requires consistent_branches lca s1' s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = 
  lem_diff_s (do (v_of s1') last1) (v_of lca)

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
  if Enqueue? (fst (snd last1)) then
     lem_diff_s (do (v_of s1') last1) (v_of lca)
  else (let i = intersection (v_of lca) (do (v_of s1') last1) (v_of s2) in
        lem_inter_tail (v_of lca) (do (v_of s1') last1) (v_of s2);
        append_empty_r i)

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
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = admit()

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
 
///////////////////////////////////////////////////////////////

let lin_gt0_s1's2'_dd_eq'_s1s2eq (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    Dequeue? (fst (snd last1)) /\ Dequeue? (fst (snd last2)) /\ 
                    length (v_of s1) > 0 /\ length (v_of s2) > 0 /\
                    head (v_of s1) == head (v_of s2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =
  let ii = intersection (v_of lca) (v_of s1) (v_of s2) in
  let dai = diff_s (v_of s1) (v_of lca) in
  let dbi = diff_s (v_of s2) (v_of lca) in  
  lemma_tl (head ii) (Seq.append (tail ii) (sorted_union dai dbi));
    //lemma_tl (head ii) (tail ii);
  append_assoc (create 1 (head ii)) (tail ii) (sorted_union dai dbi); 
  valid_is_unique lca; 
  distinct_invert_append (create 1 (head (v_of lca))) (tail (v_of lca)); 
  lem_inter (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)

(*let lin_gt0_s1's2'_dd_eq'_s2gt_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2) > length (ops_of lca) /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    fst last1 <> fst last2 /\
                    Dequeue? (fst (snd last1)) /\ Dequeue? (fst (snd last2)) /\ 
                    length (v_of s1) > 0 /\ //length (v_of s2) > 0 /\
                    //head (v_of s1) == head (v_of s2) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    
                    (let s2' = inverse_st s2 in
                    consistent_branches lca s1 s2' /\
                    distinct_ops (snoc (ops_of s2') last2) /\
                    (exists l2. (v_of s2' == apply_log (v_of lca) l2)) /\
                    (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2)) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let s2' = inverse_st s2 in
  assume (concrete_merge (v_of lca) (v_of s1) (v_of s2') == v_of s2');
  assume (concrete_merge (v_of lca) (v_of s1) (v_of s2) == v_of s2);
  assume (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) ==
          concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2') last2));
  assume (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) ==
          concrete_merge (v_of lca) (do (v_of lca) last1) (do (v_of s2) last2));
  ()

let rec lin_gt0_s1's2'_dd_eq'_s2gt (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    fst last1 <> fst last2 /\
                    Dequeue? (fst (snd last1)) /\ Dequeue? (fst (snd last2)) /\ 
                    length (v_of s1) > 0 /\ //length (v_of s2) > 0 /\
                    //head (v_of s1) == head (v_of s2) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 
          (decreases length (ops_of s2)) = 
  if ops_of s2 = ops_of lca then
    lin_gt0_s1's2'_dd_eq'_s1s2eq lca s1 s2 last1 last2
  else 
    (assume (length (ops_of s2) > length (ops_of lca));
     let s2' = inverse_st s2 in
     assume (consistent_branches lca s1 s2' /\
             distinct_ops (snoc (ops_of s2') last2) /\
             (exists l2. (v_of s2' == apply_lo g (v_of lca) l2)) /\
             (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2)));
     lin_gt0_s1's2'_dd_eq'_s2gt lca s1 s2' last1 last2;
     lin_gt0_s1's2'_dd_eq'_s2gt_ind lca s1 s2 last1 last2)*)


#push-options "--z3rlimit 100"
let lin_gt0_s1's2'_dd_eq'_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    ops_of s1 == ops_of lca /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    fst last1 <> fst last2 /\
                    Dequeue? (fst (snd last1)) /\ Dequeue? (fst (snd last2)) /\ 
                    Some? (ret_of last1) /\ ret_of last1 = ret_of last2 /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    length (v_of s1) > 0 /\ length (v_of s2) > 0 /\
                    head (v_of s1) == head (v_of s2) /\
                    head (v_of s1) == head (v_of lca) /\
                    
                    (let s2' = inverse_st s2 in
                    let _, last2' = un_snoc (ops_of s2) in
                    Enqueue? (fst (snd last2')) /\
                    consistent_branches lca s1 s2' /\
                    distinct_ops (snoc (ops_of s2') last2) /\
                    (exists l2. (v_of s2' == apply_log (v_of lca) l2)) /\
                    (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2)) /\
                    length (v_of s2') > 0 /\
                    head (v_of s1) == head (v_of s2') /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  let s2' = inverse_st s2 in
  valid_is_unique lca; valid_is_unique s1; valid_is_unique s2; valid_is_unique s2'; 
  let pre, last2' = un_snoc (ops_of s2) in
  let i' = intersection (v_of lca) (v_of s1) (v_of s2') in
  let i = intersection (v_of lca) (v_of s1) (v_of s2) in
  let da = diff_s (v_of s1) (v_of lca) in
  let db' = diff_s (v_of s2') (v_of lca) in
  let db = diff_s (v_of s2) (v_of lca) in
  let su' = sorted_union da db' in
  let su = sorted_union da db in
  let ele = (fst last2', get_ele last2') in
  assume (da == empty); 
  assume (su' == db' /\ su = db);
  assume (do (v_of s2) last2 == tail (v_of s2));
  assume (length i > 0 /\ length i' > 0); 
  assume (v_of lca == v_of s1); 
  assume (v_of s2 == snoc (v_of s2') ele);
  assume (head i' == head i /\ head i == head (v_of lca)); 
  assume (last (v_of s2) == ele); 
  assume (i == i'); //todo
  assume (db == snoc db' ele); //todo
  lemma_mem_append i su';
  lemma_mem_append i su;
  append_assoc i su' (create 1 ele);
  assume (Seq.append i su == snoc (Seq.append i su') ele);
  assume (head (Seq.append i su) == head (snoc (Seq.append i su') ele)); 
  assume (concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
          snoc (concrete_merge (v_of lca) (v_of s1) (v_of s2')) ele); 
  lemma_tail_snoc (concrete_merge (v_of lca) (v_of s1) (v_of s2')) ele;
  assume (tail (snoc (concrete_merge (v_of lca) (v_of s1) (v_of s2')) ele) ==
          snoc (tail (concrete_merge (v_of lca) (v_of s1) (v_of s2'))) ele); 
  assume (tail (concrete_merge (v_of lca) (v_of s1) (v_of s2)) ==
          snoc (tail (concrete_merge (v_of lca) (v_of s1) (v_of s2'))) ele);

  let id' = intersection (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) in
  let id = intersection (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) in
  let dad = diff_s (do (v_of s1) last1) (v_of lca) in
  let dbd' = diff_s (do (v_of s2') last2) (v_of lca) in
  let dbd = diff_s (do (v_of s2) last2) (v_of lca) in
  let sud' = sorted_union dad dbd' in
  let sud = sorted_union dad dbd in
  assume (head (v_of s2') == head (v_of s2));
  assume (dad == empty);
  assume (sud' == dbd' /\ sud = dbd);
  assume (id == id'); //todo
  assume (dbd == snoc dbd' ele); //todo
  lemma_mem_append id sud';
  lemma_mem_append id sud;
  append_assoc id sud' (create 1 ele);
  assert (Seq.append id sud == snoc (Seq.append id sud') ele); 
  assert (head (Seq.append id sud) == head (snoc (Seq.append id sud') ele));
  assert (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) ==
          snoc (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)) ele); 
  ()

let rec lin_gt0_s1's2'_dd_eq' (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    distinct_ops (snoc (ops_of s1) last1) /\
                    distinct_ops (snoc (ops_of s2) last2) /\
                    fst last1 <> fst last2 /\
                    Dequeue? (fst (snd last1)) /\ Dequeue? (fst (snd last2)) /\ 
                    Some? (ret_of last1) /\ ret_of last1 = ret_of last2 /\
                    (exists l1. (v_of s1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (v_of s2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    length (v_of s1) > 0 /\ length (v_of s2) > 0 /\
                    head (v_of s1) == head (v_of s2)) (*/\
                    return (apply_log init_st (ops_of s1)) last1 == ret_of last1 /\
                    return (apply_log init_st (ops_of s2)) last2 == ret_of last2*)
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          (decreases %[length (ops_of s2)]) = 
  assert (length (v_of s1) > 0 /\ length (v_of s2) > 0 /\ head (v_of s1) == head (v_of s2));
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    lin_gt0_s1's2'_dd_eq'_s1s2eq lca s1 s2 last1 last2
  else if ops_of s1 = ops_of lca then
    (assume (length (ops_of s2) > length (ops_of lca));
     let s2' = inverse_st s2 in
     let _, last2' = un_snoc (ops_of s2) in
     assume (v_of s1 == v_of lca);
     if Enqueue? (fst (snd last2')) then
       (assume (head (v_of s1) == head (v_of lca)); 
        distinct_snoc_inv (ops_of s2) last2;
        split_prefix init_st (ops_of lca) (ops_of s2');
        split_prefix init_st (ops_of lca) (snoc (ops_of s2') last2);
        assume (exists l2. (do (v_of s2') last2 == apply_log (v_of lca) l2));  //todo
        assume (consistent_branches lca s1 s2'); //todo
        assume (length (v_of s2') > 0 /\ head (v_of s2') == head (v_of s1));          //todo
        lin_gt0_s1's2'_dd_eq' lca s1 s2' last1 last2; 
        lin_gt0_s1's2'_dd_eq'_ind lca s1 s2 last1 last2)
     else admit())
  else 
    (admit();assert (length (ops_of s1) > length (ops_of lca));
      admit()) //not done
    
let lin_gt0_s1's2'_trial (lca s1 s2:st)
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
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  let s1' = inverse_st s1 in
  let s2' = inverse_st s2 in
  lem_inverse (ops_of lca) (ops_of s1);
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s2);
  inverse_diff_id_s1'_s2' (ops_of lca) (ops_of s1) (ops_of s2);
  lem_apply_log init_st (ops_of s1);
  lem_apply_log init_st (ops_of s2);
  lin_gt0_s1's2'_dd_eq' lca s1' s2' last1 last2

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
let rec suf_is_pre (l a b:st)
  : Lemma (requires consistent_branches l a b /\
                    length (v_of a) > 0 /\ length (v_of b) > 0 /\ head (v_of a) = head (v_of b) /\
                    mem (head (v_of a)) (v_of l))
          (ensures (let i = intersection (v_of l) (v_of a) (v_of b) in
                    is_suffix i (v_of l) /\ is_prefix i (v_of a) /\ is_prefix i (v_of b)))
  (decreases %[length (v_of l); length (v_of a); length (v_of b)]) =
  match length (v_of l), length (v_of a), length (v_of b) with
  |0,_,_ |_,0,_ |_,_,0 -> ()
  |_,_,_ -> let l' = inverse_st l in let a' = inverse_st a in let b' = inverse_st b in
           if head (v_of l) = head (v_of a) && head (v_of l) = head (v_of b) then
             suf_is_pre l' a' b'
           else if head (v_of l) = head (v_of a) then
             suf_is_pre l' a' b
           else if head (v_of l) = head (v_of b) then
             suf_is_pre l' a b'
           //else if head a = head b then
             //union_hd_ab_eq a b
           else suf_is_pre l' a b           
*)

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
