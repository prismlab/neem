module App

open SeqUtils
module L = FStar.List.Tot
#set-options "--query_stats"
// the concrete state type
// It is a sequence of pairs of timestamp and element.
type concrete_st = list (nat & nat)

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
// (the only operation is write a message)
type app_op_t:eqtype = 
  | Enqueue : nat -> app_op_t
  | Dequeue

type ret_t:eqtype = option (nat * nat)

let get_ele (o:op_t{Enqueue? (fst (snd o))}) : nat =
  match o with
  |(_, (Enqueue x,_)) -> x

let rec mem_id_s (id:nat) (s:concrete_st) =
  match s with
  |[] -> false
  |x::xs -> fst x = id || mem_id_s id xs

let rec unique_st (s:concrete_st) =
  match s with
  |[] -> true
  |x::xs -> not (mem_id_s (fst x) xs) && unique_st xs

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
  match op with
  |(id, (Enqueue x, _)) -> L.append s [(id, x)]
  |(_, (Dequeue, _)) -> if L.length s = 0 then s else L.tl s

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()

let return (s:concrete_st) (o:op_t) : ret_t =
  match o with
  |(_, (Enqueue _, _)) -> None
  |(_, (Dequeue, r)) -> if L.length s = 0 then None else Some (L.hd s)

let extract (o:op_t{Dequeue? (fst (snd o)) /\ Some? (ret_of o)}) : (nat * nat) =
  let (_, (_, Some x)) = o in x

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  match x, y with
  |(_,(Enqueue _,_)), (_,(Enqueue _,_)) -> if fst x < fst y then Second_then_first else First_then_second
  |_, (_,(Dequeue,None)) -> Noop_second
  |(_,(Dequeue,None)), _ -> Noop_first
  |(_,(Dequeue,None)), (_,(Dequeue,None)) -> Noop_both
  |(_,(Enqueue _,_)), (_,(Dequeue,Some _)) -> Second_then_first
  |(_,(Dequeue,Some _)), (_,(Enqueue _,_)) -> First_then_second 
  |(_,(Dequeue,Some _)), (_,(Dequeue,Some _)) -> if x = y then First 
                                                 else if fst (extract x) < fst (extract y) then First_then_second
                                                      else Second_then_first

let resolve_conflict_prop (x:op_t) (y:op_t{fst x <> fst y})
  : Lemma (ensures ((Enqueue? (fst (snd x)) && Enqueue? (fst (snd y)) && fst x < fst y) \/
                   (Dequeue? (fst (snd y)) && Some? (ret_of y) && Enqueue? (fst (snd x))) \/
                   (Dequeue? (fst (snd x)) && Some? (ret_of x) &&
                    Dequeue? (fst (snd y)) && Some? (ret_of y) && fst (extract x) >= fst (extract y))) <==>
                 
                   (resolve_conflict x y == Second_then_first)) = ()

val forallb : #a:eqtype
            -> f:(a -> bool)
            -> l:list a
            -> Tot (b:bool{(forall e. L.mem e l ==> f e) <==> b = true})
let rec forallb #a f l =
  match l with
  |[] -> true
  |hd::tl -> if f hd then forallb f tl else false
  
val sorted: concrete_st -> Tot bool
let rec sorted l = match l with
    | [] | [_] -> true
    | x::xs -> forallb (fun (e:(nat * nat)) -> fst x < fst e) xs  && sorted xs

let rec diff_s (a:concrete_st) (l:concrete_st)
  : Tot (d:concrete_st{(a == l ==> d = []) /\
                       (exists d. a == L.append d l ==> d = [])})
        (decreases %[a; l]) =
  match a, l with
  |[],_ -> []
  |_,[] -> a
  |x::xs,y::ys -> if x <> y then diff_s a ys else diff_s xs ys
  
  (*match a, l with
  | x::xs, y::ys -> if (fst y) < (fst x) then diff_s a ys else (diff_s xs ys)
  | [], y::ys -> []
  | _, [] -> a*)

let rec intersection (l a b:concrete_st)
  : Tot (i:concrete_st{((l == a /\ l == b) ==> i == l) /\
                       (l == a /\ (exists d. b == L.append l d) ==> i == l) /\
                       (l == b /\ (exists d. a == L.append l d) ==> i == l) /\
                       (l <> [] /\ a <> [] /\ b <> [] /\ L.hd l = L.hd a /\ L.hd l = L.hd b ==>
                           i <> [] /\ L.hd i = L.hd l)})
  (decreases %[l;a;b]) =
  match l, a, b with
  |[],_,_ |_,[],_ |_,_,[] -> []
  |x::xs,y::ys,z::zs -> if x = y && x = z then
                       x::intersection xs ys zs
                    else if x = y then
                      intersection xs ys b
                    else if x = z then
                      intersection xs a zs
                    else intersection xs a b
  (*match l, a, b with
  | x::xs, y::ys, z::zs -> if (((fst x) < (fst y) || (fst x) < (fst z))) then 
                          intersection xs a b
                       else ((*assert (fst x = fst y /\ fst x = fst z);*) x::(intersection xs ys zs))
  | x::xs, [], z::zs -> []
  | x::xs, y::ys, [] -> []
  | x::xs, [], [] -> []
  | [], _, _ -> []*)

let rec sorted_union (l1 l2:concrete_st) 
  : Tot (u:concrete_st {(l1 = [] /\ l2 = [] ==> u = []) /\
                       (l1 = [] ==> u = l2) /\
                       (l2 = [] ==> u = l1) /\
                       (forall e. L.mem e u <==> L.mem e l1 \/ L.mem e l2)})
  (decreases %[l1; l2]) =
  match l1, l2 with
  |[],[] -> []
  |[],_ -> l2
  |_,[] -> l1
  |x::xs,y::ys -> if fst x < fst y then x::sorted_union xs l2 else y::sorted_union l1 ys

let concrete_merge1 (lca s1 s2:concrete_st) : concrete_st =
  let i = intersection lca s1 s2 in
  let da = diff_s s1 lca in
  let db = diff_s s2 lca in 
  let union_ab = sorted_union da db in
  L.append i union_ab

let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun _ -> True)) =
  concrete_merge1 lca s1 s2
  
let rec append_id (l1 l2:concrete_st)
  : Lemma (ensures (forall id. mem_id_s id (L.append l1 l2) <==> mem_id_s id l1 \/ mem_id_s id l2) /\
                   (unique_st l1 /\ unique_st l2 /\ (forall id. mem_id_s id l2 ==> not (mem_id_s id l1)) ==> 
                   unique_st (L.append l1 l2)))
  = match l1 with
  | [] -> ()
  | hd::tl -> append_id tl l2
  
let do_is_unique (s:concrete_st) (op:op_t) 
  : Lemma (requires unique_st s /\ (not (mem_id_s (fst op) s)))
          (ensures unique_st (do s op)) = 
  match op with
  |(id, (Enqueue x, _)) -> append_id s [id, x]
  |(_, (Dequeue, _)) -> ()

let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (forall id. mem_id_s id (apply_log s l) ==> mem_id_s id s \/ mem_id id l))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> (if Enqueue? (fst (snd (head l))) then append_id s [fst (head l), get_ele (head l)] else ());
       mem_cons (head l) (tail l);
       lem_foldl (do s (head l)) (tail l)
       
let rec lem_foldl1 (s:concrete_st) (l:log)
  : Lemma (requires unique_st s /\ distinct_ops l /\
                    (forall id. mem_id_s id s ==> not (mem_id id l)))
          (ensures unique_st (apply_log s l))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> do_is_unique s (head l);
       (if Enqueue? (fst (snd (head l))) then append_id s [fst (head l), get_ele (head l)] else ());
       mem_cons (head l) (tail l);
       distinct_invert_append (create 1 (head l)) (tail l);
       lem_foldl1 (do s (head l)) (tail l)

let valid_is_unique (s:st0) 
  : Lemma (requires distinct_ops (ops_of s) /\ v_of s == apply_log init_st (ops_of s))
          (ensures unique_st (v_of s)) =
  lem_foldl1 init_st (ops_of s)
          
let last_deq (s:concrete_st) (op:op_t)
  : Lemma (requires Dequeue? (fst (snd op)) /\ Some? (ret_of op) /\ return s op == ret_of op)
          (ensures s <> [] /\ Some (L.hd s) == ret_of op) = ()

(*let rec lem_inter_tail (l a b:concrete_st) 
  : Lemma (ensures ((l <> [] /\ ((a = l /\ b = L.tl l) \/ (b = l /\ a = L.tl l))) ==> 
                         (intersection l a b = L.tl l)))
          (decreases l) =
  match l, a, b with
  |[],_,_ |_,[],_ |_,_,[] -> ()
  |x::xs,y::ys,z::zs -> if x = y && x = z then
                       lem_inter_tail xs ys zs
                    else lem_inter_tail xs a b*)
           
let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0)
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let rec diff_lem_last (a' l: concrete_st) (ele:nat * nat)
  : Lemma (requires sorted l /\ sorted a' /\ a' = l)
          (ensures (let da = diff_s (L.append a' [ele]) l in
                    da = [ele]))
          (decreases %[a';l]) =
  match a', l with
  |[],_ -> ()
  |_,[] -> ()
  |x::xs,y::ys -> if x <> y then diff_lem_last a' ys ele else diff_lem_last xs ys ele

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
  assume (sorted (v_of lca) /\ sorted (v_of s1) /\ sorted (v_of s2'));  //todo
  assume (ret_of last2 = return (v_of s2') last2); //to include in pre-cond        
  if Enqueue? (fst (snd last2)) then 
     diff_lem_last (v_of s2') (v_of lca) (fst last2, get_ele last2)
  else if Dequeue? (fst (snd last2)) && Some? (ret_of last2) then 
     (last_deq (v_of s2') last2;
      L.append_mem_forall (intersection (v_of lca) (v_of s1) (do (v_of s2') last2)) [])
  else ()

#push-options "--z3rlimit 50"
let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches_s2_gt0 lca s1 s2' /\
                    is_prefix (ops_of lca) (snoc (ops_of s2') last2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    Enqueue? (fst (snd last2)) /\

                    (let inv2 = inverse_st s2' in
                    let _, lastop = un_snoc (ops_of s2') in
                    Enqueue? (fst (snd lastop)) /\
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
  let i = intersection (v_of lca) (v_of s1) (v_of s2) in
  let da = diff_s (v_of s1) (v_of lca) in
  let db = diff_s (v_of s2) (v_of lca) in 
  let union_ab = sorted_union da db in
  L.append_mem_forall i union_ab

let linearizable_s2_0''_base_base (lca s1' s2:st) (last1:op_t)
  : Lemma (requires consistent_branches lca s1' s2 /\
                    is_prefix (ops_of lca) (snoc (ops_of s1') last1) /\
                    ops_of s1' = ops_of lca /\ ops_of s2 = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)))
         
          (ensures eq (do (v_of s1') last1) (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2))) = ()

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
  assume (sorted (v_of lca) /\ sorted (v_of s1') /\ sorted (v_of s2));  //todo
  assume (ret_of last1 = return (v_of s1') last1); //to include in pre-cond        
  if Enqueue? (fst (snd last1)) then 
     diff_lem_last (v_of s1') (v_of lca) (fst last1, get_ele last1)
  else if Dequeue? (fst (snd last1)) && Some? (ret_of last1) then 
     (last_deq (v_of s1') last1;
      L.append_mem_forall (intersection (v_of lca) (do (v_of s1') last1) (v_of s2)) [])
  else ()

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
  lem_apply_log init_st (ops_of s1)

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
  lem_apply_log init_st (ops_of s1);
  lem_apply_log init_st (ops_of s2)
 
///////////////////////////////////////////////////////////////

let rec not_id_not_ele (id:nat) (ele:nat) (s:concrete_st)
  : Lemma (requires not (mem_id_s id s))
          (ensures not (L.mem (id, ele) s)) 
          (decreases s) =
  match s with
  |[] -> ()
  |x::xs -> not_id_not_ele id ele xs
    
#push-options "--z3rlimit 50"
let rec lem_s1s2_then_lca (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (forall e. L.mem e (v_of s1) /\ L.mem e (v_of s2) ==> L.mem e (v_of lca)))
          (decreases %[(length (ops_of s1))]) =
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then ()
  else if ops_of s1 = ops_of lca then ()
  else (let s1' = inverse_st s1 in
        let pre1, last1 = un_snoc (ops_of s1) in
        lemma_mem_snoc pre1 last1;
        distinct_invert_append pre1 (create 1 last1);
        lem_inverse (ops_of lca) (ops_of s1); 
        lastop_diff (ops_of lca) (ops_of s1);
        inverse_diff_id_s1' (ops_of lca) (ops_of s1) (ops_of s2);
        if Dequeue? (fst (snd last1)) then
          (lem_s1s2_then_lca lca s1' s2;
           valid_is_unique lca; valid_is_unique s1; valid_is_unique s2; valid_is_unique s1')
        else (lem_s1s2_then_lca lca s1' s2;
              valid_is_unique lca; valid_is_unique s1; valid_is_unique s2; valid_is_unique s1';
              lem_foldl init_st (ops_of lca); lem_foldl init_st (ops_of s1); lem_foldl init_st (ops_of s2); 
              split_prefix init_st (ops_of lca) (ops_of s1); 
              lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
              split_prefix init_st (ops_of lca) (ops_of s2);
              lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
              lem_diff (ops_of s1) (ops_of lca); 
              lastop_diff (ops_of lca) (ops_of s1); 
              
              assert (not (mem_id (fst last1) (ops_of lca))); 
              L.append_mem_forall (v_of s1') [(fst last1, get_ele last1)];
              assert (L.mem (fst last1, get_ele last1) (v_of s1));
              assert (forall id. mem_id_s id (v_of lca) ==> mem_id id (ops_of lca));
              assert (not (mem_id_s (fst last1) (v_of lca)));
              not_id_not_ele (fst last1) (get_ele last1) (v_of lca);
              not_id_not_ele (fst last1) (get_ele last1) (v_of s2);
              assert (not (L.mem (fst last1, get_ele last1) (v_of lca)));
              ()))

let rec lem_inter (l a b:concrete_st)
  : Lemma (requires (forall e. (L.mem e a /\ L.mem e b) ==> L.mem e l) /\
                    sorted l /\ sorted a /\ sorted b)
          (ensures (a <> [] /\ b <> [] /\ L.hd a = L.hd b ==> 
                      (let i = intersection l a b in
                       i <> [] /\ L.hd i = L.hd a))) =
  match l, a, b with
  |[],_,_ |_,[],_ |_,_,[] -> ()
  |x::xs,y::ys,z::zs -> if x = y || x = z then ()
                    else (assert (x <> y /\ x <> z);
                          if y = z then lem_inter xs a b else ())

let rec inter (l a' b' a b: concrete_st)
  : Lemma (requires (forall e. (L.mem e a' /\ L.mem e b') ==> L.mem e l) /\
                    sorted l /\ sorted a /\ sorted b /\ sorted a' /\ sorted b' /\
                    
                    a' <> [] /\ b' <> [] /\ L.hd a' = L.hd b' /\
                    
                    a = L.tl a' /\ b = L.tl b')
         
          (ensures (let i' = intersection l a' b' in
                    let i = intersection l a b in
                    i' <> [] /\
                    L.tl i' = i)) =
 
  match l, a', b' with
  |[],_,_ |_,[],_ |_,_,[] -> ()
  |x::xs,y::ys,z::zs -> if x = y || x = z then ()
                    else (assert (x <> y /\ x <> z);
                          if y = z then (inter xs a' b' a b) else ())
                          
let rec diff_lem (a' l: concrete_st)
  : Lemma (requires sorted l /\ sorted a' /\
                    a' <> [] /\ L.mem (L.hd a') l)
          (ensures (let da' = diff_s a' l in
                    let da = diff_s (L.tl a') l in
                    da' = da))
          (decreases %[a';l]) =
  match a', l with
  |[],_ -> ()
  |_,[] -> ()
  |x::xs,y::ys -> if x <> y then diff_lem a' ys else ()
                          
let lin_gt0_s1's2'_dd_eq' (lca s1 s2:st) (last1 last2:op_t)
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
                    v_of s1 <> [] /\ v_of s2 <> [] /\
                    L.hd (v_of s1) == L.hd (v_of s2))
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =
                      
     assert (L.hd (v_of s1) = L.hd (v_of s2));
     assume (sorted (v_of lca) /\ sorted (v_of s1) /\ sorted (v_of s2)); //todo
     lem_s1s2_then_lca lca s1 s2;
     lem_inter (v_of lca) (v_of s1) (v_of s2);
     let i' = intersection (v_of lca) (v_of s1) (v_of s2) in
     let i = intersection (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) in
     let da' = diff_s (v_of s1) (v_of lca) in
     let db' = diff_s (v_of s2) (v_of lca) in
     let da = diff_s (do (v_of s1) last1) (v_of lca) in
     let db = diff_s (do (v_of s2) last2) (v_of lca) in   
     assert (L.hd i' = L.hd (v_of s1)); 
     assert (do (v_of s1) last1 == L.tl (v_of s1) /\ do (v_of s2) last2 == L.tl (v_of s2));
     inter (v_of lca) (v_of s1) (v_of s2) (do (v_of s1) last1) (do (v_of s2) last2);
     assert (L.tl i' = i); 
     diff_lem (v_of s1) (v_of lca);
     diff_lem (v_of s2) (v_of lca);
     assert (da = da' /\ db = db');
     ()

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

let rec inter_ee (l a' b': concrete_st) (e e1:(nat * nat))
  : Lemma (requires l = a' /\ l = b')
          (ensures (let i' = intersection l a' b' in
                    let i = intersection l (L.append a' [e]) (L.append b' [e1]) in
                    i = i')) =
  match l, a', b' with
  |[],_,_ |_,[],_ |_,_,[] -> ()
  |x::xs,y::ys,z::zs -> if x = y && x = z then 
                       inter_ee xs ys zs e e1  else ()
                          
let linearizable_gt0_base_ee_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 > fst last2)
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
   assume (sorted (v_of lca) /\ sorted (v_of s1) /\ sorted (v_of s2)); //todo
   assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
   assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond    
   let i' = intersection (v_of lca) (v_of s1) (do (v_of s2) last2) in
   let i = intersection (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) in
   let da' = diff_s (v_of s1) (v_of lca) in
   let da = diff_s (do (v_of s1) last1) (v_of lca) in
   let db = diff_s (do (v_of s2) last2) (v_of lca) in
   diff_lem_last (v_of s1) (v_of lca) (fst last1, get_ele last1);
   diff_lem_last (v_of s2) (v_of lca) (fst last2, get_ele last2);
     //assert (da = [fst last1, get_ele last1]);
     //assert (db = [fst last2, get_ele last2]);
     //assert (sorted_union da db == [(fst last2, get_ele last2); (fst last1, get_ele last1)]);
   inter_ee (v_of lca) (v_of s1) (v_of s2) (fst last1, get_ele last1) (fst last2, get_ele last2);
     //assert (i = i');
     //assert (da' = []);
     //assert (sorted_union da' db = [fst last2, get_ele last2]);
   L.append_assoc i' (sorted_union da' db) [fst last1, get_ele last1]

let rec inter_de (l a' b': concrete_st) (e:(nat * nat))
  : Lemma (requires l = a' /\ l = b')
          (ensures l <> [] ==> (let i' = intersection l l (L.append l [e]) in
                    let i = intersection l (L.tl l) (L.append l [e]) in
                    i = L.tl l)) =
  match l, a', b' with
  |[],_,_ |_,[],_ |_,_,[] -> ()
  |x::xs,y::ys,z::zs -> if x = y && x = z then 
                       inter_de xs ys zs e 
                    else ()

let linearizable_gt0_base_de_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ Enqueue? (fst (snd last2)))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
   assume (sorted (v_of lca) /\ sorted (v_of s1) /\ sorted (v_of s2)); //todo
   assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
   assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond    
   let i' = intersection (v_of lca) (v_of s1) (do (v_of s2) last2) in
   let i = intersection (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) in
   let da' = diff_s (v_of s1) (v_of lca) in
   let da = diff_s (do (v_of s1) last1) (v_of lca) in
   let db = diff_s (do (v_of s2) last2) (v_of lca) in
     //assert (v_of s1 <> []);
     //assert (do (v_of s1) last1 = L.tl (v_of lca));
     //assert (do (v_of s2) last2 = L.append (v_of lca) [fst last2, get_ele last2]);
   inter_de (v_of lca) (v_of s1) (v_of s2) (fst last2, get_ele last2);
     //assert (i = L.tl (v_of lca));  
   ()

let linearizable_gt0_base_dd_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
   assume (sorted (v_of lca) /\ sorted (v_of s1) /\ sorted (v_of s2)); //todo
   assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
   assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond  
   ()

let linearizable_gt0_base_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    First_then_second? (resolve_conflict last1 last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  if Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 > fst last2 then
    linearizable_gt0_base_ee_fts lca s1 s2 last1 last2
  else if Dequeue? (fst (snd last1)) && Some? (ret_of last1) && Enqueue? (fst (snd last2)) then
    linearizable_gt0_base_de_fts lca s1 s2 last1 last2
  else linearizable_gt0_base_dd_fts lca s1 s2 last1 last2

////////////////////////////////////////////////////////////////

let linearizable_gt0_base_ee_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Enqueue? (fst (snd last1)) /\ Enqueue? (fst (snd last2)) /\ fst last1 < fst last2)
         
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =  
   assume (sorted (v_of lca) /\ sorted (v_of s1) /\ sorted (v_of s2)); //todo
   assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
   assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond    
   let i' = intersection (v_of lca) (do (v_of s1) last1) (v_of s2) in
   let i = intersection (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) in
   let db' = diff_s (v_of s2) (v_of lca) in
   let da = diff_s (do (v_of s1) last1) (v_of lca) in
   let db = diff_s (do (v_of s2) last2) (v_of lca) in
   diff_lem_last (v_of s1) (v_of lca) (fst last1, get_ele last1);
   diff_lem_last (v_of s2) (v_of lca) (fst last2, get_ele last2);
   inter_ee (v_of lca) (v_of s1) (v_of s2) (fst last1, get_ele last1) (fst last2, get_ele last2);
   L.append_assoc i' (sorted_union da db') [fst last2, get_ele last2]                        

let linearizable_gt0_base_de_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\ Enqueue? (fst (snd last1)))
         
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =
   assume (sorted (v_of lca) /\ sorted (v_of s1) /\ sorted (v_of s2)); //todo
   assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
   assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond    
   let i' = intersection (v_of lca) (do (v_of s1) last1) (v_of s2) in
   let i = intersection (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) in
   let db' = diff_s (v_of s2) (v_of lca) in
   let da = diff_s (do (v_of s1) last1) (v_of lca) in
   let db = diff_s (do (v_of s2) last2) (v_of lca) in
   inter_de (v_of lca) (v_of s1) (v_of s2) (fst last1, get_ele last1)

let linearizable_gt0_base_dd_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    Dequeue? (fst (snd last1)) /\ Some? (ret_of last1) /\ 
                    Dequeue? (fst (snd last2)) /\ Some? (ret_of last2) /\
                    fst (extract last1) >= fst (extract last2))
         
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =          
   admit();assume (sorted (v_of lca) /\ sorted (v_of s1) /\ sorted (v_of s2)); //todo
   assume (ret_of last1 = return (v_of s1) last1); //to include in pre-cond    
   assume (ret_of last2 = return (v_of s2) last2); //to include in pre-cond  
   ()

let linearizable_gt0_base_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\ 
                    (exists l2. (do (v_of s2) last2 == apply_log (v_of lca) l2)) /\
                    (exists l1. (do (v_of s1) last1 == apply_log (v_of lca) l1)) /\
                    Second_then_first? (resolve_conflict last1 last2))
         
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =
  if Enqueue? (fst (snd last1)) && Enqueue? (fst (snd last2)) && fst last1 < fst last2 then
    linearizable_gt0_base_ee_stf lca s1 s2 last1 last2
  else if Dequeue? (fst (snd last2)) && Some? (ret_of last2) && Enqueue? (fst (snd last1)) then
    linearizable_gt0_base_de_stf lca s1 s2 last1 last2
  else linearizable_gt0_base_dd_stf lca s1 s2 last1 last2
  
////////////////////////////////////////////////////////////////




////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = list nat

// init state 
let init_st_s = []

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = 
  match op with
  |(id, (Enqueue x, _)) -> L.append s [x]
  |(_, (Dequeue, _)) -> if s = [] then s else L.tl s

//equivalence relation between the concrete states of sequential type and MRDT
let rec eq_sm (st_s:concrete_st_s) (st:concrete_st) : Tot prop =
 match st_s, st with
 |[],[] -> True
 |_,[] |[],_ -> False
 |x::xs,y::ys -> x = snd y /\ eq_sm xs ys

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

let rec do_eq1 (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st /\ Enqueue? (fst (snd op)))
          (ensures eq_sm (do_s st_s op) (do st op)) =
 match st_s, st with
 |_,[] |[],_ -> ()
 |x::xs,y::ys -> do_eq1 xs ys op

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) =
  if Enqueue? (fst (snd op)) then do_eq1 st_s st op else ()
  
////////////////////////////////////////////////////////////////


let help (p s h xs hd:concrete_st)
  : Lemma (requires xs == L.append (L.append p h) s)
          (ensures L.append hd xs == L.append (L.append (L.append hd p) h) s)
         // [SMTPat (xs == L.append (L.append p h) s)]
  = L.append_assoc hd p h;
    L.append_assoc p h s;
    L.append_assoc hd (L.append p h) s


(*let rec intersectionLemma1 (l a b: concrete_st)
  : Lemma (requires (forall e. (L.mem e a /\ L.mem e b) ==> L.mem e l) /\
                    sorted l /\ sorted a /\ sorted b /\
                    a <> [] /\ b <> [] /\ L.hd a = L.hd b)
          (ensures (exists p s. l == L.append (L.append p [L.hd a]) s (*/\ 
                    intersection l a b == intersection l (L.tl a) (L.tl b*))) = 
 match l, a, b with
  |[],_,_ |_,[],_ |_,_,[] -> ()
  |x::xs,y::ys,z::zs -> if x = y || x = z then L.append_mem_forall (L.append [] [L.hd a]) xs
                    else (assert (x <> y /\ x <> z);
                          if y = z then 
                             (intersectionLemma1 xs a b;
                              L.append_mem_forall [x] xs;
                              L.append_assoc [] [L.hd a] xs;
                              assert (exists p s. xs == L.append (L.append p [L.hd a]) s);
                              assume (exists p s. L.append [x] xs == L.append (L.append (L.append [x] p) [L.hd a]) s); //todo
                              ()) else ())*)


(*let common (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    sorted (v_of lca) /\ sorted (v_of s1) /\ sorted (v_of s2))
          (ensures (let i = intersection (v_of lca) (v_of s1) (v_of s2) in
                    let da = diff_s (v_of s1) (v_of lca) in
                    let db = diff_s (v_of s2) (v_of lca) in
                    (forall e. L.mem e (v_of s1) /\ L.mem e (v_of s2) ==> L.mem e (v_of lca)) /\
                    (forall e. L.mem e i <==> (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2))) /\
                    (forall e. L.mem e da <==> L.mem e (v_of s1) /\ not (L.mem e (v_of lca))) /\
                    (forall e. L.mem e db <==> L.mem e (v_of s2) /\ not (L.mem e (v_of lca))) /\
                    (forall id. mem_id_s id i ==> (not (mem_id_s id da) /\ not (mem_id_s id db))) /\
                    (forall id id1. mem_id_s id (v_of lca) /\ mem_id_s id1 da ==> id < id1) /\
                    (forall id id1. mem_id_s id (v_of lca) /\ mem_id_s id1 db ==> id < id1) /\
                    (forall id. mem_id_s id da ==> not (mem_id_s id db)))) = admit()*)
