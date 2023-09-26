module App

open SeqUtils
module L = FStar.List.Tot

#set-options "--query_stats"
// the concrete state type
// It is a sequence of pairs of timestamp and message.
// As the sequence is sorted based on timestamps we ignore the message
type concrete_st = list (pos & string)

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
type app_op_t:eqtype = string

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
  (fst op, snd op)::s 

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()
           
//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if fst y < fst x then First_then_second else Second_then_first

//#push-options "--z3rlimit 50"
(*let rec union_s (l1 l2:concrete_st) 
  : Tot (u:concrete_st{forall e. mem e u <==> mem e l1 \/ mem e l2}) 
  (decreases %[length l1; length l2]) =
  match length l1, length l2 with
  |0, 0 -> empty
  |0, _ -> l2
  |_, 0 -> l1
  |_, _ ->  if (fst (head l1) >= fst (head l2) )
             then (mem_cons (head l1) (union_s (tail l1) l2);
                   cons (head l1) (union_s (tail l1) l2))
             else (mem_cons (head l2) (union_s l1 (tail l2));
                   cons (head l2) (union_s l1 (tail l2)))

let rec lca_is_suffix (s:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures is_suffix s (apply_log s l))
          (decreases length l)
          [SMTPat (is_suffix s (apply_log s l))]
  = match length l with
    |0 -> ()
    |_ -> assert (is_suffix s (do s (head l)));
         lca_is_suffix (do s (head l)) (tail l)

let lca_is_suffix_forall (s:concrete_st) 
  : Lemma (ensures (forall l. (is_suffix s (apply_log s l)))) = ()*)

let rec remove (s1:concrete_st) (ele:(pos * string)) : Tot concrete_st =
  match s1 with
  |[] -> []
  |x::xs -> if x = ele then remove xs ele else x::remove xs ele

//s1 - s2
let rec diff_s (s1 s2:concrete_st) : Tot concrete_st (decreases %[s1;s2]) =
  match s1 with
  |[] -> []
  |x::xs -> if L.mem x s2 then diff_s xs s2 else x::diff_s xs s2

let rec lem_diff1 (s1 s2:concrete_st)
  : Lemma (requires (forall e. L.mem e s1 ==> L.mem e s2))
          (ensures diff_s s1 s2 = [])
          (decreases %[s1;s2]) =
  match s1,s2 with
  |[],_ -> ()
  |x::xs,_ -> lem_diff1 xs s2

let lem_diff (s1 s2:concrete_st)
  : Lemma (requires s1 = s2)
          (ensures diff_s s1 s2 = [])
  = lem_diff1 s1 s2

val sorted: concrete_st -> Tot bool
let rec sorted l = match l with
    | [] -> true
    | [x] -> true
    | x :: y :: xs -> (fst x >= fst y) && (sorted (y :: xs))

val eq1: (pos * string) -> (pos * string) -> Tot nat
let eq1 x y = if x = y then 1 else 0

val count_elem: (pos * string) -> concrete_st -> Tot nat
let rec count_elem x l = match l with
  | [] -> 0
  | hd :: tl -> eq1 hd x + count_elem x tl

val insert : x:(pos * string) -> l1:concrete_st{sorted l1} -> concrete_st
let rec insert x l1 = match l1 with
  | [] -> [x]
  | hd :: tl -> if fst x > fst hd then x :: l1 else hd :: (insert x tl)

val insert_sorted: x:(pos * string) -> l1:concrete_st{sorted l1} -> Lemma (sorted (insert x l1))
let rec insert_sorted x l1 = match l1 with
  | [] -> ()
  | hd :: tl -> insert_sorted x tl

val insert_permutation: x:(pos * string) -> l1:concrete_st{sorted l1}
  -> Lemma (forall k.{:pattern (count_elem k (insert x l1))} count_elem k (insert x l1) = eq1 k x + count_elem k l1)
let rec insert_permutation x l1 = match l1 with
  | [] -> ()
  | hd :: tl -> insert_permutation x tl

val insert_pf : x:(pos * string) -> l1:concrete_st{sorted l1} -> Tot (l2:concrete_st{sorted l2 /\ (forall k.{:pattern (count_elem k l2)} count_elem k l2 = eq1 k x + count_elem k l1)})
let rec insert_pf x l1 = insert_sorted x l1;
                         insert_permutation x l1;
                         insert x l1

val insertion_sort : l1:concrete_st -> Tot (l2:concrete_st{sorted l2 /\ (forall k. count_elem k l2 == count_elem k l1)})
let rec insertion_sort l1 = match l1 with
    | [] -> []
    | hd :: tl -> insert_pf hd (insertion_sort tl)

let order = (fun (x y:(pos & string)) -> if fst x > fst y then -1 else if fst x < fst y then 1 else 0)

let rec union_s (l1 l2:concrete_st) 
  : Tot (u:concrete_st{forall e. L.mem e u <==> L.mem e l1 \/ L.mem e l2}) 
  (decreases %[ l1;  l2]) =
  match l1,  l2 with
  |[],[] -> []
  |[], _ -> l2
  |_, [] -> l1
  |x::xs, y::ys -> if (fst x >= fst y)
             then x::(union_s xs l2)
             else y::(union_s l1 ys)


let concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
         (requires (exists l1 l2. apply_log lca l1 == s1 /\ apply_log lca l2 == s2))
         (ensures (fun m -> true)) = //(forall e. L.mem e m ==> L.mem e s1 \/ L.mem e s2 \/ L.mem e lca))) =
                  //(lca == s1 ==> m == s2) /\ (lca == s2 ==> m == s1))) =
  let la = diff_s s1 lca in
  let lb = diff_s s2 lca in
  let ab = union_s la lb in
  let m = union_s ab lca in
  //let r = insertion_sort m in
  //assert (sorted r);
  m
   
//#push-options "--z3rlimit 100"
let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) = admit()

let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0)
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

#push-options "--z3rlimit 100"
let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    consistent_branches l' s1' (do_st s2'' last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = 
  lem_diff (v_of lca) (v_of s1);
  lem_diff (v_of lca) (v_of s2');
  let l' = inverse_st lca in
  let pre,lastop = un_snoc (ops_of lca) in
  //assume (v_of lca = v_of s2'); 
  //assume (do (v_of s2') last2 = (fst last2, snd last2)::(v_of s2'));
  //assume (diff_s (v_of s1) (v_of lca) = []);
  assume (fst lastop < fst last2);
  if v_of s2' = [] then admit() else (assume (L.hd (v_of s2') = (fst lastop, snd lastop)));
  //assert (diff_s (do (v_of s2') last2) (v_of lca) = [(fst last2, snd last2)]);
  ()


let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) = ()

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca)
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) (decreases length (ops_of lca)) =
  lem_diff (v_of s1) (v_of lca);
  lem_diff (v_of s2) (v_of lca)

#push-options "--z3rlimit 10"
let linearizable_gt0_base_last1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  let l1 = (fst last1, snd last1) in
  let l2 = (fst last2, snd last2) in
  assert (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 ==
          cons l1 (cons l2 (v_of lca)));
  lemma_mem_append (create 1 l2) (v_of lca);
  append_assoc (create 1 l1) (create 1 l2) (v_of lca);
  assert (cons l1 (cons l2 (v_of lca)) == Seq.append (cons l1 (cons l2 empty)) (v_of lca));
  ()

let linearizable_gt0_base_last2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2))
         
          (ensures (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) =
  let l1 = (fst last1, snd last1) in
  let l2 = (fst last2, snd last2) in
  assert (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 ==
          cons l2 (cons l1 (v_of lca)));
  lemma_mem_append (create 1 l1) (v_of lca);
  append_assoc (create 1 l2) (create 1 l1) (v_of lca);
  assert (cons l2 (cons l1 (v_of lca)) == Seq.append (cons l2 (cons l1 empty)) (v_of lca));
  ()
#pop-options

let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2)
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second_then_first? (resolve_conflict last1 last2) ==>
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                         (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = 
  if First_then_second? (resolve_conflict last1 last2) then
    linearizable_gt0_base_last1 lca s1 s2 last1 last2
  else linearizable_gt0_base_last2 lca s1 s2 last1 last2

let lem_unionb (a b:concrete_st)
  : Lemma (requires length a > 0 /\ length b > 0 /\
                    lt (fst (head a)) (fst (head b)))
          (ensures union_s a b == cons (fst (head b), snd (head b)) (union_s a (tail b))) = ()

let lem_uniona (a b:concrete_st)
  : Lemma (requires length a > 0 /\ length b > 0 /\
                    lt (fst (head b)) (fst (head a)))
          (ensures union_s a b == cons (fst (head a), snd (head a)) (union_s (tail a) b)) = ()

#push-options "--z3rlimit 50"
let linearizable_gt0_ind_c2 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2))
       
          (ensures eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  let s1v = do (v_of s1) last1 in
  let s2v = do (v_of s2) last2 in
  let da = (diff_suf s1v (v_of lca)) in
  let db = (diff_suf s2v (v_of lca)) in
  let db' = (diff_suf (v_of s2) (v_of lca)) in
  let da' = (diff_suf (v_of s1) (v_of lca)) in
  let l1 = (fst last1, snd last1) in
  let l2 = (fst last2, snd last2) in 
  lemma_tl l2 (v_of s2);
  lem_diff_suf s2v (v_of lca); 
  lemma_tl l1 (v_of s1);
  lem_diff_suf s1v (v_of lca);  
  assert (lt (fst last1) (fst (last2))); 
  assert (lt (fst (head da)) (fst (head db))); 
  lem_unionb da db;
  append_assoc (create 1 l2) (union_s da db') (v_of lca)
  
let linearizable_gt0_ind1_c11 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2))
        
          (ensures eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  let s1v = do (v_of s1) last1 in
  let s2v = do (v_of s2) last2 in
  let da = (diff_suf s1v (v_of lca)) in
  let db = (diff_suf s2v (v_of lca)) in
  let da' = (diff_suf (v_of s1) (v_of lca)) in
  let db' = (diff_suf (v_of s2) (v_of lca)) in
  let l1 = (fst last1, snd last1) in
  let l2 = (fst last2, snd last2) in
  lemma_tl l1 (v_of s1);
  lem_diff_suf s1v (v_of lca);
  lemma_tl l2 (v_of s2);
  lem_diff_suf s2v (v_of lca);
  assert (lt (fst last2) (fst (last1)));
  assert (lt (fst (head db)) (fst (head da)));
  lem_uniona da db; 
  append_assoc (create 1 l1) (union_s da' db) (v_of lca)
#pop-options

let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2)
       
          (ensures (let s2' = inverse_st s2 in
                   ((First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()

let linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2)
                           
          (ensures (let s1' = inverse_st s1 in
                   ((ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1' (do_st s2 last2) /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                       
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) /\

                   ((Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                       
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = seq string

// init state 
let init_st_s = empty

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = cons (snd op) s

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
          (ensures eq_sm (do_s st_s op) (do st op)) = ()
  
////////////////////////////////////////////////////////////////
