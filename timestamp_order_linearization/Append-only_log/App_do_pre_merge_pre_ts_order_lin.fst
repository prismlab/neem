module App_do_pre_merge_pre_ts_order_lin

open SeqUtils
module L = FStar.List.Tot
module S = Set_extended_new

#set-options "--query_stats"
let rec mem_id_s (id:pos) (l:list (pos * string))
    : Tot (b:bool {b = true <==> (exists m. L.mem (id,m) l) /\ (exists e. L.mem e l ==> fst e = id)}) =
  match l with
  |[] -> false
  |(id1,m)::xs -> id = id1 || mem_id_s id xs

let rec unique_s (l:list (pos * string)) =
  match l with
  |[] -> true
  |(id,m)::xs -> not (mem_id_s id xs) && unique_s xs

let rec idx (id:pos * string) (l:list (pos * string) {L.mem id l /\ unique_s l}) : Tot nat =
  match l with
  |id1::xs -> if id = id1 then 0 else 1 + idx id xs

let rec total_order (l:list (pos * string) {unique_s l}) : prop =
  match l with
  |[] -> true
  |[x] -> true
  |x::xs ->  (forall e. L.mem e xs ==> lt (fst e) (fst x)) /\  total_order xs

let ord (id:(pos * string)) (id1:(pos * string) {fst id <> fst id1})
        (l:list (pos * string) {L.mem id l /\ L.mem id1 l /\ unique_s l /\ total_order l})
        : Tot (b:bool {b = true <==> idx id l < idx id1 l})
    = idx id l < idx id1 l 
    
// the concrete state type
// It is a sequence of pairs of timestamp and message.
// As the sequence is sorted based on timestamps we ignore the message
type concrete_st = l:list (pos & string){unique_s l /\ total_order l}

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

let do_pre (s:concrete_st) (op:op_t) =
  (forall id. mem_id_s id s ==> id < fst op)

// apply an operation to a state
let do (s:concrete_st) (op:op_t{do_pre s op}) 
  : (r:concrete_st{(forall e. L.mem e r <==> (L.mem e s \/ e = op))}) =
  (fst op, snd op)::s 
 
let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b /\ do_pre a op)
           (ensures eq (do a op) (do b op)) = ()

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res =
  if lt (fst y) (fst x) then First_then_second else Second_then_first

let rec remove_ele (ele:(pos * string)) (a:concrete_st)
  : Pure concrete_st
    (requires (L.mem ele a))
    (ensures (fun r -> (forall e. L.mem e r <==> L.mem e a /\ e <> ele) /\ not (mem_id_s (fst ele) r) /\
                    (forall id. mem_id_s id r <==> mem_id_s id a /\ id <> fst ele) /\
                    (forall e e1. L.mem e r /\ L.mem e1 r /\ ord e e1 r /\ fst e > fst e1 <==>
                    L.mem e a /\ L.mem e1 a /\ e <> ele /\ e1 <> ele /\ lt (fst e1) (fst e) /\ ord e e1 a))) =
  match a with
  |ele1::xs -> if ele = ele1 then xs else ele1::(remove_ele ele xs)


#push-options "--z3rlimit 100 --fuel 1"
let rec union_s (a:concrete_st) (b:concrete_st)
  : Pure concrete_st
    (requires (forall id. mem_id_s id a ==> not (mem_id_s id b)))
    (ensures (fun u -> (forall e. L.mem e u <==> L.mem e a \/ L.mem e b)/\
                    (forall e e1. ((L.mem e a /\ L.mem e1 a /\ lt (fst e1) (fst e) /\ ord e e1 a) \/
                              (L.mem e b /\ L.mem e1 b /\ lt (fst e1) (fst e) /\ ord e e1 b) \/
                              (L.mem e a /\ L.mem e1 b /\ lt (fst e1) (fst e)) \/
                              (L.mem e b /\ L.mem e1 a /\ lt (fst e1) (fst e))) <==>
                              (L.mem e u /\ L.mem e1 u /\ lt (fst e1) (fst e) /\ ord e e1 u)) /\
                              (forall id. mem_id_s id u <==> mem_id_s id a \/ mem_id_s id b))) =
  match a, b with
  |[], [] -> []
  |[], _ -> b
  |_, [] -> a
  |h1::t1, h2::t2 -> if lt (fst h2) (fst h1) then h1::(union_s t1 b) else h2::(union_s a t2)
#pop-options

//s1 - s2
let rec diff_s (s1 s2:concrete_st) 
  : Tot (d:concrete_st{(forall e. L.mem e d <==> L.mem e s1 /\ not (L.mem e s2))}) (decreases %[s1;s2]) =
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

// concrete merge pre-condition
let merge_pre l a b = 
  (forall id. mem_id_s id l ==> not (mem_id_s id (diff_s a l)) /\ not (mem_id_s id (diff_s b l))) /\ 
  (forall id. mem_id_s id (diff_s a l) ==> not (mem_id_s id (diff_s b l)))
 
#push-options "--z3rlimit 100"
let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{merge_pre lca s1 s2}) 
  : (r:concrete_st {(forall e. L.mem e r <==> (L.mem e lca \/ L.mem e s1 \/ L.mem e s2)) /\
                    (forall id. mem_id_s id r <==> (mem_id_s id lca \/ mem_id_s id s1 \/ mem_id_s id s2)) /\
                    (forall e e1. (L.mem e r /\ L.mem e1 r /\ fst e > fst e1 /\ ord e e1 r) <==>
                             ((L.mem e lca /\ L.mem e1 lca /\ fst e > fst e1 /\ ord e e1 lca) \/
                       (L.mem e (diff_s s1 lca) /\ L.mem e1 (diff_s s1 lca) /\ lt (fst e1) (fst e) /\ ord e e1 (diff_s s1 lca)) \/
                       (L.mem e (diff_s s2 lca) /\ L.mem e1 (diff_s s2 lca) /\ lt (fst e1) (fst e) /\ ord e e1 (diff_s s2 lca)) \/
                       (L.mem e (diff_s s1 lca) /\ L.mem e1 (diff_s s2 lca) /\ lt (fst e1) (fst e)) \/
                       (L.mem e (diff_s s2 lca) /\ L.mem e1 (diff_s s1 lca) /\ lt (fst e1) (fst e)) \/
                       (L.mem e (diff_s s1 lca) /\ L.mem e1 lca /\ lt (fst e1) (fst e)) \/
                       (L.mem e (diff_s s2 lca) /\ L.mem e1 lca /\ lt (fst e1) (fst e)) \/
                       (L.mem e lca /\ L.mem e1 (diff_s s1 lca) /\ lt (fst e1) (fst e)) \/
                       (L.mem e lca /\ L.mem e1 (diff_s s2 lca) /\ lt (fst e1) (fst e))))}) = 
  let la = diff_s s1 lca in
  let lb = diff_s s2 lca in
  let u = union_s la lb in 
  let r = union_s u lca in 
  r

let rec lem_equal (a b:concrete_st) 
  : Lemma (requires (forall e. L.mem e a <==> L.mem e b))  
          (ensures (List.Tot.length a = List.Tot.length b) /\
                   (a = b)) =
  let rec lem_len (a b:concrete_st) 
    : Lemma (requires (forall e. L.mem e a <==> L.mem e b))
            (ensures (List.Tot.length a = List.Tot.length b)) =
  begin
  match a,b with
  |[],[] -> ()
  |x::xs,_ -> lem_len xs (remove_ele x b)
  |[],_ -> ()
  end in

  
  begin 
  lem_len a b;
  match a,b with
  |[],[] -> ()
  |x::xs, y::ys -> lem_equal xs ys
  end

// Prove that merge is commutative
let merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
          (ensures merge_pre (v_of lca) (v_of s2) (v_of s1) /\
                   (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) =
  lem_equal (concrete_merge (v_of lca) (v_of s1) (v_of s2))
             (concrete_merge (v_of lca) (v_of s2) (v_of s1))           
                       
let linearizable_s1_0''_base_base (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) = 0 /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) =
  lem_equal (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))

let linearizable_s1_0''_base_do_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\ 
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    fst last2 > 0 /\
                    length (ops_of s2') > 0)
          (ensures do_pre (v_of (inverse_st s2')) last2) = ()

let linearizable_s1_0''_base_merge_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\ 
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 == ops_of lca /\ ops_of s2' == ops_of lca /\
                    fst last2 > 0 /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    length (ops_of s2') > 0 /\
                    do_pre (v_of (inverse_st s2')) last2)

          (ensures (let l' = inverse_st lca in
                    merge_pre (v_of l') (v_of l') (do (v_of l') last2))) = ()

let linearizable_s1_0''_base_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2' = ops_of lca /\
                    length (ops_of lca) > 0 /\

                    (let l' = inverse_st lca in
                    let s1' = inverse_st s1 in
                    let s2'' = inverse_st s2' in
                    do_pre (v_of s2'') last2 /\ 
                    consistent_branches l' s1' (do_st s2'' last2) /\
                    ops_of s1' = ops_of l' /\ ops_of s2'' = ops_of l' /\
                    merge_pre (v_of l') (v_of s1') (do (v_of s2'') last2) /\
                    eq (do (v_of s2'') last2) (concrete_merge (v_of l') (v_of s1') (do (v_of s2'') last2))) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))

          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) =
  lem_equal (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))

let linearizable_s1_0''_do_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    ops_of s1 = ops_of lca /\                    
                    fst last2 > 0 /\
                    length (ops_of s2') > length (ops_of lca))
         
          (ensures do_pre (v_of (inverse_st s2')) last2) = ()

let linearizable_s1_0''_merge_pre (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    do_pre (v_of inv2) last2 /\
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2)))
         
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of (inverse_st s2')) last2)) = ()

let linearizable_s1_0''_ind (lca s1 s2':st) (last2:op_t)
  : Lemma (requires do_pre (v_of s2') last2 /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    ops_of s1 = ops_of lca /\
                    length (ops_of s2') > length (ops_of lca) /\

                    (let inv2 = inverse_st s2' in
                    do_pre (v_of inv2) last2 /\
                    consistent_branches lca s1 (do_st inv2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of inv2) last2) /\
                    eq (do (v_of inv2) last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of inv2) last2))) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2))
        
          (ensures eq (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))) =
  lem_equal (do (v_of s2') last2) (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2))

let linearizable_s1_0_s2_0_base (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca /\ ops_of s2 == ops_of lca /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2))
        
          (ensures eq (v_of lca) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_gt0_base_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    First_then_second? (resolve_conflict last1 last2))
         
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) = 
  lem_equal (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
            (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))

let linearizable_gt0_base_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    Second_then_first? (resolve_conflict last1 last2))
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) =
  lem_equal (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
            (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))

let linearizable_gt0_base (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
         
          (ensures (First_then_second? (resolve_conflict last1 last2) ==>
                      merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                      do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                      (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   (Second_then_first? (resolve_conflict last1 last2) ==>
                      merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                      do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                      (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                          (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))) = 
  if First_then_second? (resolve_conflict last1 last2) then
    linearizable_gt0_base_fts lca s1 s2 last1 last2
  else linearizable_gt0_base_stf lca s1 s2 last1 last2

let linearizable_gt0_s2'_do_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2)) 
         
          (ensures (length (ops_of s2) > length (ops_of lca) ==> do_pre (v_of (inverse_st s2)) last2) /\
                   (length (ops_of s1) > length (ops_of lca) ==> do_pre (v_of (inverse_st s1)) last1)) = ()

let linearizable_gt0_s2'_merge_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)) 
         
          (ensures (length (ops_of s1) > length (ops_of lca) /\ do_pre (v_of (inverse_st s1)) last1 ==>
                      merge_pre (v_of lca) (do (v_of (inverse_st s1)) last1) (do (v_of s2) last2)) /\
                   (length (ops_of s2) > length (ops_of lca) /\ do_pre (v_of (inverse_st s2)) last2 ==>
                      merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of (inverse_st s2)) last2))) = ()

let linearizable_gt0_s1'_do_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2)) 
          (ensures (length (ops_of s2) > length (ops_of lca) ==> do_pre (v_of (inverse_st s2)) last2) /\
                   (length (ops_of s1) > length (ops_of lca) ==> do_pre (v_of (inverse_st s1)) last1)) = ()

let linearizable_gt0_s1'_merge_pre (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    fst last1 <> fst last2 /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
          (ensures (length (ops_of s1) > length (ops_of lca) /\ do_pre (v_of (inverse_st s1)) last1 ==>
                      merge_pre (v_of lca) (do (v_of (inverse_st s1)) last1) (do (v_of s2) last2)) /\
                   (length (ops_of s2) > length (ops_of lca) /\ do_pre (v_of (inverse_st s2)) last2 ==>
                      merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of (inverse_st s2)) last2))) = ()

let linearizable_gt0_ind_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s2' = inverse_st s2 in
                    do_pre (v_of s2') last2 /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2)))) 
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] = 
  lem_equal (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
            (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
                    
let linearizable_gt0_ind_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s2' = inverse_st s2 in
                    do_pre (v_of s2') last2 /\
                    ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2') /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))))
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] =
  lem_equal (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
            (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))

let linearizable_gt0_ind1_fts (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    (let s1' = inverse_st s1 in
                    do_pre (v_of s1') last1 /\
                    ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1' (do_st s2 last2) /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1') (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)))) 
          (ensures merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                   do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                   eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))
          [SMTPat (eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] =
  lem_equal (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
            (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))

let linearizable_gt0_ind1_stf (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2) /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    (let s1' = inverse_st s1 in
                    do_pre (v_of s1') last1 /\
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))))
          (ensures merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                   do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\    
                   eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))) 
          [SMTPat (eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                      (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))] =
  lem_equal (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
            (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))

#push-options "--z3rlimit 50"
let linearizable_gt0_ind (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s2) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
       
          (ensures (let s2' = inverse_st s2 in
                   do_pre (v_of s2') last2 /\
                   ((First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1 (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1) (do (v_of s2') last2) /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                     do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                     eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\
                          
                   ((ops_of s1 = ops_of lca /\
                    Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1 last1) s2' /\
                    consistent_branches lca (do_st s1 last1) (do_st s2' last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2') /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2) /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2') last2))) ==>
                   
                    (merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                     do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\
                     eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                        (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))))) = ()

#push-options "--z3rlimit 100"
let linearizable_gt0_ind1 (lca s1 s2:st) (last1 last2:op_t)
  : Lemma (requires do_pre (v_of s1) last1 /\ do_pre (v_of s2) last2 /\ 
                    consistent_branches lca (do_st s1 last1) (do_st s2 last2) /\
                    consistent_branches lca s1 s2 /\
                    length (ops_of s1) > length (ops_of lca) /\
                    fst last1 <> fst last2 /\
                    merge_pre (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))
                           
          (ensures (let s1' = inverse_st s1 in
                   do_pre (v_of s1') last1 /\
                   ((ops_of s2 = ops_of lca /\
                    First_then_second? (resolve_conflict last1 last2) /\
                    consistent_branches lca s1' (do_st s2 last2) /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca s1 (do_st s2 last2) /\
                    merge_pre (v_of lca) (v_of s1') (do (v_of s2) last2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2))) ==>
                       
                   (merge_pre (v_of lca) (v_of s1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2)))) /\

                   ((Second_then_first? (resolve_conflict last1 last2) /\
                    consistent_branches lca (do_st s1' last1) s2 /\
                    consistent_branches lca (do_st s1' last1) (do_st s2 last2) /\
                    consistent_branches lca (do_st s1 last1) s2 /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (v_of s2) /\
                    merge_pre (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2) /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2 /\
                    eq (do (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (do (v_of s2) last2)) ==>
                
                   (merge_pre (v_of lca) (do (v_of s1) last1) (v_of s2) /\
                    do_pre (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2 /\  
                    eq (do (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (do (v_of s2) last2))))))) = ()
                       
let fts_merge_pre (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in 
                     let _, last2 = un_snoc (ops_of s2) in 
                     fst last1 <> fst last2 /\
                     First_then_second? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) = ()
   
let stf_merge_pre (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     Second_then_first? (resolve_conflict last1 last2)))
          (ensures merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
let concrete_st_s = concrete_st

// init state 
let init_st_s = init_st

let do_pre_s (st_s:concrete_st_s) (o:op_t) = do_pre st_s o

// apply an operation to a state 
let do_s (st_s:concrete_st_s) (o:op_t{do_pre_s st_s o}) = do st_s o

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = eq st_s st

//initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st /\ do_pre st op)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////
//// Linearization properties //////

let conv_prop1 (lca s1 s2:concrete_st) (op1 op2:op_t)
  : Lemma (requires do_pre s1 op1 /\ do_pre s2 op2 /\
                    merge_pre lca s1 (do s2 op2) /\
                    do_pre (concrete_merge lca s1 (do s2 op2)) op1 /\
                    merge_pre lca (do s1 op1) (do s2 op2) /\
                    fst op1 <> fst op2 /\ resolve_conflict op1 op2 = First_then_second)
          (ensures eq (concrete_merge lca (do s1 op1) (do s2 op2)) (do (concrete_merge lca s1 (do s2 op2)) op1)) = 
  lem_equal (concrete_merge lca (do s1 op1) (do s2 op2)) (do (concrete_merge lca s1 (do s2 op2)) op1)

let conv_prop2 (lca s1 s2:concrete_st) (op1 op2:op_t)
  : Lemma (requires do_pre s1 op1 /\ do_pre s2 op2 /\
                    merge_pre lca (do s1 op1) s2 /\
                    do_pre (concrete_merge lca (do s1 op1) s2) op2 /\
                    merge_pre lca (do s1 op1) (do s2 op2) /\
                    fst op1 <> fst op2 /\ resolve_conflict op1 op2 = Second_then_first)
          (ensures eq (concrete_merge lca (do s1 op1) (do s2 op2)) (do (concrete_merge lca (do s1 op1) s2) op2)) = 
  lem_equal (concrete_merge lca (do s1 op1) (do s2 op2)) (do (concrete_merge lca (do s1 op1) s2) op2)

let conv_prop3 (s:concrete_st)
  : Lemma (eq (concrete_merge s s s) s) = ()

let conv_prop4 (lca s1 s2:concrete_st) (op:op_t)
  : Lemma (requires do_pre s1 op /\ do_pre s2 op /\
                    merge_pre lca s1 s2 /\
                    merge_pre lca (do s1 op) (do s2 op) /\
                    do_pre (concrete_merge lca s1 s2) op)
          (ensures eq (concrete_merge lca (do s1 op) (do s2 op)) (do (concrete_merge lca s1 s2) op)) = ()

////////////////////////////////////////////////////////////////
//// Linearization properties - intermediate merge //////

let inter_prop1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ fst o1 <> fst o2 /\ 
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second /\
                    do_pre l o1 /\ do_pre l o3 /\ do_pre (do l o1) o2 /\ do_pre (do l o3) o1 /\ do_pre (do (do l o3) o1) o2 /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do l o3) o1))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = 
  lem_equal (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)

let inter_prop2 (s s':concrete_st) (o1 o2:op_t) 
  : Lemma (requires fst o1 <> fst o2 /\ do_pre s o1 /\ do_pre s o2 /\ do_pre s' o2 /\ do_pre s' o1 /\ 
                    do_pre (do s o1) o2 /\ do_pre (do s' o1) o2 /\
                    merge_pre s (do s o2) s' /\
                    merge_pre (do s o1) (do (do s o1) o2) (do s' o1) /\
                    eq (concrete_merge s (do s o2) s') (do s' o2))
          (ensures eq (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = 
  lem_equal (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)

let inter_prop3 (l a b c:concrete_st) (op op':op_t)
  : Lemma (requires fst op <> fst op' /\ merge_pre l a b /\ eq (concrete_merge l a b) c /\ 
                    do_pre b op /\ do_pre c op /\ do_pre (do b op) op' /\ do_pre (do c op) op' /\
                    merge_pre l a (do (do b op) op') /\
                    (forall (o:op_t). do_pre b o /\ do_pre c o /\ merge_pre l a (do b o) ==>
                                 eq (concrete_merge l a (do b o)) (do c o)))
          (ensures eq (concrete_merge l a (do (do b op) op')) (do (do c op) op')) = 
  lem_equal (concrete_merge l a (do (do b op) op')) (do (do c op) op')

let inter_prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o2 /\ fst o1 <> fst o3' /\
                    fst o2 <> fst o3 /\ fst o2 <> fst o3' /\ fst o3 <> fst o3' /\
                    do_pre l o1 /\ do_pre s o3 /\ do_pre (do l o1) o2 /\ do_pre (do s o3) o1 /\ do_pre (do (do s o3) o1) o2 /\
                    do_pre s o3' /\ do_pre (do s o3') o3 /\ do_pre (do (do s o3') o3) o1 /\
                    do_pre (do (do (do s o3') o3) o1) o2 /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1) /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do s o3) o1) /\
                    resolve_conflict o1 o3 = First_then_second /\
                    resolve_conflict o2 o3 = First_then_second /\
                    eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                      (do (do (do (do s o3') o3) o1) o2)) = 
  lem_equal (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
            (do (do (do (do s o3') o3) o1) o2)

////////////////////////////////////////////////////////////////
//// Recursive merge condition //////

let rec_merge (s si si' sn sn':concrete_st)
  : Lemma (requires merge_pre s sn sn' /\ merge_pre s sn si' /\ merge_pre s si sn' /\ merge_pre s si' sn /\
                    merge_pre s si si' /\ merge_pre s si' si /\ 
                    merge_pre si sn (concrete_merge s si si') /\ merge_pre si' sn' (concrete_merge s si' si) /\
                    merge_pre (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn) /\
                    merge_pre si sn (concrete_merge s si sn') /\ merge_pre si' sn' (concrete_merge s sn si') /\
                    
                    eq (concrete_merge s sn sn') (concrete_merge si sn (concrete_merge s si sn')) /\
                    eq (concrete_merge s sn sn') (concrete_merge si' sn' (concrete_merge s sn si')) /\
                    eq (concrete_merge s sn si') (concrete_merge si sn (concrete_merge s si si')) /\
                    eq (concrete_merge s si sn') (concrete_merge si' sn' (concrete_merge s si' si)))         
          (ensures (eq (concrete_merge s sn sn')
                       (concrete_merge (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn)))) = 
  lem_equal (concrete_merge s sn sn')
            (concrete_merge (concrete_merge s si si') (concrete_merge s si sn') (concrete_merge s si' sn))
          
////////////////////////////////////////////////////////////////
