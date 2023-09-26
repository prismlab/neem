module App

open FStar.Seq
open FStar.Ghost
module L = FStar.List.Tot

#set-options "--query_stats"
// the concrete state type
type concrete_st:eqtype = list nat

// init state
let init_st = []

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  (forall ele. L.mem ele a <==> L.mem ele b)

// few properties of equivalence relation
let symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a) = ()

let transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c) = ()

let eq_is_equiv (a b:concrete_st)
  : Lemma (requires a = b)
          (ensures eq a b) = ()

// operation type
type op_t:eqtype = nat

// apply an operation to a state
let do (s:concrete_st) (op:log_entry)
    : (r:concrete_st{(forall e. L.mem e r <==> L.mem e s \/ e = snd op)}) =
  if (L.mem (snd op) s) then s else (snd op)::s

(*let do_prop (s:concrete_st) (o:log_entry)
  : Lemma (ensures (forall e. L.mem e (do s o) <==> L.mem e s \/ e = snd o)) = ()*)

let lem_do (a b:concrete_st) (op:log_entry)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = ()
           
////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
let concrete_st_s = list nat

// init state 
let init_st_s = []

val filter_seq : f:(nat -> bool)
               -> l:concrete_st_s
               -> Tot (l1:concrete_st_s {(forall e. L.mem e l1 <==> L.mem e l /\ f e)})
let rec filter_seq f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter_seq f tl) else filter_seq f tl
  
// apply an operation to a state 
let do_s (st_s:concrete_st_s) (o:log_entry) 
  : (r:concrete_st_s{(forall e. L.mem e r <==> L.mem e st_s \/ e = snd o)}) =
  (snd o)::st_s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  (forall e. L.mem e st_s <==> L.mem e st)

//initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op)) = ()

////////////////////////////////////////////////////////////////

val exists_op : f:(log_entry -> bool)
              -> l:log
              -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true}) (decreases length l)
let rec exists_op f l =
  match length l with
  | 0 -> false
  | _ -> if f (head l) then true else exists_op f (tail l)

val forall_op : f:(log_entry -> bool)
              -> l:log
              -> Tot (b:bool{(forall e. mem e l ==> f e) <==> b = true}) (decreases length l)
let rec forall_op f l =
  match length l with
  | 0 -> true
  | _ -> f (head l) && forall_op f (tail l)

let rec mem_ele (e:nat) (l:log) : Tot bool (decreases length l) =
  match length l with
  |0 -> false
  |_ -> snd (head l) = e || mem_ele e (tail l)

//conflict resolution
let resolve_conflict (x:log_entry) (y:log_entry{fst x <> fst y}) 
  : (l:log{Seq.length l = 1 \/ Seq.length l = 2 /\ length l = 2 /\ last l <> x}) =
  cons x (cons y empty)

let resolve_conflict_prop (x y:log_entry) 
  : Lemma (requires fst x <> fst y)
          (ensures Seq.length (resolve_conflict x y) = 2 /\
                   (last (resolve_conflict x y) <> x))
  = ()

// remove ele from l
let rec remove (l:concrete_st) (ele:nat)
  : Tot (res:concrete_st{(forall e. L.mem e res <==> L.mem e l /\ e <> ele) /\ not (L.mem ele res)}) =
  match l with
  |[] -> []
  |x::xs -> if x = ele then (remove xs ele) else x::remove xs ele

val filter : f:(nat -> bool)
           -> l:concrete_st
           -> Tot (l1:concrete_st {(forall e. L.mem e l /\ f e <==> L.mem e l1)})
let rec filter f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter f tl) else filter f tl
  
let diff_s (a l:concrete_st)
  : Pure (concrete_st) 
    (requires true)
    (ensures (fun d -> (forall e. L.mem e d <==> (L.mem e a /\ not (L.mem e l)))))  (decreases a) =
  filter (fun e -> not (L.mem e l)) a
  
#push-options "--z3rlimit 200"
val concrete_merge1 (l a b:concrete_st)
           : Pure concrete_st
             (requires true)
             (ensures (fun res -> (forall e. L.mem e res <==> (L.mem e l /\ L.mem e a /\ L.mem e b) \/ 
                                                    (L.mem e (diff_s a l)) \/ (L.mem e (diff_s b l)))))
                               (decreases %[l;a;b])
let rec concrete_merge1 l a b =
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> if (L.mem x a && L.mem x b) then x::(concrete_merge1 xs (remove a x) (remove b x)) 
                 else if (L.mem x a) then (concrete_merge1 xs (remove a x) b)
                   else if (L.mem x b) then (concrete_merge1 xs a (remove b x))
                     else (concrete_merge1 xs a b)
  |[],x::xs,_ -> x::(concrete_merge1 [] xs b)
  |[],[],x::xs -> b

// concrete merge operation
let concrete_merge (l a b:concrete_st)
    : Tot (res:concrete_st {(forall e. L.mem e res <==> (L.mem e l /\ L.mem e a /\ L.mem e b) \/ 
                                                 (L.mem e (diff_s a l)) \/ (L.mem e (diff_s b l))) /\
                            (l = a ==> (forall e. L.mem e res <==> L.mem e b)) /\
                            (l = b ==> (forall e. L.mem e res <==> L.mem e a))}) =
 concrete_merge1 l a b

#push-options "--z3rlimit 500"
let linearizable_s1_0_base (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_s1_0_ind (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    length (ops_of s2) > length (ops_of lca) /\
                    (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    eq (v_of s2') (concrete_merge (v_of lca) (v_of s1) (v_of s2'))))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_s2_0_base (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_s2_0_ind (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s2 = ops_of lca /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    length (ops_of s1) > length (ops_of lca) /\
                    (let s1' = inverse_st s1 in
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    eq (v_of s1') (concrete_merge (v_of lca) (v_of s1') (v_of s2))))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()




let linearizable_gt0_s2'_base (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))) = ()

let linearizable_gt0_s2'_s10_ind (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    length (ops_of s2) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))) /\
                    
                    (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                                      
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))) = ()

let linearizable_gt0_s2'_s10_base (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))) = ()

let linearizable_gt0_s2'_s1_gt0_ind (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires length (ops_of s1) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last2)) /\
                    not (mem_id (fst last2) (diff (ops_of s1) (ops_of lca))) /\
                    
                    (let s1' = inverse_st s1 in
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    not (mem_id (fst last2) (diff (ops_of s1') (ops_of lca))) /\
                    
                    (eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last2)
                        (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))) = ()

///////////////////////////

let linearizable_gt0_s1'_base (lca s1 s2:st) (last1:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    not (mem_id (fst last1) (diff (ops_of s2) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)))) = ()

let linearizable_gt0_s1'_s20_base (lca s1 s2:st) (last1:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    not (mem_id (fst last1) (diff (ops_of s2) (ops_of lca))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)))) = ()

let linearizable_gt0_s1'_s20_ind (lca s1 s2:st) (last1:log_entry)
  : Lemma (requires ops_of s2 = ops_of lca /\
                    length (ops_of s1) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    not (mem_id (fst last1) (diff (ops_of s2) (ops_of lca))) /\
                    
                    (let s1' = inverse_st s1 in
                    is_prefix (ops_of lca) (ops_of s1') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                                      
                    (eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1') last1) (v_of s2)))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)))) = ()

let linearizable_gt0_s1'_s2_gt0_ind (lca s1 s2:st) (last1:log_entry)
  : Lemma (requires length (ops_of s2) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (forall id. mem_id id (ops_of lca) ==> lt id (fst last1)) /\
                    not (mem_id (fst last1) (diff (ops_of s2) (ops_of lca))) /\
                    
                    (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca)))) /\
                    not (mem_id (fst last1) (diff (ops_of s2') (ops_of lca))) /\
                    
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2')))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (do (v_of s1) last1) (v_of s2)))) = ()
                       
////////////////////////////////////////////

(*let linearizable_gt0_inv2'_base (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\ ops_of s2 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))) = ()

let linearizable_gt0_inv2'_s10_ind (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    length (ops_of s2) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    (let s2' = inverse_st s2 in
                    (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') last2)))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))) = ()

let rec linearizable_gt0_inv2'_s10 (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires ops_of s1 = ops_of lca /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))))
          (decreases length (ops_of s2)) =
  if ops_of s2 = ops_of lca then ()
  else (let s2' = inverse_st s2 in
        linearizable_gt0_inv2'_s10 lca s1 s2' last2;
        linearizable_gt0_inv2'_s10_ind lca s1 s2 last2)

let linearizable_gt0_inv2'_s1_gt0_ind (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires length (ops_of s1) > length (ops_of lca) /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    not (mem_id (fst last2) (ops_of lca)) /\
                    (let s1' = inverse_st s1 in
                    (eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1') (do (v_of s2) last2)))))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2)))) = ()

let rec linearizable_gt0_inv2' (lca s1 s2:st) (last2:log_entry)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    not (mem_id (fst last2) (ops_of lca)))
          (ensures (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2)) last2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2) last2))))
          (decreases length (ops_of s1)) =
  if ops_of s1 = ops_of lca && ops_of s2 = ops_of lca then
    linearizable_gt0_inv2'_base lca s1 s2 last2
  else if ops_of s1 = ops_of lca then
    linearizable_gt0_inv2'_s10 lca s1 s2 last2
  else (let s1' = inverse_st s1 in
        linearizable_gt0_inv2' lca s1' s2 last2;
        linearizable_gt0_inv2'_s1_gt0_ind lca s1 s2 last2)

let rec mem_ele_id (op:log_entry) (l:log)
  : Lemma (requires mem op l)
          (ensures mem_id (fst op) l) (decreases length l) =
  if head l = op then ()
    else mem_ele_id op (tail l)
    
let lem_suf_equal2_last (lca s1:log)
  : Lemma (requires is_prefix lca s1 /\ length (diff s1 lca) > 0 /\ distinct_ops s1)
          (ensures (let _, lastop = un_snoc s1 in
                    not (mem_id (fst lastop) lca))) =
    distinct_invert_append lca (diff s1 lca); 
    let pre, lst = un_snoc s1 in
    lem_diff s1 lca;
    mem_ele_id lst (diff s1 lca)
    
let linearizable_gt0_inv2 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    fst last1 <> fst last2 /\
                    last (resolve_conflict last1 last2) <> last1 /\
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = 
  lem_inverse (ops_of lca) (ops_of s2);
  lem_suf_equal2_last (ops_of lca) (ops_of s2); 
  let _, last2 = un_snoc (ops_of s2) in
  linearizable_gt0_inv2' lca s1 (inverse_st s2) last2
                         
let linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\ 
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
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
                      eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                      eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) = admit()*)
  
