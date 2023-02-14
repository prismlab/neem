module App_weak

open FStar.Seq
open FStar.Ghost
module L = FStar.List.Tot

#set-options "--query_stats"

val mem_id_s : id:nat 
             -> l:list (nat * nat)
             -> Tot (b:bool{(exists n. L.mem (id,n) l) <==> b=true})
let rec mem_id_s n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || mem_id_s n xs

val mem_ele : ele:nat 
             -> l:list (nat * nat)
             -> Tot (b:bool{(exists n. L.mem (n,ele) l) <==> b=true})
let rec mem_ele ele l =
  match l with
  |[] -> false
  |(_,ele1)::xs -> (ele = ele1) || mem_ele ele xs

val unique_s : l:list (nat * nat)
             -> Tot bool
let rec unique_s l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (mem_id_s id xs) && unique_s xs
  
// the concrete state type
type concrete_st:eqtype = l:list (nat (*unique id*) * nat (*element*)) {unique_s l}

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
type op_t:eqtype =
  |Add : nat -> op_t
  |Rem : nat -> op_t

let get_ele (o:log_entry) : nat =
  match snd o with
  |Add e -> e
  |Rem e -> e

let rec mem_id_ele_l (id:nat) (ele:nat) (l:log) 
  : Tot (b:bool{b = true <==> (exists e. mem e l /\ fst e = id /\ get_ele e = ele)}) (decreases length l) =
  match length l with
  |0 -> false
  |_ -> (fst (head l) = id && get_ele (head l) = ele) || mem_id_ele_l id ele (tail l)

val filter : f:((nat * nat) -> bool)
           -> l:concrete_st
           -> Tot (l1:concrete_st {(forall e. L.mem e l1 /\ mem_id_s (fst e) l1 <==> L.mem e l /\ mem_id_s (fst e) l /\ f e)})
let rec filter f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter f tl) else filter f tl

// concrete do pre-condition
let concrete_do_pre (s:concrete_st) (op:log_entry) : prop =
  ~ (mem_id_s (fst op) s)

// apply an operation to a state
let do (s:concrete_st) (o:log_entry{concrete_do_pre s o}) 
    : (r:concrete_st{(Add? (snd o) ==> (forall ele. mem_ele ele r <==> (mem_ele ele s \/ ele = get_ele o)) /\
                                      (forall e. L.mem e r <==> (L.mem e s \/ (e = (fst o, get_ele o)))) /\
                                      (forall e. L.mem e s <==> (L.mem e r /\ (e <> (fst o, get_ele o)))) /\
                                      (forall id. mem_id_s id r <==> (mem_id_s id s \/ id = fst o)) /\
                                      (forall id. mem_id_s id s <==> (mem_id_s id r /\ id <> fst o)) /\
                                      (forall e. L.mem e r /\ snd e <> get_ele o <==> L.mem e s /\ snd e <> get_ele o)) /\
                     (Rem? (snd o) ==> (forall ele. mem_ele ele r <==> (mem_ele ele s /\ ele <> get_ele o)) /\
                                      (forall e. L.mem e r <==> (L.mem e s /\ snd e <> get_ele o)) /\
                                      (forall id. mem_id_s id r ==> mem_id_s id s) /\
                                      not (mem_ele (get_ele o) r))}) =
  match o with
  |(id, Add e) -> (id, e)::s
  |(id, Rem e) -> filter (fun ele -> snd ele <> e) s

let do_prop (s:concrete_st) (o:log_entry{concrete_do_pre s o}) 
  : Lemma (ensures (Add? (snd o) ==> ((forall ele. mem_ele ele (do s o) <==> (mem_ele ele s \/ ele = get_ele o)) /\
                                     (forall e. L.mem e (do s o) <==> (L.mem e s \/ e = (fst o, get_ele o))) /\
                                     (forall e. L.mem e s <==> (L.mem e (do s o) /\ e <> (fst o, get_ele o))) /\
                                     (forall id. mem_id_s id (do s o) <==> (mem_id_s id s \/ id = fst o)) /\
                                     (forall id. mem_id_s id s <==> (mem_id_s id (do s o) /\ id <> fst o)) /\
                                     L.mem (fst o, get_ele o) (do s o) /\
                                    (forall e. L.mem e (do s o) /\ snd e <> get_ele o <==> L.mem e s /\ snd e <> get_ele o))) /\
                   (Rem? (snd o) ==> ((forall e. L.mem e (do s o) <==> (L.mem e s /\ snd e <> get_ele o)) /\
                                     not (mem_ele (get_ele o) (do s o)) /\
                                    (forall id. mem_id_s id (do s o) ==> mem_id_s id s)))) = ()

let lem_mem_id (i a:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. L.mem e i \/ e = ele <==> L.mem e a))
          (ensures (forall id. mem_id_s id i \/ id = fst ele <==> mem_id_s id a)) = ()

let do_prop_inv (s:concrete_st) (o:log_entry{concrete_do_pre s o}) 
  : Lemma (ensures (Add? (snd o) ==> (forall id. mem_id_s id (do s o) <==> (mem_id_s id s \/ id = fst o)))) = ()
                                    
let lem_do (a b:concrete_st) (op:log_entry)
   : Lemma (requires concrete_do_pre a op /\ eq a b)
           (ensures concrete_do_pre b op /\ eq (do a op) (do b op)) = ()
           
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
  : (r:concrete_st_s{(Add? (snd o) ==> (forall e. L.mem e r <==> L.mem e st_s \/ e = get_ele o)) /\
                     (Rem? (snd o) ==> (forall e. L.mem e r <==> L.mem e st_s /\ e <> get_ele o))}) =
  match snd o with
  |(Add e) -> e::st_s
  |(Rem e) -> filter_seq (fun ele -> ele <> e) st_s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) =
  (forall e. L.mem e st_s <==> mem_ele e st)

//initial states are equivalent
let initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq_sm st_s st /\ concrete_do_pre st op)
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

#push-options "--z3rlimit 50"
let rec get_ele_l (l:log{(*distinct_ops l /\*) (forall e. mem e l ==> Add? (snd e))})
  : Tot (r:list (nat * nat){(forall e. L.mem e r <==> mem_id_ele_l (fst e) (snd e) l) /\
                        (forall id. mem_id_s id r <==> mem_id id l)}) (decreases length l) =
  match length l with
  |0 -> []
  |_ -> (fst (head l), get_ele (head l))::get_ele_l (tail l)

#push-options "--z3rlimit 200"
let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires foldl_prop s l)
          (ensures (length l = 0 ==> s = seq_foldl s l) /\
                   (length l > 0 ==> (let p,last = un_snoc l in
                       (foldl_prop s p /\
                       concrete_do_pre (seq_foldl s p) (last) /\
                       (seq_foldl s l = do (seq_foldl s p) (last)) /\
          (Add? (snd last) ==> (forall e. L.mem e (seq_foldl s l) <==> L.mem e (seq_foldl s p) \/ e = (fst last, get_ele last)) /\
                                    L.mem (fst last, get_ele last) (seq_foldl s l)) /\
          (Rem? (snd last) ==> (forall e. L.mem e (seq_foldl s l) <==> L.mem e (seq_foldl s p) /\ snd e <> get_ele last) /\
                              (forall id. mem_id_s id (seq_foldl s p) ==> mem_id_s id s \/ mem_id id l))))) /\
          (forall id. mem_id_s id (seq_foldl s l) ==> mem_id_s id s \/ mem_id id l))
          (decreases length l)
  = match length l with
    |0 -> ()
    |1 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)

let rec lem_foldl_not_ele (s:concrete_st) (l:log) (ele:nat)
  : Lemma (requires foldl_prop s l /\ ~ (exists op. mem op l /\ get_ele op = ele))
          (ensures (forall e. L.mem e s /\ snd e = ele <==> L.mem e (seq_foldl s l) /\ snd e = ele)) 
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> do_prop s (head l); lem_foldl_not_ele (do s (head l)) (tail l) ele

//operations x and y are commutative
let commutative (x y: log_entry) =
  not (((Add? (snd x) && Rem? (snd y) && get_ele x = get_ele y) ||
        (Add? (snd y) && Rem? (snd x) && get_ele x = get_ele y)))
        
let comm_symmetric (x y:log_entry) 
  : Lemma (requires commutative x y)
          (ensures commutative y x)
          [SMTPat (commutative x y)] = ()
          
// if x and y are commutative ops, applying them in any order should give equivalent results
let commutative_prop (x y:log_entry) 
  : Lemma (requires commutative x y)
          (ensures (forall s. (foldl_prop s (cons x (cons y empty)) /\ (foldl_prop s (cons y (cons x empty)))) ==>
                         eq (seq_foldl s (cons x (cons y empty))) (seq_foldl s (cons y (cons x empty))))) = ()
                   
//conflict resolution
let resolve_conflict (x y:log_entry) 
  : (l:log{Seq.length l = 2 /\ (forall e. mem e l <==> e = x \/ e = y)}) =
  if (get_ele x = get_ele y && Add? (snd x) && Rem? (snd y)) then 
    cons y (cons x empty) else
      cons x (cons y empty)

let resolve_conflict_prop (x y:log_entry) 
  : Lemma (requires fst x <> fst y)
          (ensures Seq.length (resolve_conflict x y) = 2 /\
                   (last (resolve_conflict x y) = x <==> (Add? (snd x) /\ Rem? (snd y) /\ get_ele x = get_ele y)) /\
                   (last (resolve_conflict x y) <> x <==> last (resolve_conflict x y) = y) /\
                   (last (resolve_conflict x y) = y <==> ((Add? (snd x) /\ Rem? (snd y) /\ get_ele x <> get_ele y) \/
                                                        (Add? (snd x) /\ Add? (snd y)) \/
                                                        (Rem? (snd x) /\ Rem? (snd y)) \/
                                                        (Rem? (snd x) /\ Add? (snd y)))))
  = ()

// remove ele from l
let rec remove (l:concrete_st) (ele:(nat * nat){L.mem ele l})
  : Tot (res:concrete_st{(forall e. L.mem e res <==> L.mem e l /\ e <> ele) /\
                         (forall id. mem_id_s id res <==> mem_id_s id l /\ id <> fst ele) /\ not (mem_id_s (fst ele) res)}) =
  match l with
  |[] -> []
  |x::xs -> if x = ele then xs else x::remove xs ele

// a - l
let rec diff_s (a l:concrete_st)
  : Tot (d:concrete_st{(forall e. L.mem e d <==> (L.mem e a /\ not (L.mem e l))) /\
                       (forall ele. (forall e. L.mem e a /\ snd e = ele <==> L.mem e l /\ snd e = ele) ==>
                               not (mem_ele ele d)) /\
                       (forall ele. not (mem_ele ele a) ==> not (mem_ele ele d)) /\
                       (forall id. mem_id_s id a /\ not (mem_id_s id l) ==> mem_id_s id d)}) (decreases a) =
  match a with
  |[] -> []
  |x::xs -> if L.mem x l then diff_s xs (remove l x) else x::(diff_s xs l)
  
let no_id_not_ele (ele:(nat * nat)) (s:concrete_st)
  : Lemma (requires not (mem_id_s (fst ele) s))
          (ensures not (L.mem ele s)) = ()
          
let lem_diff_st1 (a l:concrete_st) (ele:nat)
  : Lemma (requires (forall e. L.mem e a /\ snd e = ele <==> L.mem e l /\ snd e = ele))
          (ensures not (mem_ele ele (diff_s a l))) = ()

let lem_diff_st2 (a l:concrete_st) (ele:nat)
  : Lemma (requires not (mem_ele ele a))
          (ensures not (mem_ele ele (diff_s a l))) = ()
          
let lemma1 (a b:concrete_st) (ele:(nat * nat))
  : Lemma (requires L.mem ele b /\ (forall e. L.mem e a <==> L.mem e b /\ e <> ele))
          (ensures (forall e. L.mem e a \/ e = ele <==> L.mem e b)) = ()

let lemma2 (a b:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. L.mem e a <==> L.mem e b /\ e <> ele))
          (ensures not (L.mem ele a)) = ()

// concrete merge pre-condition
let concrete_merge_pre (lca a b:concrete_st) : prop =
 (forall id. mem_id_s id (diff_s a lca) ==> not (mem_id_s id b))

let lem_merge_pre (lca a b:concrete_st)
  : Lemma (concrete_merge_pre lca a b <==> 
          (forall id. mem_id_s id (diff_s a lca) ==> not (mem_id_s id b))) = ()

#push-options "--z3rlimit 200"
val concrete_merge1 (l a b:concrete_st)
           : Pure concrete_st
             (requires concrete_merge_pre l a b)
             (ensures (fun res -> (forall e. L.mem e res <==> (L.mem e l /\ L.mem e a /\ L.mem e b) \/ 
                                                    (L.mem e (diff_s a l)) \/ (L.mem e (diff_s b l))) /\
                              (forall id. mem_id_s id res ==> (mem_id_s id l \/ mem_id_s id a \/ mem_id_s id b))))
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
#pop-options

// concrete merge operation
let concrete_merge (l:concrete_st) (a:concrete_st) (b:concrete_st{concrete_merge_pre l a b}) 
    : Tot (res:concrete_st {(forall e. L.mem e res <==> (L.mem e l /\ L.mem e a /\ L.mem e b) \/ 
                                                 (L.mem e (diff_s a l)) \/ (L.mem e (diff_s b l)))})  =
 concrete_merge1 l a b

type common_pre_wo_len (lca s1 s2:st) =
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  //concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))
  
let general_1 (lca s1 s2:st)
  : Lemma (requires common_pre_wo_len lca s1 s2)
          (ensures (forall id. mem_id_s id (diff_s (v_of s1) (v_of lca)) ==> mem_id id (diff (ops_of s1) (ops_of lca))) /\
                   (forall id. mem_id_s id (v_of lca) ==> not (mem_id_s id (diff_s (v_of s1) (v_of lca))))) =
  lem_foldl init_st (ops_of lca);
  assert (forall id. mem_id_s id (v_of lca) ==> mem_id id (ops_of lca));
  
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  assert (forall id. mem_id_s id (v_of s1) ==> mem_id_s id (v_of lca) \/ mem_id id (diff (ops_of s1) (ops_of lca)));

  lt_is_neq (ops_of lca) (ops_of s1);
  assert (forall id. mem_id id (ops_of lca) ==> not (mem_id id (diff (ops_of s1) (ops_of lca))));
  assert (forall id. mem_id_s id (v_of lca) ==> not (mem_id id (diff (ops_of s1) (ops_of lca))));

  assert (forall id. mem_id_s id (v_of s1) /\ not (mem_id_s id (v_of lca)) ==> mem_id id (diff (ops_of s1) (ops_of lca)));
  assume (forall id. mem_id_s id (diff_s (v_of s1) (v_of lca)) <==> (mem_id_s id (v_of s1) /\ not (mem_id_s id (v_of lca)))); //todo
  assert (forall id. mem_id_s id (diff_s (v_of s1) (v_of lca)) ==> mem_id id (diff (ops_of s1) (ops_of lca)));
 
  assert (forall id. mem_id_s id (v_of lca) ==> not (mem_id_s id (diff_s (v_of s1) (v_of lca))));
  ()

let general_2 (lca s1 s2:st)
  : Lemma (requires common_pre_wo_len lca s1 s2)
          (ensures (forall id. mem_id_s id (diff_s (v_of s2) (v_of lca)) ==> mem_id id (diff (ops_of s2) (ops_of lca))) /\
                   (forall id. mem_id_s id (v_of lca) ==> not (mem_id_s id (diff_s (v_of s2) (v_of lca))))) =
  lem_foldl init_st (ops_of lca);
  assert (forall id. mem_id_s id (v_of lca) ==> mem_id id (ops_of lca));
  
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  assert (forall id. mem_id_s id (v_of s2) ==> mem_id_s id (v_of lca) \/ mem_id id (diff (ops_of s2) (ops_of lca)));

  lt_is_neq (ops_of lca) (ops_of s2);
  assert (forall id. mem_id id (ops_of lca) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))));
  assert (forall id. mem_id_s id (v_of lca) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))));

  assert (forall id. mem_id_s id (v_of s2) /\ not (mem_id_s id (v_of lca)) ==> mem_id id (diff (ops_of s2) (ops_of lca)));
  assume (forall id. mem_id_s id (diff_s (v_of s2) (v_of lca)) <==> (mem_id_s id (v_of s2) /\ not (mem_id_s id (v_of lca)))); //todo
  assert (forall id. mem_id_s id (diff_s (v_of s2) (v_of lca)) ==> mem_id id (diff (ops_of s2) (ops_of lca)));
 
  assert (forall id. mem_id_s id (v_of lca) ==> not (mem_id_s id (diff_s (v_of s2) (v_of lca))));
  ()

let general' (a b:concrete_st) (al bl:log)
  : Lemma (requires (forall id. mem_id_s id a ==> mem_id id al) /\
                    (forall id. mem_id_s id b ==> mem_id id bl) /\
                    (forall id. mem_id id al ==> not (mem_id id bl)))
          (ensures (forall id. mem_id_s id a ==> not (mem_id_s id b))) = ()

let general (lca s1 s2:st)
  : Lemma (requires common_pre_wo_len lca s1 s2)
          (ensures (forall id. mem_id_s id (v_of lca) ==> not (mem_id_s id (diff_s (v_of s1) (v_of lca)))) /\
                   (forall id. mem_id_s id (v_of lca) ==> not (mem_id_s id (diff_s (v_of s2) (v_of lca)))) /\
                   (forall id. mem_id_s id (diff_s (v_of s1) (v_of lca)) ==> not (mem_id_s id (diff_s (v_of s2) (v_of lca)))) /\
                   (forall id. mem_id_s id (diff_s (v_of s1) (v_of lca)) ==> not (mem_id_s id (v_of s2))) /\
                   (forall id. mem_id_s id (diff_s (v_of s2) (v_of lca)) ==> not (mem_id_s id (v_of s1)))) =
  general_1 lca s1 s2;
  general_2 lca s1 s2;
  general' (diff_s (v_of s1) (v_of lca)) (diff_s (v_of s2) (v_of lca)) (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca))

let lem_not_exists (lastop:log_entry) (l:log)
  : Lemma (requires Rem? (snd lastop))
          (ensures not (exists_triple lastop l) <==> 
                   (~ (exists e. mem e l /\ get_ele e = get_ele lastop)) \/
                   
                    ((exists e. mem e l /\ get_ele e = get_ele lastop) /\
                    (forall r. mem r l /\ get_ele r = get_ele lastop ==> Rem? (snd r))) \/
                    
                    ((exists op. mem op l /\ Add? (snd op) /\ get_ele op = get_ele lastop) /\
                    (forall op. (mem op l /\ Add? (snd op) /\ get_ele op = get_ele lastop) ==>
                       (let _, suf = pre_suf l op in
                         (exists r. mem r suf /\ Rem? (snd r) /\ get_ele r = get_ele lastop)))))
  = ()

let lem_exists (lastop:log_entry) (l:log)
  : Lemma (requires Rem? (snd lastop))
          (ensures exists_triple lastop l <==>
                   (exists op. mem op l /\ Add? (snd op) /\ get_ele op = get_ele lastop /\
                    (let _, suf = pre_suf l op in
                    (forall r. mem r suf /\ get_ele r = get_ele lastop ==> Add? (snd r)))))
  = ()
  
let lem_eq_is_equiv (a b:log)
  : Lemma (requires (forall x. foldl_prop x a /\ foldl_prop x b ==>
                          seq_foldl x a = seq_foldl x b) /\ a = b)
          (ensures (forall x. foldl_prop x a /\ foldl_prop x b ==>
                         eq (seq_foldl x a) (seq_foldl x b))) = ()

let lem_foldl_prop_comm_4 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. (foldl_prop x (cons op l) /\ foldl_prop x (snoc l op)) ==>
                         (foldl_prop x (cons hd (cons op tl)) /\
                          foldl_prop (do x hd) (cons op tl) /\
                          foldl_prop (seq_foldl x (cons hd (create 1 op))) tl)))) = admit()

let lem_eq_is_equiv_c1 (l:log) (op:log_entry) 
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                          (lem_foldl_prop_comm l op;
                          eq (seq_foldl x (cons op l)) (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) /\
                          eq (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) (seq_foldl x (cons hd (cons op tl)))))))
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                         (lem_foldl_prop_comm l op;
                         eq (seq_foldl x (cons op l)) (seq_foldl x (cons hd (cons op tl))))))) = ()

let lem_eq_is_equiv_c2 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                          (lem_foldl_prop_comm l op;
                          eq (seq_foldl x (cons op l)) (seq_foldl x (cons hd (cons op tl))) /\
                          eq (seq_foldl x (cons hd (cons op tl))) (seq_foldl (do x hd) (cons op tl))))))
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                         (lem_foldl_prop_comm l op;
                         eq (seq_foldl x (cons op l)) (seq_foldl (do x hd) (cons op tl)))))) = ()

let lem_eq_is_equiv_c3 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                          (lem_foldl_prop_comm l op;
                          eq (seq_foldl x (cons op l)) (seq_foldl (do x hd) (cons op tl)) /\
                          eq (seq_foldl (do x hd) (cons op tl)) (seq_foldl (do x hd) (snoc tl op))))))
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                         (lem_foldl_prop_comm l op;
                         eq (seq_foldl x (cons op l)) (seq_foldl (do x hd) (snoc tl op)))))) = ()

let lem_eq_is_equiv_c4 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                          (lem_foldl_prop_comm l op;
                          eq (seq_foldl x (cons op l)) (seq_foldl (do x hd) (snoc tl op)) /\
                          eq (seq_foldl (do x hd) (snoc tl op)) (seq_foldl x (snoc l op))))))
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                         (lem_foldl_prop_comm l op;
                         eq (seq_foldl x (cons op l)) (seq_foldl x (snoc l op)))))) = ()
                         
let lem_case1_eq (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    lem_foldl_prop_comm l op;
                    (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>             
                          (seq_foldl x (cons op l)) = (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl))))
          (ensures (let hd = head l in let tl = tail l in
                    lem_foldl_prop_comm l op;
                    (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>  
                          eq (seq_foldl x (cons op l)) (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl)))) = ()

let lem_case3_eq  (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                   (let hd = head l in let tl = tail l in
                   (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                         (lem_foldl_prop_comm l op;
                          (seq_foldl x (cons hd (cons op tl))) = (seq_foldl (do x hd) (cons op tl))))))
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                         (lem_foldl_prop_comm l op;
                         eq (seq_foldl x (cons hd (cons op tl))) (seq_foldl (do x hd) (cons op tl)))))) = ()

let lem_case4_eq  (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                   (let hd = head l in let tl = tail l in
                   (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                         (lem_foldl_prop_comm l op;
                          (seq_foldl (do x hd) (snoc tl op)) = (seq_foldl x (snoc l op))))))
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                         (lem_foldl_prop_comm l op;
                         eq (seq_foldl (do x hd) (snoc tl op)) (seq_foldl x (snoc l op)))))) = ()
        
let rec lem_equiv_st_foldl_help (a b:concrete_st) (l:log)
  : Lemma (requires foldl_prop a l /\ foldl_prop b l /\ eq a b)
          (ensures eq (seq_foldl a l) (seq_foldl b l)) (decreases length l)
          [SMTPat (eq (seq_foldl a l) (seq_foldl b l))] =
  match length l with
  |0 -> ()
  |_ -> lem_equiv_st_foldl_help (do a (head l)) (do b (head l)) (tail l)
           
let lem_equiv_st_foldl (a b:log) (l:log)
  : Lemma (ensures (forall x. (foldl_prop x a /\ foldl_prop x b /\ 
                         foldl_prop (seq_foldl x a) l /\ foldl_prop (seq_foldl x b) l /\
                         eq (seq_foldl x a) (seq_foldl x b)) ==>
                         eq (seq_foldl (seq_foldl x a) l) (seq_foldl (seq_foldl x b) l))) = ()

let lem_case2 (l:log) (op:log_entry)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                          (lem_foldl_prop_comm l op;
                          eq (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) 
                             (seq_foldl (seq_foldl x (cons hd (create 1 op))) tl) /\
                          seq_foldl (seq_foldl x (cons hd (create 1 op))) tl =
                          seq_foldl x (cons hd (cons op tl))))))
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. foldl_prop x (cons op l) /\ foldl_prop x (snoc l op) ==>
                          (lem_foldl_prop_comm l op;
                           eq (seq_foldl (seq_foldl x (cons op (create 1 hd))) tl) (seq_foldl x (cons hd (cons op tl))))))) = ()
                        
#push-options "--z3rlimit 500"
let merge_inv_prop_inv2'_1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    exists_triple last1 (diff (ops_of s2) (ops_of lca))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                       suf2 = snd (pre_suf (ops_of s2) op2) /\
                       fst last1 <> fst op2))) =
  let _, last1 = un_snoc (ops_of s1) in
  let (_, op, suf) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  mem_ele_id op (diff (ops_of s2) (ops_of lca));
  assert (mem_id (fst op) (diff (ops_of s2) (ops_of lca)));
  lem_suf_equal (ops_of lca) (ops_of s2) op;
  assert (suf = snd (pre_suf (ops_of s2) op));
  lastop_diff (ops_of lca) (ops_of s1);
  assert (mem_id (fst last1) (diff (ops_of s1) (ops_of lca)));
  id_not_eq (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) (fst last1) (fst op);
  assert (fst op <> fst last1); ()
  
let merge_inv_prop_inv2' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    exists_triple last1 (diff (ops_of s2) (ops_of lca))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                       suf2 = snd (pre_suf (ops_of s2) op2) /\
                       (let inv2 = inverse_st_op s2 op2 in
                       concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2))))) =
  merge_inv_prop_inv2'_1 lca s1 s2;
  let _, last1 = un_snoc (ops_of s1) in
  let (pre, op, suf) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  resolve_conflict_prop last1 op;
  assert (Add? (snd op) /\ Rem? (snd last1) /\ get_ele last1 = get_ele op);
  let inv2 = inverse_st_op s2 op in 
  do_prop (v_of inv2) op;
  assert (forall e. (L.mem e (v_of inv2) \/ e = (fst op, get_ele op)) <==> L.mem e (v_of s2));
  assert (forall id. (mem_id_s id (v_of inv2) \/ id = fst op) <==> mem_id_s id (v_of s2));  
  assert (forall id. mem_id_s id (v_of inv2) ==> mem_id_s id (v_of s2)); 
  lem_merge_pre (v_of lca) (v_of s1) (v_of inv2)

let merge_inv_prop_inv1'_1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                    exists_triple last2 (diff (ops_of s1) (ops_of lca))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                       suf1 = snd (pre_suf (ops_of s1) op1) /\
                       fst last2 <> fst op1))) =
  let _, last2 = un_snoc (ops_of s2) in
  let (_, op, suf) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  lem_inverse_op (ops_of lca) (ops_of s1) op;
  mem_ele_id op (diff (ops_of s1) (ops_of lca));
  assert (mem_id (fst op) (diff (ops_of s1) (ops_of lca)));
  lem_suf_equal (ops_of lca) (ops_of s1) op;
  assert (suf = snd (pre_suf (ops_of s1) op));
  lastop_diff (ops_of lca) (ops_of s2);
  assert (mem_id (fst last2) (diff (ops_of s2) (ops_of lca)));
  id_not_eq (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) (fst op) (fst last2);
  assert (fst op <> fst last2); ()
                       
let merge_inv_prop_inv1' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                    not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                    exists_triple last2 (diff (ops_of s1) (ops_of lca))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                       suf1 = snd (pre_suf (ops_of s1) op1) /\
                       (let inv1 = inverse_st_op s1 op1 in
                       concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2))))) = 
  merge_inv_prop_inv1'_1 lca s1 s2;
  let _, last2 = un_snoc (ops_of s2) in
  let (_, op, suf) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  resolve_conflict_prop last2 op;
  assert (Add? (snd op) /\ Rem? (snd last2) /\ get_ele last2 = get_ele op);
  lem_suf_equal (ops_of lca) (ops_of s1) op;
  let inv1 = inverse_st_op s1 op in
  do_prop (v_of inv1) op;
  assert (L.mem (fst op, get_ele op) (v_of s1));
  assert (forall e. (L.mem e (v_of inv1) \/ e = (fst op, get_ele op)) <==> L.mem e (v_of s1)); 
  assert (forall e. L.mem e (v_of inv1) <==> (L.mem e (v_of s1) /\ e <> (fst op, get_ele op)));
  lem_foldl init_st (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_suf_equal2 (ops_of lca) (ops_of s1) op;
  assert (not (mem_id_s (fst op) (v_of lca)));
  no_id_not_ele (fst op, get_ele op) (v_of lca);
  assert (not (L.mem (fst op, get_ele op) (v_of lca)));
  assert (L.mem (fst op, get_ele op) (diff_s (v_of s1) (v_of lca))); 

  lemma1 (diff_s (v_of inv1) (v_of lca)) (diff_s (v_of s1) (v_of lca)) (fst op, get_ele op);
  assert (forall e. (L.mem e (diff_s (v_of inv1) (v_of lca)) \/ e = (fst op, get_ele op)) <==>
               L.mem e (diff_s (v_of s1) (v_of lca)));
  lem_mem_id (diff_s (v_of inv1) (v_of lca)) (diff_s (v_of s1) (v_of lca)) (fst op, get_ele op);
  assert (forall id. mem_id_s id (diff_s (v_of inv1) (v_of lca)) ==> mem_id_s id (diff_s (v_of s1) (v_of lca)));
  lem_merge_pre (v_of lca) (v_of inv1) (v_of s2)

let merge_inv_prop_inv1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last1))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) = 
  let p1, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  resolve_conflict_prop last1 last2; 
  assert (Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last2 = get_ele last1);
  let inv1 = inverse_st s1 in
  lem_foldl init_st (ops_of s1);
  
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s1); 
  inverse_diff_id (ops_of lca) (ops_of s1) (ops_of s2);
  lem_foldl init_st (ops_of inv1); 
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of inv1);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of inv1) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca))

let merge_inv_prop_inv2_c2_c4 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last2 /\
                     Add? (snd last2)))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2); 
  inverse_diff_id (ops_of lca) (ops_of s1) (ops_of s2);
  lem_foldl init_st (ops_of inv2); 
  lem_foldl init_st (ops_of s1);
  split_prefix init_st (ops_of lca) (ops_of inv2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of inv2) (ops_of lca));
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca))

let merge_inv_prop_inv2_c3 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last2 /\
                     Rem? (snd last1) /\ Rem? (snd last2)))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = 
  let _, last2 = un_snoc (ops_of s2) in
  assume (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (ops_of s2)));//todo
  lem_foldl init_st (ops_of s1);
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s2);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  assert (forall id. mem_id_s id (diff_s (v_of s1) (v_of lca)) ==> mem_id_s id (v_of s1)); 
  assume (forall id. mem_id_s id (v_of lca) ==> not (mem_id_s id (diff_s (v_of s1) (v_of lca))));//todo
  assert (forall id. mem_id_s id (v_of (inverse_st s2)) ==> mem_id id (ops_of s2));
  ()
  
let merge_inv_prop_inv2_c1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     fst last1 <> fst last2 /\
                     last (resolve_conflict last1 last2) = last2 /\
                     Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 <> get_ele last2))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) = 
  let _, last2 = un_snoc (ops_of s2) in
  //inverse_diff_id1 (ops_of lca) (ops_of s1) (ops_of s2);
  assume (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (ops_of s2)));
  assume (forall id. mem_id_s id (diff_s (v_of s1) (v_of lca)) ==> mem_id id (diff (ops_of s1) (ops_of lca)));
  lem_foldl init_st (ops_of s2);
  assert (forall id. mem_id_s id (v_of (inverse_st s2)) ==> mem_id id (ops_of s2));
  ()

let merge_inv_prop (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2)
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==> 
                      (let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                        suf2 = snd (pre_suf (ops_of s2) op2) /\
                        concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st_op s2 op2)))) /\
                        
                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==> 
                      (let (pre1, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                        suf1 = snd (pre_suf (ops_of s1) op1) /\
                        concrete_merge_pre (v_of lca) (v_of (inverse_st_op s1 op1)) (v_of s2))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  if exists_triple last1 (diff (ops_of s2) (ops_of lca)) 
    then merge_inv_prop_inv2' lca s1 s2
  else if exists_triple last2 (diff (ops_of s1) (ops_of lca)) 
    then merge_inv_prop_inv1' lca s1 s2
  else if last (resolve_conflict last1 last2) = last1
    then merge_inv_prop_inv1 lca s1 s2
  else 
    match snd last1, snd last2 with
    |_, Add _ -> merge_inv_prop_inv2_c2_c4 lca s1 s2
    |Add _, Rem _ -> merge_inv_prop_inv2_c1 lca s1 s2
    |Rem _, Rem _ -> merge_inv_prop_inv2_c3 lca s1 s2

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    ops_of s1 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()
  
let linearizable_s2_0 (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    ops_of s2 = ops_of lca /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    foldl_prop (v_of lca) (diff (ops_of s1) (ops_of lca)))
          (ensures eq (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))) = ()

let linearizable_gt0_pre_inv2' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\
                    (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                     suf2 = snd (pre_suf (ops_of s2) op2) /\
                    (let inv2 = inverse_st_op s2 op2 in
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let inv2 = inverse_st_op s2 op2 in
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)) = 
  inverse_diff_id_inv2' (ops_of lca) (ops_of s1) (ops_of s2);
  let _, last1 = un_snoc (ops_of s1) in
  let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  let s2' = inverse_st_op s2 op2 in 
  lem_foldl init_st (ops_of lca);
  assert (forall id. mem_id_s id (v_of lca) ==> mem_id id (ops_of lca)); 
  lem_foldl init_st (ops_of s1);
  assert (forall id. mem_id_s id (v_of s1) ==> mem_id id (ops_of s1)); 
  lem_foldl init_st (ops_of s2);
  assert (forall id. mem_id_s id (v_of s2) ==> mem_id id (ops_of s2));
  lem_foldl init_st (ops_of s2');
  assert (forall id. mem_id_s id (v_of s2') ==> mem_id id (ops_of s2'));
  assert (forall id. mem_id_s id (concrete_merge (v_of lca) (v_of s1) (v_of s2')) ==> 
               (mem_id_s id (v_of lca) \/ mem_id_s id (v_of s1) \/ mem_id_s id (v_of s2')));
  assert (forall id. (mem_id id (ops_of lca) \/ mem_id id (ops_of s1) \/ mem_id id (pre2 ++ suf2)) ==> id <> fst op2); ()

let linearizable_gt0_pre_inv1' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     exists_triple last2 (diff (ops_of s1) (ops_of lca)) /\
                    (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                     suf1 = snd (pre_suf (ops_of s1) op1) /\
                    (let inv1 = inverse_st_op s1 op1 in
                     concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    let inv1 = inverse_st_op s1 op1 in
                    concrete_do_pre (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)) = 
  inverse_diff_id_inv1' (ops_of lca) (ops_of s1) (ops_of s2);
  let _, last2 = un_snoc (ops_of s2) in
  let (pre1, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  let s1' = inverse_st_op s1 op1 in 
  lem_foldl init_st (ops_of lca);
  assert (forall id. mem_id_s id (v_of lca) ==> mem_id id (ops_of lca));  
  lem_foldl init_st (ops_of s1);
  assert (forall id. mem_id_s id (v_of s1) ==> mem_id id (ops_of s1));
  lem_foldl init_st (ops_of s2);
  assert (forall id. mem_id_s id (v_of s2) ==> mem_id id (ops_of s2));
  lem_foldl init_st (ops_of s1');
  assert (forall id. mem_id_s id (v_of s1') ==> mem_id id (ops_of s1'));
  assert (forall id. mem_id_s id (concrete_merge (v_of lca) (v_of s1') (v_of s2)) ==> 
               (mem_id_s id (v_of lca) \/ mem_id_s id (v_of s1') \/ mem_id_s id (v_of s2)));
  assert (forall id. (mem_id id (ops_of lca) \/ mem_id id (pre1 ++ suf1) \/ mem_id id (ops_of s2)) ==> id <> fst op1); ()
  
let linearizable_gt0_pre_inv2 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                    concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) = 
  let _, last1 = un_snoc (ops_of s1) in
  let s1' = inverse_st s1 in
  lem_foldl init_st (ops_of lca);
  assert (forall id. mem_id_s id (v_of lca) ==> mem_id id (ops_of lca)); 
  lem_foldl init_st (ops_of s1);
  assert (forall id. mem_id_s id (v_of s1) ==> mem_id id (ops_of s1));
  lem_foldl init_st (ops_of s2);
  assert (forall id. mem_id_s id (v_of s2) ==> mem_id id (ops_of s2)); 
  lem_foldl init_st (ops_of s1');
  assert (forall id. mem_id_s id (v_of s1') ==> mem_id id (ops_of s1'));
  assert (forall id. mem_id_s id (concrete_merge (v_of lca) (v_of s1') (v_of s2)) ==> 
               (mem_id_s id (v_of lca) \/ mem_id_s id (v_of s1') \/ mem_id_s id (v_of s2)));
  inverse_diff_id_last1 (ops_of lca) (ops_of s1) (ops_of s2);
  assert (forall id. (mem_id id (ops_of lca) \/ mem_id id (ops_of s1') \/ mem_id id (ops_of s2)) ==> id <> fst last1); ()

let linearizable_gt0_pre_inv1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) = 
  let _, last2 = un_snoc (ops_of s2) in
  let s2' = inverse_st s2 in
  lem_foldl init_st (ops_of lca);
  assert (forall id. mem_id_s id (v_of lca) ==> mem_id id (ops_of lca)); 
  lem_foldl init_st (ops_of s1);
  assert (forall id. mem_id_s id (v_of s1) ==> mem_id id (ops_of s1));
  lem_foldl init_st (ops_of s2);
  assert (forall id. mem_id_s id (v_of s2) ==> mem_id id (ops_of s2)); 
  lem_foldl init_st (ops_of s2');
  assert (forall id. mem_id_s id (v_of s2') ==> mem_id id (ops_of s2'));
  assert (forall id. mem_id_s id (concrete_merge (v_of lca) (v_of s1) (v_of s2')) ==> 
               (mem_id_s id (v_of lca) \/ mem_id_s id (v_of s1) \/ mem_id_s id (v_of s2'))); 
  inverse_diff_id_last2 (ops_of lca) (ops_of s1) (ops_of s2);
  assert (forall id. (mem_id id (ops_of lca) \/ mem_id id (ops_of s1) \/ mem_id id (ops_of s2')) ==> id <> fst last2); ()
                    
#push-options "--z3rlimit 200"
let linearizable_gt0_pre (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                     (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                        suf2 = snd (pre_suf (ops_of s2) op2) /\
                        (let inv2 = inverse_st_op s2 op2 in
                        concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)))) /\

                      ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                        exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                        suf1 = snd (pre_suf (ops_of s1) op1) /\
                        (let inv1 = inverse_st_op s1 op1 in
                        concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2)))) /\

                     ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                     (last (resolve_conflict last1 last2) = last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                           concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                           
                     (last (resolve_conflict last1 last2) <> last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                           concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                       (let inv2 = inverse_st_op s2 op2 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                       (let inv1 = inverse_st_op s1 op1 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                    
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1) /\
                       
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  if exists_triple last1 (diff (ops_of s2) (ops_of lca)) 
    then linearizable_gt0_pre_inv2' lca s1 s2
  else if exists_triple last2 (diff (ops_of s1) (ops_of lca)) 
    then linearizable_gt0_pre_inv1' lca s1 s2
  else if last (resolve_conflict last1 last2) = last1
    then linearizable_gt0_pre_inv2 lca s1 s2
  else 
    linearizable_gt0_pre_inv1 lca s1 s2

let trans_op (a b c:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. L.mem e a <==> (L.mem e b \/ e = ele)) /\
                    (forall e. (L.mem e b \/ e = ele) <==> L.mem e c))
          (ensures eq a c) = ()

let trans_op_ele (a b c:concrete_st) (ele:nat)
  : Lemma (requires (forall e. L.mem e a <==> (L.mem e b /\ snd e <> ele)) /\
                    (forall e. (L.mem e b /\ snd e <> ele) <==> L.mem e c))
          (ensures eq a c) = ()

let trans_op_not (a b c:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. L.mem e a <==> (L.mem e b /\ e <> ele)) /\
                    (forall e. (L.mem e b /\ e <> ele) <==> L.mem e c))
          (ensures eq a c) = ()

let lem_merge_inv2 (l s1 s2 inv2:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. (L.mem e (diff_s inv2 l) \/ e = ele) <==> (L.mem e (diff_s s2 l))) /\
                     concrete_merge_pre l s1 inv2 /\ concrete_merge_pre l s1 s2 /\
                    (forall e. L.mem e (concrete_merge l s1 inv2) <==> (L.mem e (concrete_merge l s1 s2) /\ e <> ele)))
          (ensures (forall e. (L.mem e (concrete_merge l s1 inv2) \/ e = ele) <==> L.mem e (concrete_merge l s1 s2))) = ()

let lem_merge_inv1 (l s1 s2 inv1:concrete_st) (ele:(nat * nat))
  : Lemma (requires (forall e. (L.mem e (diff_s inv1 l) \/ e = ele) <==> (L.mem e (diff_s s1 l))) /\
                     concrete_merge_pre l inv1 s2 /\ concrete_merge_pre l s1 s2 /\
                    (forall e. L.mem e (concrete_merge l inv1 s2) <==> (L.mem e (concrete_merge l s1 s2) /\ e <> ele)))
          (ensures (forall e. (L.mem e (concrete_merge l inv1 s2) \/ e = ele) <==> L.mem e (concrete_merge l s1 s2))) = ()
          
#push-options "--z3rlimit 500"
type common_pre_linearizable_gt0_inv2' (lca s1 s2:st) =
  common_pre lca s1 s2 /\
  (let _, last1 = un_snoc (ops_of s1) in
  exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\
  (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  suf2 = snd (pre_suf (ops_of s2) op2) /\
  (let inv2 = inverse_st_op s2 op2 in
  concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2) /\
  concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)))

let linearizable_gt0_inv2'_1 (lca s1 s2:st)
  : Lemma (requires common_pre_linearizable_gt0_inv2' lca s1 s2)
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    Add? (snd op2) /\ Rem? (snd last1) /\ get_ele last1 = get_ele op2)) = 
  let _, last1 = un_snoc (ops_of s1) in
  let (_, op, suf) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  lem_inverse_op (ops_of lca) (ops_of s2) op;
  assert (commutative_seq op suf); 
  assert (last (resolve_conflict last1 op) = op); 
  lastop_diff (ops_of lca) (ops_of s1);
  assert (mem_id (fst last1) (diff (ops_of s1) (ops_of lca)));
  mem_ele_id op (diff (ops_of s2) (ops_of lca));
  assert (fst last1 <> fst op); 
  resolve_conflict_prop last1 op;
  assert (Add? (snd op) /\ Rem? (snd last1) /\ get_ele last1 = get_ele op); 
  ()

let linearizable_gt0_inv2'_2 (lca s1 s2:st)
  : Lemma (requires common_pre_linearizable_gt0_inv2' lca s1 s2 /\
                    (let _, last1 = un_snoc (ops_of s1) in
                    let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    Add? (snd op2) /\ Rem? (snd last1) /\ get_ele last1 = get_ele op2))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let inv2 = inverse_st_op s2 op2 in
                    (forall e. L.mem e (v_of inv2) <==> (L.mem e (v_of s2) /\ e <> (fst op2, get_ele op2))) /\
                    (L.mem (fst op2, get_ele op2) (v_of s2)))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let (_, op, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  lem_suf_equal (ops_of lca) (ops_of s2) op;
  let inv2 = inverse_st_op s2 op in
  do_prop (v_of inv2) op; 
  assert (L.mem (fst op, get_ele op) (v_of s2));
  assert (forall e. (L.mem e (v_of inv2) \/ e = (fst op, get_ele op)) <==> L.mem e (v_of s2)); 
  assert (forall e. L.mem e (v_of inv2) <==> (L.mem e (v_of s2) /\ e <> (fst op, get_ele op)));
  ()

let linearizable_gt0_inv2' (lca s1 s2:st)
  : Lemma (requires common_pre_linearizable_gt0_inv2' lca s1 s2)
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let inv2 = inverse_st_op s2 op2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))  = 
  linearizable_gt0_inv2'_1 lca s1 s2;
  linearizable_gt0_inv2'_2 lca s1 s2;
  let _, last1 = un_snoc (ops_of s1) in
  let (pre, op, suf) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  let inv2 = inverse_st_op s2 op in
  lem_foldl init_st (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  
  lem_suf_equal2 (ops_of lca) (ops_of s2) op;
  
  assert (not (mem_id_s (fst op) (v_of lca)));
  
  no_id_not_ele (fst op, get_ele op) (v_of lca);
  assert (not (L.mem (fst op, get_ele op) (v_of lca)));
  
  assert (L.mem (fst op, get_ele op) (diff_s (v_of s2) (v_of lca)));
  
  assert (forall e. L.mem e (diff_s (v_of inv2) (v_of lca)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)) /\ e <> (fst op, get_ele op));
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst op, get_ele op)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)));      
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst op, get_ele op))); 

  lemma1 (diff_s (v_of inv2) (v_of lca)) (diff_s (v_of s2) (v_of lca)) (fst op, get_ele op);
  assert (forall e. (L.mem e (diff_s (v_of inv2) (v_of lca)) \/ e = (fst op, get_ele op)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)));   

  lem_merge_inv2 (v_of lca) (v_of s1) (v_of s2) (v_of inv2) (fst op, get_ele op); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst op, get_ele op)));

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst op, get_ele op)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op));

  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
           (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op)
           (fst op, get_ele op);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

type common_pre_linearizable_gt0_inv1' (lca s1 s2:st) =
  common_pre lca s1 s2 /\
  (let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
  exists_triple last2 (diff (ops_of s1) (ops_of lca)) /\
  (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  suf1 = snd (pre_suf (ops_of s1) op1) /\
  (let inv1 = inverse_st_op s1 op1 in
  concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2) /\
  concrete_do_pre (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)))

let linearizable_gt0_inv1'_1 (lca s1 s2:st)
  : Lemma (requires common_pre_linearizable_gt0_inv1' lca s1 s2)
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    Add? (snd op1) /\ Rem? (snd last2) /\ get_ele last2 = get_ele op1)) = 
  let _, last2 = un_snoc (ops_of s2) in
  let (_, op, suf) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  lem_inverse_op (ops_of lca) (ops_of s1) op;
  assert (commutative_seq op suf); 
  assert (last (resolve_conflict last2 op) = op); 
  lastop_diff (ops_of lca) (ops_of s2);
  assert (mem_id (fst last2) (diff (ops_of s2) (ops_of lca)));
  mem_ele_id op (diff (ops_of s1) (ops_of lca));
  assert (fst last2 <> fst op); 
  resolve_conflict_prop last2 op;
  assert (Add? (snd op) /\ Rem? (snd last2) /\ get_ele last2 = get_ele op); 
  ()

let linearizable_gt0_inv1'_2 (lca s1 s2:st)
  : Lemma (requires common_pre_linearizable_gt0_inv1' lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                    let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    Add? (snd op1) /\ Rem? (snd last2) /\ get_ele last2 = get_ele op1))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    let inv1 = inverse_st_op s1 op1 in
                    (forall e. L.mem e (v_of inv1) <==> (L.mem e (v_of s1) /\ e <> (fst op1, get_ele op1))) /\
                    (L.mem (fst op1, get_ele op1) (v_of s1)))) = 
  let _, last2 = un_snoc (ops_of s2) in
  let (_, op, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  lem_suf_equal (ops_of lca) (ops_of s1) op;
  let inv1 = inverse_st_op s1 op in
  do_prop (v_of inv1) op; 
  assert (L.mem (fst op, get_ele op) (v_of s1));
  assert (forall e. (L.mem e (v_of inv1) \/ e = (fst op, get_ele op)) <==> L.mem e (v_of s1)); 
  assert (forall e. L.mem e (v_of inv1) <==> (L.mem e (v_of s1) /\ e <> (fst op, get_ele op)));
  ()
  
let linearizable_gt0_inv1' (lca s1 s2:st)
  : Lemma (requires common_pre_linearizable_gt0_inv1' lca s1 s2)
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    let (_, op1, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    let inv1 = inverse_st_op s1 op1 in
                    eq (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  linearizable_gt0_inv1'_1 lca s1 s2;
  linearizable_gt0_inv1'_2 lca s1 s2;
  let _, last2 = un_snoc (ops_of s2) in
  let (_, op, _) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
  let inv1 = inverse_st_op s1 op in
  lem_foldl init_st (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_suf_equal2 (ops_of lca) (ops_of s1) op;
  assert (not (mem_id_s (fst op) (v_of lca)));
  no_id_not_ele (fst op, get_ele op) (v_of lca);
  assert (not (L.mem (fst op, get_ele op) (v_of lca)));
  assert (L.mem (fst op, get_ele op) (diff_s (v_of s1) (v_of lca))); 
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst op, get_ele op)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of inv1) /\ L.mem e (v_of s2)));    
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst op, get_ele op)));  

  lemma1 (diff_s (v_of inv1) (v_of lca)) (diff_s (v_of s1) (v_of lca)) (fst op, get_ele op);
  assert (forall e. (L.mem e (diff_s (v_of inv1) (v_of lca)) \/ e = (fst op, get_ele op)) <==>
               L.mem e (diff_s (v_of s1) (v_of lca)));   

  lem_merge_inv1 (v_of lca) (v_of s1) (v_of s2) (v_of inv1) (fst op, get_ele op); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) \/ e = (fst op, get_ele op))); 

  do_prop (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) \/ e = (fst op, get_ele op)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op));  

  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of inv1) (v_of s2))
           (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op)
           (fst op, get_ele op);
  assert (eq (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()
                    
let linearizable_gt0_inv1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last1 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                     concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let p1, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2);
  resolve_conflict_prop last1 last2; 
  assert (Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last2 = get_ele last1);
  let inv1 = inverse_st s1 in
  lem_foldl init_st (ops_of s1);
  assert (forall e. (L.mem e (v_of inv1) \/ e = (fst last1, get_ele last1)) <==> L.mem e (v_of s1));
  assert (forall e. L.mem e (v_of inv1) <==> (L.mem e (v_of s1) /\ e <> (fst last1, get_ele last1)));
  assert (forall e. L.mem e (diff_s (v_of inv1) (v_of lca)) <==>
               L.mem e (diff_s (v_of s1) (v_of lca)) /\ e <> (fst last1, get_ele last1));
  
  assert (L.mem (fst last1, get_ele last1) (v_of s1)); 
  lem_diff (ops_of s1) (ops_of lca);
  lem_foldl init_st (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca));
  lem_suf_equal2_last (ops_of lca) (ops_of s1) last1;
  assert (not (mem_id_s (fst last1) (v_of lca))); 
  no_id_not_ele (fst last1, get_ele last1) (v_of lca);
  assert (not (L.mem (fst last1, get_ele last1) (v_of lca)));
  assert (L.mem (fst last1, get_ele last1) (diff_s (v_of s1) (v_of lca)));
  
  lemma1 (diff_s (v_of inv1) (v_of lca)) (diff_s (v_of s1) (v_of lca)) (fst last1, get_ele last1);
  assert (forall e. (L.mem e (diff_s (v_of inv1) (v_of lca)) \/ e = (fst last1, get_ele last1)) <==>
               L.mem e (diff_s (v_of s1) (v_of lca)));
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst last1, get_ele last1)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of inv1) /\ L.mem e (v_of s2))); 
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst last1, get_ele last1)));
  
  lem_merge_inv1 (v_of lca) (v_of s1) (v_of s2) (v_of inv1) (fst last1, get_ele last1); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) \/ e = (fst last1, get_ele last1)));
  
  do_prop (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) last1;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) \/ e = (fst last1, get_ele last1)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) last1));
  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of inv1) (v_of s2))
           (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) last1)
           (fst last1, get_ele last1)

let linearizable_gt0_inv2_c2 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Add? (snd last1) /\ Add? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2);
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) \/ e = (fst last2, get_ele last2)) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (v_of inv2) <==> (L.mem e (v_of s2) /\ e <> (fst last2, get_ele last2)));
  assert (forall e. L.mem e (diff_s (v_of inv2) (v_of lca)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)) /\ e <> (fst last2, get_ele last2)); 

  assert (L.mem (fst last2, get_ele last2) (v_of s2)); 
  lem_diff (ops_of s2) (ops_of lca);
  lem_foldl init_st (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  lem_suf_equal2_last (ops_of lca) (ops_of s2) last2;
  assert (not (mem_id_s (fst last2) (v_of lca))); 
  no_id_not_ele (fst last2, get_ele last2) (v_of lca);
  assert (not (L.mem (fst last2, get_ele last2) (v_of lca)));
  assert (L.mem (fst last2, get_ele last2) (diff_s (v_of s2) (v_of lca)));
  
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst last2, get_ele last2)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)));         
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst last2, get_ele last2))); 

  lemma1 (diff_s (v_of inv2) (v_of lca)) (diff_s (v_of s2) (v_of lca)) (fst last2, get_ele last2);
  assert (forall e. (L.mem e (diff_s (v_of inv2) (v_of lca)) \/ e = (fst last2, get_ele last2)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)));   

  lem_merge_inv2 (v_of lca) (v_of s1) (v_of s2) (v_of inv2) (fst last2, get_ele last2); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst last2, get_ele last2)));

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst last2, get_ele last2)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
           (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
           (fst last2, get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

let linearizable_gt0_inv2_c4 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Rem? (snd last1) /\ Add? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2);
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) \/ e = (fst last2, get_ele last2)) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (v_of inv2) <==> (L.mem e (v_of s2) /\ e <> (fst last2, get_ele last2)));
  assert (forall e. L.mem e (diff_s (v_of inv2) (v_of lca)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)) /\ e <> (fst last2, get_ele last2)); 

  assert (L.mem (fst last2, get_ele last2) (v_of s2)); 
  lem_diff (ops_of s2) (ops_of lca);
  lem_foldl init_st (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  lem_suf_equal2_last (ops_of lca) (ops_of s2) last2;
  assert (not (mem_id_s (fst last2) (v_of lca))); 
  no_id_not_ele (fst last2, get_ele last2) (v_of lca);
  assert (not (L.mem (fst last2, get_ele last2) (v_of lca)));
  assert (L.mem (fst last2, get_ele last2) (diff_s (v_of s2) (v_of lca)));
  
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst last2, get_ele last2)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)));         
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst last2, get_ele last2))); 

  lemma1 (diff_s (v_of inv2) (v_of lca)) (diff_s (v_of s2) (v_of lca)) (fst last2, get_ele last2);
  assert (forall e. (L.mem e (diff_s (v_of inv2) (v_of lca)) \/ e = (fst last2, get_ele last2)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)));   

  lem_merge_inv2 (v_of lca) (v_of s1) (v_of s2) (v_of inv2) (fst last2, get_ele last2); 
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2))) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst last2, get_ele last2)));

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) \/ e = (fst last2, get_ele last2)) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
           (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
           (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
           (fst last2, get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

#push-options "--z3rlimit 200"
let rec lem_foldl_all_rem (s:concrete_st) (l:log) (ele:nat)
  : Lemma (requires foldl_prop s l /\
                    (exists op. mem op l /\ get_ele op = ele) /\
                    (forall op. (mem op l /\ get_ele op = ele) ==> Rem? (snd op)))
          (ensures not (mem_ele ele (seq_foldl s l)))
          (decreases length l) = 
  match length l with
  |1 -> ()
  |_ -> match snd (head l) with
       |Add e -> lem_foldl_all_rem (do s (head l)) (tail l) ele
       |Rem e -> if e = ele then (do_prop s (head l);
                   assert (not (mem_ele ele (do s (head l))));
                   admit(); lem_foldl_all_rem (do s (head l)) (tail l) ele)
                   else lem_foldl_all_rem (do s (head l)) (tail l) ele

let lem_not_exists_st (ele:nat) (x:concrete_st) (l:log)
  : Lemma (requires foldl_prop x l /\ //length l = 3 /\
                    (exists op. mem op l /\ Add? (snd op) /\ get_ele op = ele) /\
                    (forall op. (mem op l /\ Add? (snd op) /\ get_ele op = ele) ==>
                       (let _, suf = pre_suf l op in
                         (exists r. mem r suf /\ Rem? (snd r) /\ get_ele r = ele))))
          (ensures not (mem_ele ele (seq_foldl x l))) (decreases length l) = admit()
  (*match length l with
  |0 -> admit()
  |1 -> (*assume (~ (Add? (snd (head l)) /\ get_ele (head l) = ele));*) admit()
  |2 -> (*assume (~ (Add? (snd (last l)) /\ get_ele (last l) = ele));*) admit()
  |_ -> do_prop x (head l); lem_foldl x l; lem_foldl (do x (head l)) (tail l);
       lem_not_exists_st ele (do x (head l)) (tail l)
       (*if Add? (snd (head l)) && get_ele (head l) = ele 
          then (let _, suf = pre_suf l (head l) in
               (assume (exists r. mem r suf /\ Rem? (snd r) /\ get_ele r = ele);
                do_prop x (head l); admit(); lem_not_exists_st ele (do x (head l)) (tail l)))
             else (do_prop x (head l); lem_foldl x l; lem_not_exists_st ele (do x (head l)) (tail l))*)*)

let linearizable_gt0_inv2_c3_nec1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Rem? (snd last1) /\ Rem? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                     ~ (exists e. mem e (diff (ops_of s1) (ops_of lca)) /\ get_ele e = get_ele last2)))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_diff (ops_of s1) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2); 
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) /\ snd e <> get_ele last2) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==>
               L.mem e (diff_s (v_of inv2) (v_of lca)) /\ snd e <> get_ele last2); 
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca)); 
  lem_foldl_not_ele (v_of lca) (diff (ops_of s1) (ops_of lca)) (get_ele last2);
  assert (forall e. L.mem e (v_of s1) /\ snd e = get_ele last2 <==> L.mem e (v_of lca) /\ snd e = get_ele last2);
  lem_diff_st1 (v_of s1) (v_of lca) (get_ele last2) ;
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca))));
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)) /\ snd e <> get_ele last2) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)));   
  
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2));  

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
               (get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

let linearizable_gt0_inv2_c3_nec2 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Rem? (snd last1) /\ Rem? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                     ((exists e. mem e (diff (ops_of s1) (ops_of lca)) /\ get_ele e = get_ele last2) /\
                       (forall r. mem r (diff (ops_of s1) (ops_of lca)) /\ get_ele r = get_ele last2 ==> Rem? (snd r)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_diff (ops_of s1) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2); 
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) /\ snd e <> get_ele last2) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==>
               L.mem e (diff_s (v_of inv2) (v_of lca)) /\ snd e <> get_ele last2); 
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca)); 
  lem_foldl_all_rem (v_of lca) (diff (ops_of s1) (ops_of lca)) (get_ele last2);
  lem_diff_st2 (v_of s1) (v_of lca) (get_ele last2) ;
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca))));
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)) /\ snd e <> get_ele last2) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)));   
  
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2));  

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
               (get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()
             
let linearizable_gt0_inv2_c3_nec3 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Rem? (snd last1) /\ Rem? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                     ((exists op. mem op (diff (ops_of s1) (ops_of lca)) /\ Add? (snd op) /\ get_ele op = get_ele last2) /\
                      (forall op. (mem op (diff (ops_of s1) (ops_of lca)) /\ Add? (snd op) /\ get_ele op = get_ele last2) ==>
                         (let _, suf = pre_suf (diff (ops_of s1) (ops_of lca)) op in
                         (exists r. mem r suf /\ Rem? (snd r) /\ get_ele r = get_ele last2))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_not_exists last2 (diff (ops_of s1) (ops_of lca));
  lem_diff (ops_of s1) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_not_exists_st (get_ele last2) (v_of lca) (diff (ops_of s1) (ops_of lca));
  assert (not (mem_ele (get_ele last2) (v_of s1)));
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2); 
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) /\ snd e <> get_ele last2) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==>
               L.mem e (diff_s (v_of inv2) (v_of lca)) /\ snd e <> get_ele last2); 
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca)))); 
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)) /\ snd e <> get_ele last2) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)));   
  
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2));  

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
               (get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()
             
let lem_nec12 (lastop:log_entry) (l:log)
  : Lemma (ensures ((exists e. mem e l /\ get_ele e = get_ele lastop) /\
                    (forall r. mem r l /\ get_ele r = get_ele lastop ==> Rem? (snd r))) <==>
          (existsb (fun e -> get_ele e = get_ele lastop) l &&
          (forallb (fun r -> if get_ele r = get_ele lastop then Rem? (snd r) else true) l))) = ()

let linearizable_gt0_inv2_c3 (lca s1 s2:st)
 : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Rem? (snd last1) /\ Rem? (snd last2) /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_not_exists last2 (diff (ops_of s1) (ops_of lca));
  lem_nec12 last2 (diff (ops_of s1) (ops_of lca));
  if not (existsb (fun e -> get_ele e = get_ele last2) (diff (ops_of s1) (ops_of lca)))
    then linearizable_gt0_inv2_c3_nec1 lca s1 s2
  else if (existsb (fun e -> get_ele e = get_ele last2) (diff (ops_of s1) (ops_of lca)) &&
          (forallb (fun r -> if get_ele r = get_ele last2 then Rem? (snd r) else true) (diff (ops_of s1) (ops_of lca))))
    then linearizable_gt0_inv2_c3_nec2 lca s1 s2
  else linearizable_gt0_inv2_c3_nec3 lca s1 s2

let linearizable_gt0_inv2_c1_nec1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                     ~ (exists e. mem e (diff (ops_of s1) (ops_of lca)) /\ get_ele e = get_ele last2)))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_diff (ops_of s1) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2); 
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) /\ snd e <> get_ele last2) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==>
               L.mem e (diff_s (v_of inv2) (v_of lca)) /\ snd e <> get_ele last2); 
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca)); 
  lem_foldl_not_ele (v_of lca) (diff (ops_of s1) (ops_of lca)) (get_ele last2);
  assert (forall e. L.mem e (v_of s1) /\ snd e = get_ele last2 <==> L.mem e (v_of lca) /\ snd e = get_ele last2);
  lem_diff_st1 (v_of s1) (v_of lca) (get_ele last2) ;
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca))));
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)) /\ snd e <> get_ele last2) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)));   
  
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2));  

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
               (get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

let linearizable_gt0_inv2_c1_nec2 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                     ((exists e. mem e (diff (ops_of s1) (ops_of lca)) /\ get_ele e = get_ele last2) /\
                       (forall r. mem r (diff (ops_of s1) (ops_of lca)) /\ get_ele r = get_ele last2 ==> Rem? (snd r)))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_diff (ops_of s1) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2); 
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) /\ snd e <> get_ele last2) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==>
               L.mem e (diff_s (v_of inv2) (v_of lca)) /\ snd e <> get_ele last2); 
  lem_foldl (v_of lca) (diff (ops_of s1) (ops_of lca)); 
  lem_foldl_all_rem (v_of lca) (diff (ops_of s1) (ops_of lca)) (get_ele last2);
  lem_diff_st2 (v_of s1) (v_of lca) (get_ele last2) ;
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca))));
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)) /\ snd e <> get_ele last2) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)));   
  
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2));  

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
               (get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()

let linearizable_gt0_inv2_c1_nec3 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                     ((exists op. mem op (diff (ops_of s1) (ops_of lca)) /\ Add? (snd op) /\ get_ele op = get_ele last2) /\
                      (forall op. (mem op (diff (ops_of s1) (ops_of lca)) /\ Add? (snd op) /\ get_ele op = get_ele last2) ==>
                         (let _, suf = pre_suf (diff (ops_of s1) (ops_of lca)) op in
                         (exists r. mem r suf /\ Rem? (snd r) /\ get_ele r = get_ele last2))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_not_exists last2 (diff (ops_of s1) (ops_of lca));
  lem_diff (ops_of s1) (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s1);
  lem_not_exists_st (get_ele last2) (v_of lca) (diff (ops_of s1) (ops_of lca));
  assert (not (mem_ele (get_ele last2) (v_of s1)));
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  assert (fst last1 <> fst last2); 
  resolve_conflict_prop last1 last2; 
  let inv2 = inverse_st s2 in
  lem_foldl init_st (ops_of s2);
  assert (forall e. (L.mem e (v_of inv2) /\ snd e <> get_ele last2) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==>
               L.mem e (diff_s (v_of inv2) (v_of lca)) /\ snd e <> get_ele last2); 
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca)))); 
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2)) /\ snd e <> get_ele last2) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)));   
  
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2));  

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) /\ snd e <> get_ele last2) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2));

  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
               (get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()
             
let linearizable_gt0_inv2_c1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     Add? (snd last1) /\ Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     last (resolve_conflict last1 last2) = last2 /\
                     is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2)) /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  lem_not_exists last2 (diff (ops_of s1) (ops_of lca));
  lem_nec12 last2 (diff (ops_of s1) (ops_of lca));
  if not (existsb (fun e -> get_ele e = get_ele last2) (diff (ops_of s1) (ops_of lca)))
    then linearizable_gt0_inv2_c1_nec1 lca s1 s2
  else if (existsb (fun e -> get_ele e = get_ele last2) (diff (ops_of s1) (ops_of lca)) &&
          (forallb (fun r -> if get_ele r = get_ele last2 then Rem? (snd r) else true) (diff (ops_of s1) (ops_of lca))))
    then linearizable_gt0_inv2_c1_nec2 lca s1 s2
  else linearizable_gt0_inv2_c1_nec3 lca s1 s2

#push-options "--z3rlimit 500"
let linearizable_gt0 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     
                     (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                        suf2 = snd (pre_suf (ops_of s2) op2) /\
                        (let inv2 = inverse_st_op s2 op2 in
                        concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)))) /\

                      ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                        exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                        suf1 = snd (pre_suf (ops_of s1) op1) /\
                        (let inv1 = inverse_st_op s1 op1 in
                        concrete_merge_pre (v_of lca) (v_of inv1) (v_of s2)))) /\

                     ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                     (last (resolve_conflict last1 last2) = last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s1)) /\
                           concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) /\
                           
                     (last (resolve_conflict last1 last2) <> last1 ==>
                           is_prefix (ops_of lca) (ops_of (inverse_st s2)) /\
                           concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let _, last2 = un_snoc (ops_of s2) in
                    
                    (exists_triple last1 (diff (ops_of s2) (ops_of lca)) ==>
                      (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                       (let inv2 = inverse_st_op s2 op2 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2 /\
                       eq (do (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)
                          (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                      exists_triple last2 (diff (ops_of s1) (ops_of lca))) ==>
                      (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                       (let inv1 = inverse_st_op s1 op1 in
                       concrete_do_pre (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1 /\
                       eq (do (concrete_merge (v_of lca) (v_of inv1) (v_of s2)) op1)
                          (concrete_merge (v_of lca) (v_of s1) (v_of s2))))) /\

                    ((not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                       not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))) ==>
                    
                    (last (resolve_conflict last1 last2) = last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1 /\
                      eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2))) /\
                       
                    (last (resolve_conflict last1 last2) <> last1 ==>
                      concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2 /\
                      eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                         (concrete_merge (v_of lca) (v_of s1) (v_of s2)))))) = 
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  linearizable_gt0_pre lca s1 s2;
  if exists_triple last1 (diff (ops_of s2) (ops_of lca)) 
     then linearizable_gt0_inv2' lca s1 s2
  else if exists_triple last2 (diff (ops_of s1) (ops_of lca)) 
     then (assert (not (exists_triple last1 (diff (ops_of s2) (ops_of lca)))); linearizable_gt0_inv1' lca s1 s2)
  else if last (resolve_conflict last1 last2) = last1
     then (assert (not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                   not (exists_triple last2 (diff (ops_of s1) (ops_of lca)))); linearizable_gt0_inv1 lca s1 s2)
  else (assert (not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                last (resolve_conflict last1 last2) = last2);
    match snd last1, snd last2 with
    |Add _, Add _ -> linearizable_gt0_inv2_c2 lca s1 s2
    |Add _, Rem _ -> linearizable_gt0_inv2_c1 lca s1 s2
    |Rem _, Add _ -> linearizable_gt0_inv2_c4 lca s1 s2
    |Rem _, Rem _ -> linearizable_gt0_inv2_c3 lca s1 s2)
                
let convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre lca o /\
                    concrete_do_pre s1 o /\ s1' = do s1 o /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures eq (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1')) = ()

(**********************************************************************************************************)

#push-options "--z3rlimit 500"
type common_pre1 (lca s1 s2:st) =
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  //Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
  Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
  concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))

type common_pre2 (lca s1 s2:st) =
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  //Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
  //Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
  concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))
  
let base_case (lca s1 s2:st)
  : Lemma (requires common_pre1 lca s1 s2 /\
                    ops_of s1 = ops_of lca /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let s2' = inverse_st s2 in
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2))                   
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = ()

let base_case1 (lca s1 s2:st)
  : Lemma (requires common_pre1 lca s1 s2 /\
                    ops_of s1 = ops_of lca /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let s2' = inverse_st s2 in
                     ops_of s2' = ops_of lca /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2))                   
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = ()
                       
let lem_last (a:log)
  : Lemma (ensures (length a > 0 ==>
                   (let _, lst = un_snoc a in
                    last a = lst))) = ()

#push-options "--z3rlimit 600"
let ind_case_last1_rem_eq (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    common_pre1 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                     Rem? (snd last2) /\ Rem? (snd last1) && get_ele last1 = get_ele last2 /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     (let s2' = inverse_st s2 in
                     is_prefix (ops_of lca) (ops_of s2') /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)))               
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let pre2, last2 = un_snoc (ops_of s2) in
  let pre1, last1 = un_snoc (ops_of s1) in
  let s2' = inverse_st s2 in
  let s1' = inverse_st s1 in
  lem_last (ops_of s2);
  do_prop (v_of s2') last2;
  assert (forall e. (L.mem e (v_of s2') /\ snd e <> get_ele last2) <==> L.mem e (v_of s2));
  assert (forall e. L.mem e (diff_s (v_of s2) (v_of lca)) <==>
               L.mem e (diff_s (v_of s2') (v_of lca)) /\ snd e <> get_ele last2);
  lem_last (ops_of s1);
  do_prop (v_of s1') last1;
  assert (not (mem_ele (get_ele last1) (v_of s1)));
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca)))); 
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2')) /\ snd e <> get_ele last2) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)));   
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2')) /\ snd e <> get_ele last2));

  do_prop (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2;
  assert (forall e. (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2')) /\ snd e <> get_ele last2) <==>
                L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)); 

  trans_op_ele (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
               (concrete_merge (v_of lca) (v_of s1) (v_of s2'))
               (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
               (get_ele last2);
  assert (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
             (concrete_merge (v_of lca) (v_of s1) (v_of s2))); ()
#pop-options

let lem_not_ele_diff (s1' s1 lca:concrete_st) (op:log_entry) (ele:nat)
  : Lemma (requires concrete_do_pre s1' op /\ s1 = do s1' op /\ get_ele op <> ele /\
                    not (mem_ele ele (diff_s s1' lca)))
          (ensures not (mem_ele ele (diff_s s1 lca))) = ()

let lem_not_ele_diff1 (lca s1 s2 m:concrete_st) (ele:nat)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    not (mem_ele ele m) /\
                    eq m (concrete_merge lca s1 s2) /\
                    not (mem_ele ele (diff_s s2 lca)) /\
                    (forall e. L.mem e lca /\ L.mem e s1 /\ L.mem e s2 ==> snd e <> ele))
          (ensures not (mem_ele ele (diff_s s1 lca))) = ()

let lem_lastop_suf_0 (l l1 l2:log) (op:log_entry)
  : Lemma (requires distinct_ops l /\ mem op l /\
                    l = snoc l1 op ++ l2 /\
                    (lemma_mem_append (snoc l1 op) l2;
                    last l = op))
          (ensures length l2 = 0) =
  admit()
  
#push-options "--z3rlimit 600"
let not_add_eq (lca s1 s2:st)
  : Lemma (requires Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    common_pre1 lca s1 s2 /\
                    (let _, last2 = un_snoc (ops_of s2) in
                     let _, last1 = un_snoc (ops_of s1) in
                     Rem? (snd last2) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     (let s2' = inverse_st s2 in
                     is_prefix (ops_of lca) (ops_of s2') /\
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)))  
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    ~ (Add? (snd last1) /\ get_ele last1 = get_ele last2))) = 
  let _, last2 = un_snoc (ops_of s2) in
  let _, last1 = un_snoc (ops_of s1) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2); 
  assert (fst last1 <> fst last2);

  let s1' = inverse_st s1 in
  lemma_mem_snoc (ops_of s1') last1;
  assert (mem last1 (ops_of s1));
  assert (last (ops_of s1) = last1);
  lem_diff (ops_of s1) (ops_of lca);
  assert (last (diff (ops_of s1) (ops_of lca)) = last1);
  assert (mem last1 (diff (ops_of s1) (ops_of lca)));
  let pre, suf = pre_suf (diff (ops_of s1) (ops_of lca)) last1 in
  lem_lastop_suf_0 (diff (ops_of s1) (ops_of lca)) pre suf last1;
  assert (length suf = 0);
  lemma_empty suf; 
  comm_empty_log last1 suf; 
  assert (commutative_seq last1 suf);

  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> not (commutative last1 last2));
  resolve_conflict_prop last2 last1;
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> 
                last (resolve_conflict last2 last1) = last1);
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> 
                not (commutative last2 last1) /\
                last (resolve_conflict last2 last1) = last1 /\
                commutative_seq last1 suf);
  assert ((Add? (snd last1) /\ get_ele last1 = get_ele last2) ==> exists_triple last2 (diff (ops_of s1) (ops_of lca)));
  assert (~ (Add? (snd last1) /\ get_ele last1 = get_ele last2)); ()
#pop-options

#push-options "--z3rlimit 700"
let ind_case_last1_neq (lca s1 s2:st)
  : Lemma (requires (Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    (let s1' = inverse_st s1 in
                    common_pre1 lca s1 s2 /\
                    (let s2' = inverse_st s2 in
                    (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last2 <> get_ele last1 /\
                    is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2') /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                    concrete_merge_pre (v_of lca) (v_of s1') (v_of s2') /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    concrete_merge_pre (v_of lca) (v_of s1') (v_of s2) /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2 /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2 /\
                    eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1') (v_of s2)))))))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) =
  let _, last2 = un_snoc (ops_of s2) in 
  let s2' = inverse_st s2 in 
  lem_last (ops_of s2); 
  do_prop (v_of s2') last2; 
  assert (not (mem_ele (get_ele last2) (v_of s2))); 
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s2) (v_of lca))));
  let _, last1 = un_snoc (ops_of s1) in
  let s1' = inverse_st s1 in
  lem_last (ops_of s1);
  do_prop (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2;
  assert (not (mem_ele (get_ele last2) (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2))); 
  assert (forall e. L.mem e (v_of lca) /\ L.mem e (v_of s1') /\ L.mem e (v_of s2) ==> snd e <> get_ele last2); 
  lem_not_ele_diff1 (v_of lca) (v_of s1') (v_of s2) (do (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2) (get_ele last2);
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s1') (v_of lca)))); 
  lem_not_ele_diff (v_of s1') (v_of s1) (v_of lca) last1 (get_ele last2);
  assert (not (mem_ele (get_ele last2) (diff_s (v_of s1) (v_of lca))));
  ()
#pop-options

#push-options "--z3rlimit 500"
let ind_case_last1_neq_pre1 (lca s1 s2:st)
 : Lemma (requires common_pre1 lca s1 s2 /\ 
                   length (ops_of s1) > length (ops_of lca) /\
                   (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)))
         (ensures (let s1' = inverse_st s1 in
                   common_pre1 lca s1' s2)) =
 let s1' = inverse_st s1 in
 let s2' = inverse_st s2 in
 lem_inverse (ops_of lca) (ops_of s1);
 assert (is_prefix (ops_of lca) (ops_of s1')); 
 inverse_diff_id (ops_of lca) (ops_of s1) (ops_of s2);
 assert (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))));
 lastop_diff (ops_of lca) (ops_of s1);
 assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1') (ops_of lca)) ==> lt id id1); 
 general lca s1' s2;
 assert (forall id. mem_id_s id (diff_s (v_of s1') (v_of lca)) ==> not (mem_id_s id (v_of s2)));
 lem_merge_pre (v_of lca) (v_of s1') (v_of s2);
 assert (concrete_merge_pre (v_of lca) (v_of s1') (v_of s2));
 assert (common_pre1 lca s1' s2);
 ()

let ind_case_last1_neq_pre2 (lca s1 s2:st)
 : Lemma (requires common_pre1 lca s1 s2 /\ 
                   length (ops_of s1) > length (ops_of lca) /\
                   (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)))
         (ensures (let s1' = inverse_st s1 in
                   let s2' = inverse_st s2 in
                   concrete_merge_pre (v_of lca) (v_of s1') (v_of s2'))) =
 let s1' = inverse_st s1 in
 ind_case_last1_neq_pre1 lca s1 s2;
 let s2' = inverse_st s2 in
 lem_inverse (ops_of lca) (ops_of s2);
 assert (is_prefix (ops_of lca) (ops_of s2'));
 inverse_diff_id2 (ops_of lca) (ops_of s1) (ops_of s2);
 assert (forall id. mem_id id (diff (ops_of s1') (ops_of lca)) ==> not (mem_id id (diff (ops_of s2') (ops_of lca))));
 lastop_diff (ops_of lca) (ops_of s2);
 assert (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2') (ops_of lca)) ==> lt id id1);
 general lca s1' s2';
 assert (forall id. mem_id_s id (diff_s (v_of s1') (v_of lca)) ==> not (mem_id_s id (v_of s2')));
 lem_merge_pre (v_of lca) (v_of s1') (v_of s2')

let ind_case_last1_neq_pre3 (lca s1 s2:st)
 : Lemma (requires common_pre1 lca s1 s2 /\ 
                   length (ops_of s1) > length (ops_of lca) /\
                   (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)))
         (ensures (let s1' = inverse_st s1 in
                   let s2' = inverse_st s2 in
                   let _, last2 = un_snoc (ops_of s2) in
                   (ind_case_last1_neq_pre1 lca s1 s2;
                    ind_case_last1_neq_pre2 lca s1 s2;
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2))) =
 ind_case_last1_neq_pre1 lca s1 s2; 
 ind_case_last1_neq_pre2 lca s1 s2;
 let s2' = inverse_st s2 in
 let pre2, last2 = un_snoc (ops_of s2) in
 let s1' = inverse_st s1 in
 let pre1, last1 = un_snoc (ops_of s1) in
 assert (forall id. mem_id_s id (concrete_merge (v_of lca) (v_of s1) (v_of s2')) ==> 
               (mem_id_s id (v_of lca) \/ mem_id_s id (v_of s1) \/ mem_id_s id (v_of s2'))); 
 lem_foldl init_st (ops_of lca);
 assert (forall id. mem_id_s id (v_of lca) ==> mem_id id (ops_of lca));
 lem_foldl init_st (ops_of s1);
 assert (forall id. mem_id_s id (v_of s1) ==> mem_id id (ops_of s1));
 lem_foldl init_st (ops_of s2');
 assert (forall id. mem_id_s id (v_of s2') ==> mem_id id (ops_of s2'));
 lem_foldl init_st (ops_of s1');
 assert (forall id. mem_id_s id (v_of s1') ==> mem_id id (ops_of s1'));

 assert (forall id. mem_id_s id (concrete_merge (v_of lca) (v_of s1) (v_of s2')) ==> 
               (mem_id id (ops_of lca) \/ mem_id id (ops_of s1) \/ mem_id id (ops_of s2')));

 assert (forall id. mem_id_s id (concrete_merge (v_of lca) (v_of s1') (v_of s2')) ==> 
               (mem_id_s id (v_of lca) \/ mem_id_s id (v_of s1') \/ mem_id_s id (v_of s2')));
 inverse_diff_id_last2 (ops_of lca) (ops_of s1) (ops_of s2);
 assert (forall id. (mem_id id (ops_of lca) \/ mem_id id (ops_of s1') \/ mem_id id (ops_of s2')) ==> id <> fst last2);
 ()

let lem_exists_new (lastop:log_entry) (l:log)
  : Lemma (ensures exists_triple lastop l <==>
                   (exists op. mem op l /\
                         (let pre,suf = pre_suf l op in
                          not (commutative lastop op) /\
                          last (resolve_conflict lastop op) = op /\
                          commutative_seq op suf)))
  = ()

let commu_seq_prop (op:log_entry) (l:log)
  : Lemma (requires Add? (snd op))
          (ensures commutative_seq op l <==> (forall e. mem e l ==> ~ (get_ele op = get_ele e /\ Rem? (snd e)))) = ()

let commu_seq_prop_l (op:log_entry) (l':log) (last1:log_entry)
  : Lemma (requires Add? (snd op) /\ get_ele last1 <> get_ele op /\ commutative_seq op l')
          (ensures commutative_seq op (snoc l' last1)) = 
  lemma_mem_snoc l' last1;
  commu_seq_prop op l';
  commu_seq_prop op (snoc l' last1)

let ind_case_last1_neq_pre4_help1 (l:log) (last2:log_entry)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd last2) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 <> get_ele last2 /\
                    exists_triple last2 l'))
          (ensures exists_triple last2 l) 
          [SMTPat (let l', last1 = un_snoc l in
                   (exists_triple last2 l'))] =
  let l', last1 = un_snoc l in
  lem_exists_new last2 l';
  let pre', op', suf' = find_triple last2 l' in
  lemma_mem_snoc l' last1;
  assert (mem op' l);
  let pre, suf = pre_suf l op' in
  commu_seq_prop op' suf';
  
  assert ((snoc pre op') ++ suf = snoc ((snoc pre' op') ++ suf') last1);
  append_assoc (snoc pre' op') suf' (create 1 last1);
  assert ((snoc pre op') ++ suf = ((snoc pre' op') ++ (snoc suf' last1)));
  lem_suf_equal4 l op';
  distinct_invert_append l' (create 1 last1);
  lem_suf_equal4 l' op';

  not_mem_id l' last1;
  mem_ele_id op' l;
  mem_ele_id op' l';
  lem_id_not_snoc l' suf' last1 op'; 
  assert (not (mem_id (fst op') (snoc suf' last1)));
 
  count_1 l;
  assert (count_id (fst op') (snoc pre op' ++ suf) = 1);
  lem_count_1 pre suf pre' (snoc suf' last1) op';
  
  assert (length suf = length (snoc suf' last1));
  lemma_append_inj (snoc pre op') suf (snoc pre' op') (snoc suf' last1);
  assert (suf = snoc suf' last1);
  commu_seq_prop_l op' suf' last1;
  assert (commutative_seq op' suf);
  lem_exists_new last2 l
                    
let ind_case_last1_neq_pre4_help (l:log) (last2:log_entry)
  : Lemma (requires distinct_ops l /\ length l > 0 /\
                    Rem? (snd last2) /\
                   (let l', last1 = un_snoc l in
                    get_ele last1 <> get_ele last2))
          (ensures (let l', last1 = un_snoc l in 
                    (exists_triple last2 l' ==> exists_triple last2 l) /\
                    (not (exists_triple last2 l) ==> not (exists_triple last2 l')))) = ()
                    
let ind_case_last1_neq_pre4 (lca s1 s2:st)
 : Lemma (requires common_pre1 lca s1 s2 /\ 
                   length (ops_of s1) > length (ops_of lca) /\
                   (let _, last2 = un_snoc (ops_of s2) in
                    let _, last1 = un_snoc (ops_of s1) in
                    Rem? (snd last2) /\ get_ele last1 <> get_ele last2 /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)))
         (ensures (let s1' = inverse_st s1 in
                   let s2' = inverse_st s2 in
                   let _, last2 = un_snoc (ops_of s2) in
                   (ind_case_last1_neq_pre1 lca s1 s2;
                    ind_case_last1_neq_pre2 lca s1 s2;
                    ind_case_last1_neq_pre3 lca s1 s2;
                    (not (exists_triple last2 (diff (ops_of s1') (ops_of lca))))))) = 
 ind_case_last1_neq_pre1 lca s1 s2;
 ind_case_last1_neq_pre2 lca s1 s2;
 ind_case_last1_neq_pre3 lca s1 s2;
 let s1' = inverse_st s1 in
 let _, last2 = un_snoc (ops_of s2) in
 let pre1, last1 = un_snoc (ops_of s1) in
 let pre1d, last1d = un_snoc (diff (ops_of s1) (ops_of lca)) in
 lem_diff (ops_of s1) (ops_of lca);
 assert (last1 = last1d);
 assert (get_ele last1d <> get_ele last2);
 assert ((diff (ops_of s1') (ops_of lca)) = pre1d);
 ind_case_last1_neq_pre4_help (diff (ops_of s1) (ops_of lca)) last2
#pop-options
                    
#push-options "--z3rlimit 2500 --fuel 1 --ifuel 1"
let rec linearizable_gt0_inv2_c3_new1 (lca s1 s2:st)
 : Lemma (requires common_pre1 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Rem? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))
         (decreases %[length (ops_of s1)]) =
   let _, last2 = un_snoc (ops_of s2) in
   let s2' = inverse_st s2 in
   if ops_of s1 = ops_of lca then
     base_case lca s1 s2
   else 
     (assert ((length (ops_of s1) > length (ops_of lca)));
      let _, last1 = un_snoc (ops_of s1) in
      not_add_eq lca s1 s2;
      assert (~ (Add? (snd last1) /\ get_ele last1 = get_ele last2));
      let s1' = inverse_st s1 in
      if Rem? (snd last1) && get_ele last1 = get_ele last2 then
        ind_case_last1_rem_eq lca s1 s2
      else if get_ele last1 <> get_ele last2 then
        (ind_case_last1_neq_pre1 lca s1 s2;
         assert (common_pre1 lca s1' s2);
         ind_case_last1_neq_pre2 lca s1 s2;
         assert (concrete_merge_pre (v_of lca) (v_of s1') (v_of s2')); 
         ind_case_last1_neq_pre3 lca s1 s2;
         assert (concrete_do_pre (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2);
         ind_case_last1_neq_pre4 lca s1 s2;
         assert (not (exists_triple last2 (diff (ops_of s1') (ops_of lca))));
         linearizable_gt0_inv2_c3_new1 lca s1' s2;
         ind_case_last1_neq lca s1 s2)
      else ())

#push-options "--z3rlimit 500" // --fuel 1 --ifuel 1"
(*let rec linearizable_gt0_inv2_c3_new (lca s1 s2:st)
 : Lemma (requires common_pre1 lca s1 s2 /\ 
                   (let _, last2 = un_snoc (ops_of s2) in
                    Rem? (snd last2) /\
                    not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   (let s2' = inverse_st s2 in
                    is_prefix (ops_of lca) (ops_of s2') /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2') /\
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let s2' = inverse_st s2 in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))
         (decreases %[length (ops_of s1); length (ops_of s2)]) =
   let _, last2 = un_snoc (ops_of s2) in
   let s2' = inverse_st s2 in
   if ops_of s1 = ops_of lca then
     if ops_of s2' = ops_of lca then
       admit() //base_case1 lca s1 s2
     else (assume ((length (ops_of s2') > length (ops_of lca)));
           let s2'' = inverse_st s2' in 
           assume (concrete_do_pre (v_of s2'') last2);
           assume (not (mem_id (fst last2) (ops_of s2'')));
           let s2''l = (do (v_of s2'') last2, hide (snoc (ops_of s2'') last2)) in
           assume (common_pre1 lca s1 s2''l); admit();
                   //not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                   //concrete_merge_pre (v_of lca) (v_of s1) (v_of s2''l) /\
                   //concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of s2''l)) last2); admit();
           (*linearizable_gt0_inv2_c3_new lca s1 s2''l;
           assume (eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) last2)
                      (concrete_merge (v_of lca) (v_of s1) (v_of s2)));
           ()*) ())
     
     //base_case lca s1 s2
   
   else 
     (admit()(*;assert ((length (ops_of s1) > length (ops_of lca)));
      let _, last1 = un_snoc (ops_of s1) in
      not_add_eq lca s1 s2;
      assert (~ (Add? (snd last1) /\ get_ele last1 = get_ele last2));
      let s1' = inverse_st s1 in
      if Rem? (snd last1) && get_ele last1 = get_ele last2 then
        ind_case_last1_rem_eq lca s1 s2
      else if Rem? (snd last1) && get_ele last1 <> get_ele last2 then
        (assume (common_pre2 lca s1' s2 /\
                 not (exists_triple last2 (diff (ops_of s1') (ops_of lca))) /\
`                 concrete_merge_pre (v_of lca) (v_of s1') (v_of s2') /\
                 concrete_do_pre (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2);
        linearizable_gt0_inv2_c3_new lca s1' s2;
        ind_case_last1_rem_neq lca s1 s2)
      else if Add? (snd last1) && get_ele last1 <> get_ele last2 then
        (assume (common_pre2 lca s1' s2 /\
                 not (exists_triple last2 (diff (ops_of s1') (ops_of lca))) /\
                 concrete_merge_pre (v_of lca) (v_of s1') (v_of s2') /\
                 concrete_do_pre (concrete_merge (v_of lca) (v_of s1') (v_of s2')) last2);
         linearizable_gt0_inv2_c3_new lca s1' s2;
         ind_case_last1_add_neq lca s1 s2)
      else ()*))*)


(*

let linearizable_gt0_pre_inv2'_1 (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\
                    (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                     suf2 = snd (pre_suf (ops_of s2) op2) /\
                    (let inv2 = inverse_st_op s2 op2 in
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let inv2 = inverse_st_op s2 op2 in
                    fst last1 <> fst op2 /\
                    Add? (snd op2) /\ Rem? (snd last1) /\ get_ele last1 = get_ele op2 /\
                    L.mem (fst op2, get_ele op2) (v_of s2) /\
                    (forall e. L.mem e (v_of inv2) <==> (L.mem e (v_of s2) /\ e <> (fst op2, get_ele op2))))) =
  let _, last1 = un_snoc (ops_of s1) in
  let (_, op, suf) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  let inv2 = inverse_st_op s2 op in
  mem_ele_id op (diff (ops_of s2) (ops_of lca));
  assert (mem_id (fst op) (diff (ops_of s2) (ops_of lca)));
  lastop_diff (ops_of lca) (ops_of s1);
  assert (mem_id (fst last1) (diff (ops_of s1) (ops_of lca))); 
  id_not_eq (diff (ops_of s1) (ops_of lca)) (diff (ops_of s2) (ops_of lca)) (fst last1) (fst op);
  assert (fst op <> fst last1);
  resolve_conflict_prop last1 op;
  assert (Add? (snd op) /\ Rem? (snd last1) /\ get_ele last1 = get_ele op);
  do_prop (v_of inv2) op; 
  assert (L.mem (fst op, get_ele op) (v_of s2)); 
  assert (forall e. (L.mem e (v_of inv2) \/ e = (fst op, get_ele op)) <==> L.mem e (v_of s2)); 
  assert (forall e. L.mem e (v_of inv2) <==> (L.mem e (v_of s2) /\ e <> (fst op, get_ele op))); ()
  
let linearizable_gt0_pre_inv2' (lca s1 s2:st)
  : Lemma (requires common_pre lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\
                    (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                     suf2 = snd (pre_suf (ops_of s2) op2) /\
                    (let inv2 = inverse_st_op s2 op2 in
                     concrete_merge_pre (v_of lca) (v_of s1) (v_of inv2)))))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                   (let (_, op2, _) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                   (let inv2 = inverse_st_op s2 op2 in
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) op2)))) =
  linearizable_gt0_pre_inv2'_1 lca s1 s2;
  let _, last1 = un_snoc (ops_of s1) in
  let (_, op, suf) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
  let inv2 = inverse_st_op s2 op in
  lem_foldl init_st (ops_of lca);
  split_prefix init_st (ops_of lca) (ops_of s2);
  lem_foldl (v_of lca) (diff (ops_of s2) (ops_of lca));
  lem_suf_equal2 (ops_of lca) (ops_of s2) op;
  assert (not (mem_id_s (fst op) (v_of lca)));
  no_id_not_ele (fst op, get_ele op) (v_of lca);
  assert (not (L.mem (fst op, get_ele op) (v_of lca)));
  assert (L.mem (fst op, get_ele op) (diff_s (v_of s2) (v_of lca)));
  assert (forall e. L.mem e (diff_s (v_of inv2) (v_of lca)) <==>
               L.mem e (diff_s (v_of s2) (v_of lca)) /\ e <> (fst op, get_ele op)); 
  assert (forall e. ((L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of s2)) /\ e <> (fst op, get_ele op)) <==>
               (L.mem e (v_of lca) /\ L.mem e (v_of s1) /\ L.mem e (v_of inv2))); 
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of inv2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) /\ e <> (fst op, get_ele op))); 
  lemma2 (concrete_merge (v_of lca) (v_of s1) (v_of inv2))
         (concrete_merge (v_of lca) (v_of s1) (v_of s2))
         (fst op, get_ele op);
  assert (not (L.mem (fst op, get_ele op) (concrete_merge (v_of lca) (v_of s1) (v_of inv2))));
  admit()
    
    *)
