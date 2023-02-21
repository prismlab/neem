module App

open FStar.Seq
open FStar.Ghost
module L = FStar.List.Tot

let rec mem_id_s (id:nat) (l:list (nat * string))
    : Tot (b:bool {b = true <==> (exists m. L.mem (id,m) l) /\ (exists e. L.mem e l ==> fst e = id)}) =
  match l with
  |[] -> false
  |(id1,m)::xs -> id = id1 || mem_id_s id xs

let rec unique_s (l:list (nat * string)) =
  match l with
  |[] -> true
  |(id,m)::xs -> not (mem_id_s id xs) && unique_s xs

let rec pos (id:nat * string) (l:list (nat * string) {L.mem id l /\ unique_s l}) : Tot nat =
  match l with
  |id1::xs -> if id = id1 then 0 else 1 + pos id xs

let rec total_order (l:list (nat * string) {unique_s l}) : prop =
  match l with
  |[] -> true
  |[x] -> true
  |x::xs ->  (forall e. L.mem e xs ==> lt (fst e) (fst x)) /\  total_order xs

let ord (id:(nat * string)) (id1:(nat * string) {fst id <> fst id1})
        (l:list (nat * string) {L.mem id l /\ L.mem id1 l /\ unique_s l /\ total_order l})
        : Tot (b:bool {b = true <==> pos id l < pos id1 l})
    = pos id l < pos id1 l 

// the concrete state type
// It is a list of pairs of timestamp and message ordered in descending order of timestamps
type concrete_st = l:list (nat (*timestamp*) * string (*message*)) {unique_s l /\ total_order l}

//initial state
let init_st = []

let eq (a b:concrete_st) = a == b

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
// (the only operation is append value, so string is fine)
type op_t = string

// concrete do pre-condition
let concrete_do_pre (s:concrete_st) (op:log_entry) : prop = 
  (*L.length s > 0 ==> lt (fst (L.hd s)) (fst op)*)
  (forall id. mem_id_s id s ==> lt id (fst op))

// apply an operation to a state
let do (s:concrete_st) (op:log_entry{concrete_do_pre s op}) 
  : (r:concrete_st{(forall e. L.mem e r <==> (L.mem e s \/ e = op))})
  = op::s

let lem_do (a b:concrete_st) (op:log_entry)
   : Lemma (requires concrete_do_pre a op /\ eq a b)
           (ensures concrete_do_pre b op /\ eq (do a op) (do b op)) = ()
           
let lem_cons (#a:eqtype) (s:list a) (op:a)
  : Lemma (ensures (forall e. L.mem e (op::s) <==> L.mem e s \/ e = op)) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = list (nat * string)

// init state 
let init_st_s = []

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:log_entry) : concrete_st_s = op::s

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = st_s == st

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:log_entry)
  : Lemma (requires eq_sm st_s st /\ concrete_do_pre st op)
          (ensures eq_sm (do_s st_s op) (do st op)) 
  = ()

////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 50"
let rec lem_foldl (s:concrete_st) (l:log)
  : Lemma (requires foldl_prop s l)
          (ensures (length l = 0 ==> (seq_foldl s l = s)) /\ 
                   (forall e. L.mem e (seq_foldl s l) <==> L.mem e s \/ mem e l) /\
                   (forall id. mem_id_s id (seq_foldl s l) <==> mem_id_s id s \/ mem_id id l) /\
                   (length l > 0 ==> (let p,last = un_snoc l in
                           (foldl_prop s p /\
                           (forall e. L.mem e (seq_foldl s l) <==> L.mem e (seq_foldl s p) \/ e = last) /\
                           (forall e. L.mem e (seq_foldl s l) <==> L.mem e (seq_foldl s p) \/ e = last) /\  
                           (forall id. mem_id_s id (seq_foldl s l) <==> mem_id_s id (seq_foldl s p) \/ id = fst (last)) /\
                           concrete_do_pre (seq_foldl s p) (last) /\
                           (seq_foldl s l == do (seq_foldl s p) (last))))))
          (decreases length l)
  = match length l with
    |0 -> ()
    |1 -> ()
    |_ -> lem_foldl (do s (head l)) (tail l)
#pop-options

//conflict resolution
let resolve_conflict (x y:log_entry) : (l:log{forall e. mem e l <==> e = x \/ e = y}) =
  if lt (fst y) (fst x)
    then cons y (cons x empty)
      else cons x (cons y empty)

#push-options "--z3rlimit 50"
let resolve_conflict_prop (x y:log_entry)
  : Lemma (requires fst x <> fst y)
          (ensures (lt (fst y) (fst x) <==> last (resolve_conflict x y) = x) /\
                   (last (resolve_conflict x y) <> x <==> lt (fst x) (fst y)))
  = ()

let rec filter_s (f:((nat * string) -> bool)) (l:concrete_st)
             : Tot (l1:concrete_st {(forall e. L.mem e l1 <==> L.mem e l /\ f e)}) = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter_s f tl) else filter_s f tl

let rec filter_uni (f:((nat * string) -> bool)) (l:concrete_st)
  : Lemma (ensures (unique_s (filter_s f l) /\ total_order (filter_s f l)) /\
                   (forall e. L.mem e l /\ f e <==> L.mem e (filter_s f l)) /\
                   (forall e e1. L.mem e l /\ L.mem e1 l /\ f e /\ f e1 /\ lt (fst e1) (fst e) /\ ord e e1 l <==>
       L.mem e (filter_s f l) /\ L.mem e1 (filter_s f l) /\ lt (fst e1) (fst e) /\ ord e e1 (filter_s f l)))
                               [SMTPat (filter_s f l)] =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

let rec remove_ele (ele:(nat * string)) (a:concrete_st)
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

let rec diff_s (a:concrete_st) (l:concrete_st)
  : Pure concrete_st
    (requires (forall e. L.mem e l ==> L.mem e a))
    (ensures (fun r -> (forall e. L.mem e r <==> L.mem e a /\ not (L.mem e l)) /\
                    (forall id. mem_id_s id r <==> mem_id_s id a /\ not (mem_id_s id l)) /\
                    (forall e e1. L.mem e r /\ L.mem e1 r /\ lt (fst e1) (fst e) /\ ord e e1 r <==>
             L.mem e a /\ L.mem e1 a /\ not (L.mem e l) /\ not (L.mem e1 l) /\ lt (fst e1) (fst e) /\ ord e e1 a)))
             (decreases l) =
  match l with
  |[] -> a
  |x::xs -> diff_s (remove_ele x a) xs
  
// concrete merge pre-condition
let concrete_merge_pre l a b = 
  (forall e. L.mem e l ==> L.mem e a /\ L.mem e b) /\
  (forall id. mem_id_s id (diff_s a l) ==> not (mem_id_s id (diff_s b l)))

// concrete merge operation
let concrete_merge (lca:concrete_st) (s1:concrete_st) (s2:concrete_st{concrete_merge_pre lca s1 s2}) 
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

#push-options "--z3rlimit 100"
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
  
let merge_inv_s1_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) = last1))
          (ensures concrete_merge_pre (v_of lca) (v_of (inverse_st s1)) (v_of s2)) = 
  lem_inverse (ops_of lca) (ops_of s1);
  lastop_diff (ops_of lca) (ops_of s1); 
  inverse_diff_id (ops_of lca) (ops_of s1) (ops_of s2);
  merge_prop lca (inverse_st s1) s2

let merge_inv_s2_prop (lca s1 s2:st)
  : Lemma (requires is_prefix (ops_of lca) (ops_of s1) /\
                    is_prefix (ops_of lca) (ops_of s2) /\
                    Seq.length (ops_of s1) > Seq.length (ops_of lca) /\
                    Seq.length (ops_of s2) > Seq.length (ops_of lca) /\
                    concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                    (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                    (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     last (resolve_conflict last1 last2) <> last1))
          (ensures concrete_merge_pre (v_of lca) (v_of s1) (v_of (inverse_st s2))) =
  lem_inverse (ops_of lca) (ops_of s2);
  lastop_diff (ops_of lca) (ops_of s2); 
  inverse_diff_id (ops_of lca) (ops_of s2) (ops_of s1);
  merge_prop lca s1 (inverse_st s2)

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
  if last (resolve_conflict last1 last2) = last1 then
    merge_inv_s1_prop lca s1 s2 else
      merge_inv_s2_prop lca s1 s2

let rec lem_length (a b:concrete_st) 
  : Lemma (requires (forall e. L.mem e a <==> L.mem e b))
          (ensures (List.Tot.length a = List.Tot.length b)) =
  match a,b with
  |[],[] -> ()
  |x::xs,_ -> lem_length xs (remove_ele x b)
  |[],_ -> ()
  
let rec lem_equal (a b:concrete_st)
  : Lemma (requires (forall e. L.mem e a <==> L.mem e b) /\
                    (List.Tot.length a = List.Tot.length b))
          (ensures a = b) =
  match a,b with
  |[],[] -> ()
  |x::xs, y::ys -> lem_equal xs ys

let linearizable_s1_0' (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                ops_of s1 = ops_of lca /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
      (ensures (forall e. L.mem e (v_of s2) <==> L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = ()

let linearizable_s1_0 (lca s1 s2:st)
  : Lemma 
      (requires concrete_merge_pre (v_of lca) (v_of s1) (v_of s2) /\
                is_prefix (ops_of lca) (ops_of s1) /\
                is_prefix (ops_of lca) (ops_of s2) /\
                ops_of s1 = ops_of lca /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
                (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
                (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca)))) /\
                foldl_prop (v_of lca) (diff (ops_of s2) (ops_of lca)))
      (ensures v_of s2 == concrete_merge (v_of lca) (v_of s1) (v_of s2))
  = linearizable_s1_0' lca s1 s2;
    lem_length (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2));
    lem_equal (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))
  
let linearizable_s2_0' (lca s1 s2:st)
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
      (ensures (forall e. L.mem e (v_of s1) <==> L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)))) = ()

let linearizable_s2_0 (lca s1 s2:st)
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
       (ensures v_of s1 == concrete_merge (v_of lca) (v_of s1) (v_of s2))
  = linearizable_s2_0' lca s1 s2;
    lem_length (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2));
    lem_equal (v_of s1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))
#pop-options

let lem_merge (l:concrete_st) (a:concrete_st) (b:concrete_st{concrete_merge_pre l a b})
  : Lemma (ensures (forall id. mem_id_s id (concrete_merge l a b) <==> (mem_id_s id l \/ mem_id_s id a \/ mem_id_s id b)) /\
                   (forall e. L.mem e (concrete_merge l a b) <==> (L.mem e l \/ L.mem e a \/ L.mem e b))) = ()
  
#push-options "--z3rlimit 100"
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
                   (forall id. mem_id_s id (v_of (inverse_st s1)) ==> lt id (fst last1)) /\
                   (forall id. mem_id_s id (v_of lca) ==> lt id (fst last1)))) =
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s1)

let linearizable_s1_gt02 (lca s1 s2:st)
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
                   (forall id. mem_id_s id (v_of s2) ==> lt id (fst last1)))) =
  let _, last1 = un_snoc (ops_of s1) in 
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  lem_foldl init_st (ops_of s2)
  
let linearizable_s1_gt03 (lca s1 s2:st)
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
                   concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) =
  let p1, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  linearizable_s1_gt01 lca s1 s2;
  linearizable_s1_gt02 lca s1 s2;
  lem_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)

let linearizable_s1_gt04 (lca s1 s2:st)
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
                     last (resolve_conflict last1 last2) = last1 /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1))
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                          L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)))) =
  let p1, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  inverse_helper init_st p1 last1; 
  lem_merge (v_of lca) (v_of s1) (v_of s2);
  lem_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2);
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) <==>
               (L.mem e (v_of lca) \/ L.mem e (v_of (inverse_st s1)) \/ L.mem e (v_of s2)));
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) \/ e = last1)); 
  lem_cons (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1;
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               L.mem e (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1));
  ()

let linearizable_s1_gt0 (lca s1 s2:st)
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
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)) =
  linearizable_s1_gt03 lca s1 s2;
  linearizable_s1_gt04 lca s1 s2;
  let _, last1 = un_snoc (ops_of s1) in
  lem_length (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1) (concrete_merge (v_of lca) (v_of s1) (v_of s2));   
  lem_equal (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1) (concrete_merge (v_of lca) (v_of s1) (v_of s2))
#pop-options

#push-options "--z3rlimit 200"
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
                     last (resolve_conflict last1 last2) = last2))
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                   (forall id. mem_id_s id (v_of (inverse_st s2)) ==> lt id (fst last2)) /\
                   (forall id. mem_id_s id (v_of lca) ==> lt id (fst last2)))) =
  lem_foldl init_st (ops_of lca);
  lem_foldl init_st (ops_of s2)

let linearizable_s2_gt02 (lca s1 s2:st)
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
                     last (resolve_conflict last1 last2) = last2))
           (ensures (let _, last2 = un_snoc (ops_of s2) in
                   (forall id. mem_id_s id (v_of s1) ==> lt id (fst last2)))) =
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2; 
  lem_foldl init_st (ops_of s1)

let linearizable_s2_gt03 (lca s1 s2:st)
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
                     last (resolve_conflict last1 last2) = last2))
           (ensures (let _, last2 = un_snoc (ops_of s2) in
                    concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) =
  let p1, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  linearizable_s2_gt01 lca s1 s2;
  linearizable_s2_gt02 lca s1 s2;
  lem_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))

let linearizable_s2_gt04 (lca s1 s2:st)
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
                     last (resolve_conflict last1 last2) = last2 /\
                     concrete_do_pre (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2))
           (ensures (let _, last2 = un_snoc (ops_of s2) in
                     (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
                           L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)))) =
  let p1, last1 = un_snoc (ops_of s1) in
  let p2, last2 = un_snoc (ops_of s2) in
  inverse_helper init_st p2 last2; 
  lem_merge (v_of lca) (v_of s1) (v_of s2);
  lem_merge (v_of lca) (v_of s1) (v_of (inverse_st s2));
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) <==>
               (L.mem e (v_of lca) \/ L.mem e (v_of s1) \/ L.mem e (v_of (inverse_st s2))));
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               (L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) \/ e = last2)); 
  lem_cons (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2;
  assert (forall e. L.mem e (concrete_merge (v_of lca) (v_of s1) (v_of s2)) <==>
               L.mem e (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2));
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
                   concrete_merge (v_of lca) (v_of s1) (v_of s2) ==
                   do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)) =
  let _,last1 = un_snoc (ops_of s1) in
  let _,last2 = un_snoc (ops_of s2) in
  lastop_neq (ops_of lca) (ops_of s1) (ops_of s2);
  resolve_conflict_prop last1 last2;
  linearizable_s2_gt03 lca s1 s2;
  linearizable_s2_gt04 lca s1 s2;
  let _, last2 = un_snoc (ops_of s2) in
  lem_length (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2) (concrete_merge (v_of lca) (v_of s1) (v_of s2));   
  lem_equal (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2) (concrete_merge (v_of lca) (v_of s1) (v_of s2))

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
  let _, last1 = un_snoc (ops_of s1) in
  let _, last2 = un_snoc (ops_of s2) in
  if last (resolve_conflict last1 last2) = last1 then
    linearizable_s1_gt0 lca s1 s2 else
      linearizable_s2_gt0 lca s1 s2

let lem_mem (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ s1' == do s1 o /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures (forall e. L.mem e (concrete_merge lca s1' s2) <==> L.mem e (concrete_merge s1 (concrete_merge lca s1 s2) s1'))) 
  = ()

let convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ s1' == do s1 o /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures concrete_merge lca s1' s2 == concrete_merge s1 (concrete_merge lca s1 s2) s1') =
  lem_mem lca s1 s2 s1' o;
  lem_length (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1');
  lem_equal (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1')
#pop-options
