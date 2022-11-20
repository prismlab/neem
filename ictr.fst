module Ictr

module L = FStar.List.Tot
open FStar.Ghost
open FStar.Seq.Base
open FStar.Seq.Properties

type op =
  | Inc

type ctr_st = nat //concrete state of the counter
type st = ctr_st & (erased (seq (ctr_st & (nat (*id*) & op))))

val init : st
let init = (0, hide empty)

val get_id : (nat * op) -> nat
let get_id (id, o) = id

val get_op : (ctr_st * (nat * op)) -> (nat * op)
let get_op (_, o) = o

val get_val : st -> ctr_st
let get_val (c, _) = c

val get_seq : st -> GTot (seq (ctr_st * (nat * op)))
let get_seq (st, seq) = (reveal seq)

val get_st : (ctr_st * (nat * op)) -> ctr_st
let get_st (st, o) = st

val get_init : c:st -> GTot nat
let get_init c = 
  if (length (get_seq c) > 0) then get_st (head (get_seq c)) else get_val c

val last_op : c:st{length (get_seq c) > 0} -> GTot (nat * op)
let last_op c = get_op (last (get_seq c))

val inverse : c:st{length (get_seq c) > 0} -> GTot ctr_st
let inverse c = get_st (last (get_seq c))

val st_i : c:st{length (get_seq c) > 0} -> i:nat{i < length (get_seq c)} -> GTot ctr_st
let st_i c i = (get_st (index (get_seq c) i))

val op_i : c:st{length (get_seq c) > 0} -> i:nat{i < length (get_seq c)} -> GTot (nat * op)
let op_i c i = (get_op (index (get_seq c) i))

let pre_cond_do s op = true 

val do : c:ctr_st -> (nat * op) -> c1:ctr_st{c1 > c}
let do c (_, Inc) = c + 1

val mem_id_l : id:nat -> s:(list (ctr_st & (nat (*id*) & op))) 
             -> Tot (b:bool{(exists e. L.mem e s /\ get_id (get_op e) = id)  <==> (b = true)})
let rec mem_id_l id s =
  match s with
  |[] -> false
  |x::xs -> id = get_id (get_op x) || mem_id_l id xs

val mem_id_s : id:nat -> c:(seq (ctr_st & (nat & op))) 
           -> Tot (b:bool{(exists e. mem e c /\ get_id (get_op e) = id) <==> (b = true)})
             (decreases length c)
let rec mem_id_s id c = 
  match length c with
  |0 -> false
  |_ -> id = get_id (get_op (head c)) || mem_id_s id (tail c)

val mem_id : id:nat -> c:st
           -> GTot (b:bool{(exists e. mem e (get_seq c) /\ get_id (get_op e) = id) <==> b = true})
let mem_id id c = mem_id_s id (get_seq c)

(*)val unique_id : (s:st) -> GTot bool
                (decreases (length (get_seq s)))
let rec unique_id s =
  match length (get_seq s) with
  |0 -> true
  |_ -> (not (mem_id_s (get_id (get_op (head (get_seq s)))) (hide (tail (get_seq s))))) &&
       (*unique_id (inverse s, hide (slice (get_seq s) 0 (length (get_seq s) - 1)))) &&*)
       (unique_id (get_val s, (hide (tail (get_seq s)))))*)

val unique_id_s : c:(seq (ctr_st & (nat & op)))  -> GTot bool
                  (decreases (length c))
let rec unique_id_s s =
  match length s with
  |0 -> true
  |_ -> not (mem_id_s (get_id (get_op (head s))) (tail s)) && unique_id_s (tail s)

val unique_id : (s:st) -> GTot bool
let unique_id s = unique_id_s (get_seq s)

val unique_id_l : s:(list (ctr_st & (nat & op))) 
                -> Tot bool
let rec unique_id_l s =
  match s with
  |[] -> true
  |x::xs -> not (mem_id_l (get_id (get_op x)) xs) && unique_id_l xs

(*)let unique_id (s:st) =
  unique_id_l (seq_to_list (get_seq s))*)

val count_id : id:nat -> s:seq(ctr_st & (nat (*id*) & op)) -> Tot nat (decreases length s)
let rec count_id id s =
  match length s with
  |0 -> 0 
  |_ -> if get_id (get_op (head s)) = id then 1 + count_id id (tail s) else count_id id (tail s)

let valid_st (c:st) = 
  (forall (i:nat). i < length (get_seq c) - 1 ==> (do (st_i c i) (op_i c i) = (st_i c (i+1)))) /\
  (*forall (id:nat). mem_id id c ==> count_id id (get_seq c) = 1) /\*)
  (forall (i:nat). i < length (get_seq c) - 1 ==> not (mem_id_s (get_id (op_i c i)) (slice (get_seq c) 0 i))
            (*)not (mem_id_s (get_id (op_i c i)) (slice (get_seq c) 0 i)*)) /\
  (length (get_seq c) > 0 ==> get_val c = do (inverse c) (last_op c)) 

val to_unique_ls : l:(list (ctr_st & (nat (*id*) & op))) 
              -> Lemma (requires true)
                      (ensures (forall e. L.mem e l <==> mem e (seq_of_list l)) /\
                               (unique_id_l l <==> unique_id_s (seq_of_list l)) /\ 
                               L.length l = length (seq_of_list l))
                      (decreases L.length l)
#set-options "--z3rlimit 1000"
let rec to_unique_ls l = 
  lemma_seq_of_list_induction l;
  match l with
  |[] -> ()
  |x::xs -> to_unique_ls xs
  
(*)val rem_last : s:(seq (ctr_st & (nat & op))){length s > 0 /\ unique_id_s s}
             -> Pure (seq (ctr_st & (nat & op)))
               (requires length s > 0 /\ unique_id_s s)
               (ensures (fun s1 -> (length s1 = length s - 1) /\
                                (forall e. mem e s /\ e <> last s <==> mem e s1)
                                (*forall id. mem_id_s id s <==> mem_id_s id s1 \/ id = get_id (get_op (last s))*)))
               (decreases length s)

#set-options "--z3rlimit 1000"
let rem_last s = 
  match length s with
  |1 -> empty
  |_ -> slice s 0 (length s - 1)*)
 
val to_unique_sl : s:(seq (ctr_st & (nat & op)))
                -> Lemma (requires true)
                        (ensures (forall e. mem e s <==> L.mem e (seq_to_list s))  /\
                                 (unique_id_s s <==> unique_id_l (seq_to_list s)) /\ 
                                 length s = L.length (seq_to_list s) /\
                                 (length s > 0 ==> (forall e. mem e (slice s 0 (length s - 1)) ==> mem e s) /\
                                         (length (slice s 0 (length s - 1)) = length s - 1) /\
                                 (forall id. mem_id_s id (slice s 0 (length s - 1)) ==> mem_id_s id s)))
                        (decreases length s)

#set-options "--z3rlimit 1000"
let rec to_unique_sl s = 
  match length s with
  |0 -> ()
  |_ ->  to_unique_sl (tail s)

val init_le_inv : c:st
           -> Lemma (requires valid_st c /\ length (get_seq c) > 0)
                   (ensures get_init c <= inverse c /\ get_val c = get_init c + length (get_seq c))
                   (decreases (length (get_seq c)))

#set-options "--z3rlimit 1000"
let rec init_le_inv c = 
  match (length (get_seq c)) with
  |0 -> ()
  |1 -> ()
  |_ -> init_le_inv (inverse c, hide (slice (get_seq c) 0 (length (get_seq c) - 1)))

val pre_cond_merge : l:ctr_st -> a:ctr_st -> b:ctr_st -> bool
let pre_cond_merge l a b = a >= l && b >= l

val merge : l:ctr_st -> a:ctr_st -> b:ctr_st
           -> Pure ctr_st (requires pre_cond_merge l a b)
                    (ensures (fun r -> r = a + b - l))
let merge l a b =
  a + b - l

//equivalence relation between 2 states
val eq_m : a:ctr_st -> b:ctr_st -> bool
let eq_m a b = a = b

(*)val spec : ctr_st -> (nat * op) -> (nat * op) -> nat
let spec a o1 o2 =
    do (do a o1) o2*)

val mem_op_s : o:(nat * op) -> s:(seq (ctr_st & (nat & op))) 
             -> Tot (b:bool{(exists e. mem e s /\ get_op e = o)  <==> (b = true)})
             (decreases length s)
let rec mem_op_s o s =
  match length s with
  |0 -> false
  |_ -> get_op (head s) = o || mem_op_s o (tail s)

let mem_op (o:(nat * op)) (s:st) =
  mem_op_s o (get_seq s)

(*)val lem_spec : l:st -> a:st -> b:st
             -> o1:(nat * op) -> o2:(nat * op)
             -> Lemma (requires get_id o1 <> get_id o2 /\
                               (get_val a) = do (get_val l) o1 /\ (get_val b) = do (get_val l) o2)
                     (ensures pre_cond_merge (get_val l) (get_val a) (get_val b) /\ 
                              eq_m (spec (get_val l) o1 o2) (merge (get_val l) (get_val a) (get_val b)) /\
                              (exists (s:st). valid_st s /\ get_init s = get_val l /\
                              (forall o. mem_op o s <==> o = o1 \/ o = o2) /\
                              eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)))

#set-options "--z3rlimit 1000"
let lem_spec l a b o1 o2 = 
  let s = (spec (get_val l) o1 o2, hide (cons (get_val l, o1) (create 1 (do (get_val l) o1, o2)))) in
  assert (valid_st s /\ eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s));
  ()*)

val spec : a:ctr_st -> o1:(nat * op) -> o2:(nat * op){get_id o1 <> get_id o2} -> s:st{valid_st s}
let spec a o1 o2 =
  (do (do a o1) o2 , hide (cons (a, o1) (cons (do a o1, o2) empty))) 

val lem_spec : l:st -> a:st -> b:st
             -> o1:(nat * op) -> o2:(nat * op)
             -> Lemma (requires pre_cond_do (get_val l) o1 /\ pre_cond_do (get_val l) o2 /\ get_id o1 <> get_id o2 /\ 
                               valid_st l /\ valid_st a /\ valid_st b /\
                               length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                               get_val a = do (get_val l) o1 /\ get_val b = do (get_val l) o2 /\
                               pre_cond_merge (get_val l) (get_val a) (get_val b) )
                     (ensures (*)pre_cond_merge (get_val l) (get_val a) (get_val b) /\ *)
                         eq_m (get_val (spec (get_val l) o1 o2)) (merge (get_val l) (get_val a) (get_val b)) /\

                              (exists (s:st). valid_st s /\ get_init s = get_val l /\
                                (forall o. mem_op o s <==> o = o1 \/ o = o2) /\
                                      eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)))

#set-options "--z3rlimit 100000"
let lem_spec l a b o1 o2 = 
  (*)init_le_inv a; init_le_inv b;*)
  let s = spec (get_val l) o1 o2 in 
  introduce exists s. valid_st s /\ get_init s = get_val l /\ (forall o. mem_op o s <==> o = o1 \/ o = o2) /\
                   eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)
  with s
  and ()

val len_ab_gt0 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\
                                  length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b) /\
                                  (forall id. mem_id id l ==> not (mem_id id a)) /\
                                  (forall id. mem_id id a ==> not (mem_id id b)) /\
                                  (forall id. mem_id id l ==> not (mem_id id b)))
                         (ensures pre_cond_merge (get_val l) (inverse a) (inverse b) /\
                                  (let m = merge (get_val l) (inverse a) (inverse b) in
                                       eq_m (merge (get_val l) (get_val a) (get_val b))
                                            (*merge m (do m (last_op a)) (do m (last_op b))*)
                                            (do (do m (last_op a)) (last_op b)) /\

                                  (exists (s:st). valid_st s /\ get_init s = m /\
                                     (forall o. mem_op o s <==> o = last_op a \/ o = last_op b) /\ 
                                     eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s))))

#set-options "--z3rlimit 10000"
let len_ab_gt0 l a b =
  init_le_inv a;
  init_le_inv b;
  let m = merge (get_val l) (inverse a) (inverse b) in
  let s = ((do (do m (last_op a)) (last_op b)), hide (cons (m, last_op a) (cons (do m (last_op a), last_op b) empty))) in
  assume (valid_st s);
  assume (eq_m (merge (get_val l) (get_val a) (get_val b))
               (do (do m (last_op a)) (last_op b)));
  assume (get_init s = m); 
  assume (get_id (last_op a) <> get_id (last_op b)); 
  assume (forall o. mem_op o s ==> o = last_op a \/ o = last_op b);
  assume (forall o. o = last_op a \/ o = last_op b ==> mem_op o s); 
  assert (forall o. o = last_op a \/ o = last_op b <==> mem_op o s);
  introduce exists s. valid_st s /\ get_init s = m /\ (forall o. mem_op o s <==> o = last_op a \/ o = last_op b) /\ 
          eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)
  with s
  and ()

val len_b_gt0 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) = 0 /\ length (get_seq b) > 0 /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b) /\
                                  (forall id. mem_id id l ==> not (mem_id id a)) /\
                                  (forall id. mem_id id a ==> not (mem_id id b)) /\
                                  (forall id. mem_id id l ==> not (mem_id id b)))
                         (ensures pre_cond_merge (get_val l) (get_val a) (inverse b) /\
                                 (let m = merge (get_val l) (get_val a) (inverse b) in
                                      eq_m (merge (get_val l) (get_val a) (get_val b)) 
                                           (do m (last_op b)) /\

                                 (exists (s:st). valid_st s /\ get_init s = m /\
                                    (forall o. mem_op o s <==> o = last_op b) /\ 
                                    eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s))))

#set-options "--z3rlimit 1000"
let len_b_gt0 l a b = 
  init_le_inv b;
  let m = merge (get_val l) (get_val a) (inverse b) in
  let s = ((do m (last_op b)), hide (cons (m, last_op b) empty)) in
  introduce exists s. valid_st s /\ get_init s = m /\ (forall o. mem_op o s <==> o = last_op b) /\ 
          eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)
  with s
  and ()

val len_a_gt0 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) > 0 /\ length (get_seq b) = 0 /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b) /\
                                  (forall id. mem_id id l ==> not (mem_id id a)) /\
                                  (forall id. mem_id id a ==> not (mem_id id b)) /\
                                  (forall id. mem_id id l ==> not (mem_id id b)))
                        (ensures pre_cond_merge (get_val l) (inverse a) (get_val b) /\
                                 (let m = merge (get_val l) (inverse a) (get_val b) in
                                      eq_m (merge (get_val l) (get_val a) (get_val b))
                                           (do m (last_op a)) /\

                                 (exists (s:st). valid_st s /\ get_init s = m /\
                                    (forall o. mem_op o s <==> o = last_op a) /\ 
                                    eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s))))

#set-options "--z3rlimit 1000"
let len_a_gt0 l a b =
  init_le_inv a;
  let m = merge (get_val l) (inverse a) (get_val b) in
  let s = ((do m (last_op a)), hide (cons (m, last_op a) empty)) in
  introduce exists s. valid_st s /\ get_init s = m /\ (forall o. mem_op o s <==> o = last_op a) /\ 
          eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)
  with s
  and ()

val len_ab_0 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) = 0 /\ length (get_seq b) = 0 /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b) /\
                                  (forall id. mem_id id l ==> not (mem_id id a)) /\
                                  (forall id. mem_id id a ==> not (mem_id id b)) /\
                                  (forall id. mem_id id l ==> not (mem_id id b)))
                        (ensures (eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val l)) /\

                                 (exists (s:st). valid_st s /\ get_init s = get_val l /\ length (get_seq s) = 0 /\
                                    eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)))

#set-options "--z3rlimit 1000"
let len_ab_0 l a b = ()

val final : l:st -> a:st -> b:st
          -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\
                            get_init a = get_init b /\ get_init a = get_val l /\
                            pre_cond_merge (get_val l) (get_val a) (get_val b) /\
                            (forall id. mem_id id l ==> not (mem_id id a)) /\
                            (forall id. mem_id id a ==> not (mem_id id b)) /\
                            (forall id. mem_id id l ==> not (mem_id id b)))
                  (ensures (exists (s:st). valid_st s /\ get_init s = get_val l /\
                                      (forall o. mem_op o s <==> mem_op o a \/ mem_op o b) /\ 
                                      eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)))
                  (decreases %[length (get_seq a); length (get_seq b)])

#set-options "--initial_fuel 0 --max_fuel 10 --initial_ifuel 0 --max_ifuel 10 --z3rlimit 10000"
let rec final l a b =
    match length (get_seq a), length (get_seq b) with
    |0,0 -> len_ab_0 l a b
    
    |1,0 -> admit();introduce exists s. valid_st s /\ get_init s = get_val l /\ (forall o. mem_op o s <==> mem_op o a \/ mem_op o b) /\
           eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s) 
           with ((do (merge (get_val l) (inverse a) (get_val b)) (last_op a)), 
                     hide (cons ((merge (get_val l) (inverse a) (get_val b)), last_op a) empty))
           and ()

    |0,1 -> admit();introduce exists s. valid_st s /\ get_init s = get_val l /\ (forall o. mem_op o s <==> mem_op o a \/ mem_op o b) /\ 
           eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)
           with ((do (merge (get_val l) (get_val a) (inverse b)) (last_op b)), 
                     hide (cons ((merge (get_val l) (get_val a) (inverse b)), last_op b) empty))
           and ()

    |1,1 -> admit();len_ab_gt0 l a b;
           assert (exists (s:st). valid_st s /\ get_init s = (merge (get_val l) (inverse a) (inverse b)) /\
                     (forall o. mem_op o s <==> o = last_op a \/ o = last_op b) /\ 
                     eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)); 
           final l (inverse a, hide (slice (get_seq a) 0 (length (get_seq a) - 1)))
                   (inverse b, hide (slice (get_seq b) 0 (length (get_seq b) - 1)))

    |0,_ -> len_b_gt0 l a b; 
           assume (exists (s:st). valid_st s /\ get_init s = (merge (get_val l) (get_val a) (inverse b)) /\
                     (forall o. mem_op o s <==> o = last_op b) /\ 
                     eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)); 
           final l a (inverse b, hide (slice (get_seq b) 0 (length (get_seq b) - 1)))
    |_,0 -> admit(); len_a_gt0 l a b; final l (inverse a, hide (slice (get_seq a) 0 (length (get_seq a) - 1))) b
    |_,_ -> admit(); len_ab_gt0 l a b; final l (inverse a, hide (slice (get_seq a) 0 (length (get_seq a) - 1)))
                                     (inverse b, hide (slice (get_seq b) 0 (length (get_seq b) - 1)))

    
 
