module Ictr

open FStar.List.Tot
open FStar.Ghost
open FStar.Seq.Base
open FStar.Seq.Properties

type op =
  | Inc

type ctr_st = nat //concrete state of the counter
type st = ctr_st & (erased (Seq.seq (ctr_st & (nat (*id*) & op))))

val init : st
let init = (0, hide empty)

val get_id : (nat * op) -> nat
let get_id (id, o) = id

val get_op : (ctr_st * (nat * op)) -> (nat * op)
let get_op (_, o) = o

val get_val : st -> ctr_st
let get_val (c, _) = c

val get_seq : st -> GTot (Seq.seq (ctr_st * (nat * op)))
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

let valid_st (c:st) = 
  (forall (i:nat). i < length (get_seq c) - 1 ==> do (st_i c i) (op_i c i) = (st_i c (i+1))) /\
  (length (get_seq c) > 0 ==> get_val c = do (inverse c) (last_op c))

val init_le_inv : c:st
           -> Lemma (requires valid_st c /\ length (get_seq c) > 0)
                   (ensures get_init c <= inverse c /\ get_val c = get_init c + length (get_seq c))
                   (decreases (length (get_seq c)))
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

  val mem_op_l : o:(nat * op) -> s:(list (ctr_st & (nat (*id*) & op))) 
               -> Tot (b:bool{(exists e. List.Tot.mem e s /\ get_op e = o)  <==> (b = true)})
  let rec mem_op_l o s =
      match s with
      |[] -> false
      |x::xs -> get_op x = o || mem_op_l o xs

  let mem_op (o:(nat * op)) (s:st) =
      mem_op_l o (seq_to_list (get_seq s))


//equivalence relation between 2 states
val eq_m : a:ctr_st -> b:ctr_st -> bool
let eq_m a b = a = b

val spec : ctr_st -> (nat * op) -> (nat * op) -> nat
let spec a o1 o2 =
    do (do a o1) o2

val lem_spec : l:st -> a:st -> b:st
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
  ()

val len_ab_gt0 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\
                                  length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
                         (ensures pre_cond_merge (get_val l) (inverse a) (inverse b) /\
                                  (let m = merge (get_val l) (inverse a) (inverse b) in
                                       eq_m (merge (get_val l) (get_val a) (get_val b))
                                            (*merge m (do m (last_op a)) (do m (last_op b))*)
                                            (do (do m (last_op a)) (last_op b)) /\

                                  (exists (s:st). valid_st s /\ get_init s = m /\
                                     (forall o. mem_op o s <==> o = last_op a \/ o = last_op b) /\ 
                                     eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s))))

#set-options "--z3rlimit 1000"
let len_ab_gt0 l a b =
  init_le_inv a;
  init_le_inv b;
  let m = merge (get_val l) (inverse a) (inverse b) in
  let s = ((do (do m (last_op a)) (last_op b)), hide (cons (m, last_op a) (create 1 (do m (last_op a), last_op b)))) in
  assert (valid_st s /\ get_init s = m /\ (forall o. mem_op o s <==> o = last_op a \/ o = last_op b) /\ 
          eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s));
  ()

val len_b_gt0 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) = 0 /\ length (get_seq b) > 0 /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
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
  assert (valid_st s /\ get_init s = m /\ (forall o. mem_op o s <==> o = last_op b) /\ 
          eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s));
  ()

val len_a_gt0 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) > 0 /\ length (get_seq b) = 0 /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
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
  assert (valid_st s /\ get_init s = m /\ (forall o. mem_op o s <==> o = last_op a) /\ 
          eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s));
  ()

val len_ab_0 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) = 0 /\ length (get_seq b) = 0 /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
                        (ensures (eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val l)) /\

                                 (exists (s:st). valid_st s /\ get_init s = get_val l /\ length (get_seq s) = 0 /\
                                    eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)))

#set-options "--z3rlimit 1000"
let len_ab_0 l a b = ()

val final : l:st -> a:st -> b:st
          -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\
                            get_init a = get_init b /\ get_init a = get_val l /\
                            pre_cond_merge (get_val l) (get_val a) (get_val b))
                  (ensures (exists (s:st). valid_st s /\ get_init s = get_val l /\
                                      (forall o. mem_op o s <==> mem_op o a \/ mem_op o b) /\ 
                                      eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val s)))
                  (decreases %[length (get_seq a); length (get_seq b)])

#set-options "--initial_fuel 0 --max_fuel 5 --initial_ifuel 0 --max_ifuel 5 --z3rlimit 10000"
let rec final l a b =
    match length (get_seq a), length (get_seq b) with
    |0,0 -> len_ab_0 l a b
    |1,0 -> len_a_gt0 l a b
    |0,1 -> len_b_gt0 l a b
    |1,1 -> len_ab_gt0 l a b
    |0,_ -> len_b_gt0 l a b; final l a (inverse b, hide (slice (get_seq b) 0 (length (get_seq b) - 1)))
    |_,0 -> len_a_gt0 l a b; final l (inverse a, hide (slice (get_seq a) 0 (length (get_seq a) - 1))) b
    |_,_ -> len_ab_gt0 l a b; final l (inverse a, hide (slice (get_seq a) 0 (length (get_seq a) - 1)))
                                     (inverse b, hide (slice (get_seq b) 0 (length (get_seq b) - 1)))

