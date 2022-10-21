module Nn_ctr

open FStar.List.Tot
open FStar.Ghost
open FStar.Seq.Base
open FStar.Seq.Properties

type op =
  |Inc
  |Dec

type ctr_st = c:(nat & nat){fst c >= snd c} //concrete state of the counter
type st = ctr_st & (erased (Seq.seq (ctr_st & (nat (*id*) & op))))

val init : st
let init = ((0,0), hide empty)

val get_id : (nat * op) -> nat
let get_id (id, o) = id

let get_op (_, o) = o

val get_val : st -> ctr_st
let get_val (c, _) = c

val get_seq : st -> GTot (Seq.seq (ctr_st * (nat * op)))
let get_seq (st, seq) = (reveal seq)

val get_st : (ctr_st * (nat * op)) -> ctr_st
let get_st (st, o) = st

val get_init : c:st -> GTot ctr_st
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

val do : c:ctr_st -> o:(nat * op) -> c1:ctr_st{(Inc? (get_op o) <==> c1 = (fst c + 1, snd c)) /\
                                           (Dec? (get_op o) /\ fst c > snd c <==> c1 = (fst c, snd c + 1)) /\
                                           (Dec? (get_op o) /\ fst c = snd c <==> c1 = c) /\
                                           (((Dec? (get_op o) /\ fst c = snd c) \/ Inc? (get_op o)) <==> snd c = snd c1) /\
                                           (Dec? (get_op o) /\ fst c > snd c <==> snd c + 1 = snd c1)}
#set-options "--z3rlimit 1000"
let do c o =
 match o with
 |(_, Inc) -> (fst c + 1, snd c)
 |(_, Dec) -> if fst c > snd c then (fst c, snd c + 1) else c

let valid_st (c:st) = 
  (forall i. i < length (get_seq c) - 1 ==> do (st_i c i) (op_i c i) = (st_i c (i+1))) /\
  (length (get_seq c) > 0 ==> get_val c = do (inverse c) (last_op c))

val lemma1 : c:st
           -> Lemma (requires valid_st c /\ length (get_seq c) > 0)
                   (ensures fst (get_init c) <= fst (inverse c) /\
                            snd (get_init c) <= snd (inverse c))
                   (decreases (length (get_seq c)))
                   [SMTPat (valid_st c /\ length (get_seq c) > 0)]
let rec lemma1 c =
  match (length (get_seq c)) with
  |0 -> ()
  |1 -> ()
  |_ -> lemma1 (inverse c, hide (slice (get_seq c) 0 (length (get_seq c) - 1)))

val pre_cond_merge : l:ctr_st -> a:ctr_st -> b:ctr_st -> bool
let pre_cond_merge l a b = fst a >= fst l && fst b >= fst l && snd a >= snd l && snd b >= snd l

(* Given lca and a child version, we want to compute how many of the available
   values of the lca were decremented. Analogous to popping existing elements
   from the queue. *)
val num_dec_from_lca : l:ctr_st -> a:ctr_st{fst a >= fst l /\ snd a >= snd l} -> nat
let num_dec_from_lca (il, dl) (ia, da) =
  if il - dl < da - dl then
    (* the number of new decrement operations that were performed on the child
       is greater than the original number of available values in the lca. Then
       all the values in the lca must have been decremented. *)
    il - dl
  else
    (* Otherwise, the number of lca values decremented is exactly the number of
       new decrements *)
    da - dl

(* If both branches decremented from the value at the lca, then we compute
   overcount as the number of common values decremented, which is the minimum
   of the two decrements. Analogous to popping same elements from the queue. *)
val overcount : l:ctr_st 
              -> a:ctr_st
              -> b:ctr_st
              -> Pure nat (requires pre_cond_merge l a b)
                       (ensures (fun r -> true))
let overcount l a b =
  let na = num_dec_from_lca l a in
  let nb = num_dec_from_lca l b in
  min na nb

val merge : l:ctr_st -> a:ctr_st -> b:ctr_st 
          -> Pure ctr_st (requires pre_cond_merge l a b)
                        (ensures (fun r -> true))
let merge l a b =
  let o = overcount l a b in
  let i = fst a + fst b - fst l in
  let d = snd a + snd b - snd l in
  (i, d - o) (* account for the overcount *)

//equivalence relation between 2 states
val eq_m : a:ctr_st -> b:ctr_st -> bool
let eq_m a b = a = b

val prop_merge1 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                  get_op (last_op a) = Inc /\ get_op (last_op b) = Inc /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
                         (ensures pre_cond_merge (get_val l) (inverse a) (inverse b) /\
                                  (let m = merge (get_val l) (inverse a) (inverse b) in
                                       eq_m (merge (get_val l) (get_val a) (get_val b)) 
                                            (do (do m (last_op a)) (last_op b))))

#set-options "--z3rlimit 1000"
let prop_merge1 l a b = 
  lemma1 a;
  lemma1 b

(*even eq_m (merge (get_val l) (get_val a) (get_val b)) (merge (get_val l) (inverse a) (inverse b))
  will work out because the inverses are same as that of a and b and last_op a & last_op b are treated as no-op*)
val prop_merge2 : l:st -> a:st -> b:st
                 -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                   length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                   get_op (last_op a) = Dec /\ get_op (last_op b) = Dec /\
                                   get_val a = inverse a /\ get_val b = inverse b /\
                                   get_init a = get_init b /\ get_init a = get_val l /\ 
                                   pre_cond_merge (get_val l) (get_val a) (get_val b))
                          (ensures pre_cond_merge (get_val l) (inverse a) (inverse b) /\
                                   (let m = merge (get_val l) (inverse a) (inverse b) in
                                        eq_m (merge (get_val l) (get_val a) (get_val b))
                                             (do (do m (last_op a)) (last_op b))))
let prop_merge2 l a b = 
  lemma1 a;
  lemma1 b

(*since a = inverse a, last_op a is treated as no-op *)
val prop_merge3 : l:st -> a:st -> b:st
                  -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                    length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                    get_op (last_op a) = Dec /\ get_op (last_op b) = Dec /\
                                    get_val a = inverse a /\ get_val b <> inverse b /\
                                    get_init a = get_init b /\ get_init a = get_val l /\ 
                                    pre_cond_merge (get_val l) (get_val a) (get_val b))
                           (ensures (pre_cond_merge (get_val l) (inverse a) (get_val b) /\
                                    (let m = merge (get_val l) (inverse a) (get_val b) in
                                         eq_m (merge (get_val l) (get_val a) (get_val b)) m)))
let prop_merge3 l a b =
  lemma1 a;
  lemma1 b

(*since b = inverse b, last_op b is treated as no-op *)
val prop_merge4 : l:st -> a:st -> b:st
                  -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                    length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                    get_op (last_op a) = Dec /\ get_op (last_op b) = Dec /\
                                    get_val a <> inverse a /\ get_val b = inverse b /\
                                    get_init a = get_init b /\ get_init a = get_val l /\ 
                                    pre_cond_merge (get_val l) (get_val a) (get_val b))
                           (ensures (pre_cond_merge (get_val l) (get_val a) (inverse b) /\
                                    (let m = merge (get_val l) (get_val a) (inverse b) in
                                         eq_m (merge (get_val l) (get_val a) (get_val b)) m)))
let prop_merge4 l a b =
  lemma1 a;
  lemma1 b

(* all the available values in lca are not decremented by both the branches. So only decrement should take effect.*)
val prop_merge5 : l:st -> a:st -> b:st
                  -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                    length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                    get_op (last_op a) = Dec /\ get_op (last_op b) = Dec /\
                                    get_val a <> inverse a /\ get_val b <> inverse b /\
                                    (fst (get_val l) - snd (get_val l) >= snd (get_val a) - snd (get_val l) \/
                                    fst (get_val l) - snd (get_val l) >= snd (get_val b) - snd (get_val l)) /\
                                    get_init a = get_init b /\ get_init a = get_val l /\ 
                                    pre_cond_merge (get_val l) (get_val a) (get_val b))
                           (ensures (pre_cond_merge (get_val l) (inverse a) (inverse b) /\
                                    (let m = merge (get_val l) (inverse a) (inverse b) in
                                         eq_m (merge (get_val l) (get_val a) (get_val b))
                                              (do m (last_op a)))))

#set-options "--z3rlimit 100000"
let prop_merge5 l a b =
  lemma1 a;
  lemma1 b;
  assert (fst (get_val a) >= fst (get_val l) /\ fst (get_val b) >= fst (get_val l)); 
  assert (snd (get_val a) >= snd (get_val l) /\ snd (get_val b) >= snd (get_val l)); 
  assert (fst (get_init b) <= fst (inverse b) /\ snd (get_init b) <= snd (inverse b)); 
  assert (fst (get_init a) <= fst (inverse a) /\ snd (get_init a) <= snd (inverse a)); 
  assert (fst (get_val l) <= fst (inverse a) /\ snd (get_val l) <= snd (inverse a)); 
  assert (fst (get_val l) <= fst (inverse b) /\ snd (get_val l) <= snd (inverse b));
  assert (snd (get_val a) <> snd (inverse a) /\ snd (get_val b) <> snd (inverse b)); 
  assert (fst (get_val a) = fst (inverse a) /\ fst (get_val b) = fst (inverse b)); 
  () (*done*)

(* all the available values in lca are decremented by both the branches. The two decrements are decrementing the newly added values in both the branches. So both decrements should take effect.*)
val prop_merge6 : l:st -> a:st -> b:st
                  -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                    length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                    get_op (last_op a) = Dec /\ get_op (last_op b) = Dec /\
                                    get_val a <> inverse a /\ get_val b <> inverse b /\
                                    get_init a = get_init b /\ get_init a = get_val l /\
                                    fst (get_val l) - snd (get_val l) < snd (get_val a) - snd (get_val l) /\
                                    fst (get_val l) - snd (get_val l) < snd (get_val b) - snd (get_val l) /\
                                    pre_cond_merge (get_val l) (get_val a) (get_val b))
                           (ensures (pre_cond_merge (get_val l) (inverse a) (inverse b) /\
                                    (let m = merge (get_val l) (inverse a) (inverse b) in
                                         eq_m (merge (get_val l) (get_val a) (get_val b))
                                              (do (do m (last_op a)) (last_op b)))))

#set-options "--z3rlimit 100000"
let prop_merge6 l a b = 
  lemma1 a;
  lemma1 b;
  assert (snd (get_val a) <> snd (inverse a) /\ snd (get_val b) <> snd (inverse b)); 
  assert (fst (get_val a) = fst (inverse a) /\ fst (get_val b) = fst (inverse b)); 
  ()

val prop_merge7 : l:st -> a:st -> b:st
                 -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                   length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                   get_op (last_op a) = Dec /\ get_op (last_op b) = Inc /\
                                   get_init a = get_init b /\ get_init a = get_val l /\ 
                                   pre_cond_merge (get_val l) (get_val a) (get_val b))
                         (ensures (pre_cond_merge (get_val l) (get_val a) (inverse b) /\
                                       (let m = merge (get_val l) (get_val a) (inverse b) in
                                           eq_m (merge (get_val l) (get_val a) (get_val b)) (do m (last_op b)))))

#set-options "--z3rlimit 1000"
let prop_merge7 l a b =
  lemma1 a;
  lemma1 b (*done*)

val prop_merge8 : l:st -> a:st -> b:st
                 -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                   length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                   get_op (last_op a) = Inc /\ get_op (last_op b) = Dec /\
                                   get_init a = get_init b /\ get_init a = get_val l /\ 
                                   pre_cond_merge (get_val l) (get_val a) (get_val b))
                         (ensures (pre_cond_merge (get_val l) (inverse a) (get_val b) /\
                                       (let m = merge (get_val l) (inverse a) (get_val b) in
                                           eq_m (merge (get_val l) (get_val a) (get_val b)) (do m (last_op a)))))

#set-options "--z3rlimit 1000"
let prop_merge8 l a b =
  lemma1 a;
  lemma1 b (*done*)

val prop_merge9 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) = 0 /\ length (get_seq b) > 0 /\
                                  get_val a = get_init b /\ get_val a = get_val l /\
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
                        (ensures pre_cond_merge (get_val l) (get_val a) (inverse b) /\
                                 (let m = merge (get_val l) (get_val a) (inverse b) in
                                      eq_m (merge (get_val l) (get_val a) (get_val b)) (do m (last_op b))))
let prop_merge9 l a b = 
  lemma1 b

val prop_merge10 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) > 0 /\ length (get_seq b) = 0 /\
                                  get_val b = get_init a /\ get_val b = get_val l /\
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
                        (ensures pre_cond_merge (get_val l) (inverse a) (get_val b) /\
                                 (let m = merge (get_val l) (inverse a) (get_val b) in
                                      eq_m (merge (get_val l) (get_val a) (get_val b)) (do m (last_op a))))
let prop_merge10 l a b = 
  lemma1 a

val prop_merge11 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) = 0 /\ length (get_seq b) = 0 /\
                                  get_val b = get_init a /\ get_val b = get_val l /\
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
                        (ensures pre_cond_merge (get_val l) (get_val a) (get_val b) /\
                                 (let m = merge (get_val l) (get_val a) (get_val b) in
                                 eq_m (merge (get_val l) (get_val a) (get_val b)) (get_val l)))
let prop_merge11 l a b = ()
    
val spec : ctr_st -> (nat * op) -> (nat * op) -> ctr_st
let spec a o1 o2 =
  match o1, o2 with
  |(_, Dec), (_, Dec) -> do a o1
  |(_, Inc), (_, Dec) -> do (do a o2) o1
  |_ -> do (do a o1) o2

val lem_spec : l:st -> a:st -> b:st
             -> o1:(nat * op) -> o2:(nat * op)
             -> Lemma (requires pre_cond_do (get_val l) o1 /\ pre_cond_do (get_val l) o2 /\ get_id o1 <> get_id o2 /\
                               get_val a = do (get_val l) o1 /\ get_val b = do (get_val l) o2)
                     (ensures pre_cond_merge (get_val l) (get_val a) (get_val b) /\ 
                              eq_m (spec (get_val l) o1 o2) (merge (get_val l) (get_val a) (get_val b)))
let lem_spec l a b o1 o2 = ()

