module App

open SeqUtils
open Set_extended

#set-options "--query_stats"
// the concrete state type
// It is a set of pairs of timestamp and element.
type concrete_st = s:set (nat & nat)//{s <> empty ==> (exists (e:(nat * nat)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1))}

// init state
let init_st = empty

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  (forall e. mem e a <==> mem e b)

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

let mem_id_s (id:nat) (s:concrete_st) =
  exists_s s (fun e -> fst e = id)

let unique_st (s:concrete_st) =
  //forall_s s (fun e -> count e s > 0) &&
  forall_s s (fun e -> not (exists_s s (fun e1 -> snd e <> snd e1 && fst e = fst e1)))

val extract_s (m:option (nat * nat){Some? m}) : nat * nat
let extract_s (Some x) = x

let find_min (s:concrete_st)
    : (m:option (nat * nat) 
           {(Some? m <==> (exists (e:(nat * nat)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1))) /\
            (Some? m ==> (exists (e:(nat * nat)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1) /\ e = extract_s m)) /\
        (s = empty ==> (m = None \/ (~ (exists (e:(nat * nat)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1))))) 
        (*s <> empty ==> Some? m*)}) =
  find_if s (fun e -> (forall_s s (fun e1 -> fst e <= fst e1)))

let check_find_min (s:concrete_st)
  : Lemma (requires s = add (2,1) (singleton (3,1)))
          (ensures find_min s = Some (2,1)) 
  = let m = find_min s in
    assert (mem (2,1) s /\ (forall e1. mem e1 s ==> fst (2,1) <= fst e1));
    (*assert (Some? m);
    assert (fst (extract_s m) = 1);
    assert (forall e. mem e s ==> 1 <= fst e);*) ()

let remove_min (s:concrete_st) 
  : (r:concrete_st{(s = empty ==> r = s) /\
                   (s <> empty /\ Some? (find_min s) ==> (forall e. mem e r <==> (mem e s /\ e <> extract_s (find_min s)))) /\
                   (s <> empty /\ None? (find_min s) ==> (forall e. mem e r <==> mem e s))}) =
  if s = empty then s 
  else (let m = find_min s in
        if Some? m then remove_if s (fun e -> e = extract_s (find_min s))
        else s)

let find_min_equal (a b:concrete_st)
  : Lemma (requires unique_st a /\ unique_st b /\ eq a b)
          (ensures eq (remove_min a) (remove_min b)) = ()

// apply an operation to a state
let do (s:concrete_st) (op:op_t) : concrete_st =
  match op with
  |(id, (Enqueue x, _)) -> add (id, x) s
  |(_, (Dequeue, _)) -> if s = empty then s else remove_min s

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op)) = 
  assume (unique_st a /\ unique_st b); 
  match op with
  |(id, (Enqueue x, _)) -> ()
  |(_, (Dequeue, _)) -> ()
  
let return (s:concrete_st) (o:op_t) : ret_t =
  match o with
  |(_, (Enqueue _, _)) -> None
  |(_, (Dequeue, r)) -> if s = empty then None 
                          else (assume (exists (e:(nat * nat)). mem e s /\ (forall e1. mem e1 s ==> fst e <= fst e1));
                                assert (Some? (find_min s));
                                Some (extract_s (find_min s)))

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
 
