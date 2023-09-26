module Ewflag_rid

module L = FStar.List.Tot

#set-options "--query_stats"

let cf = (int * bool)

let rec mem_rid (rid:nat) (s:list (nat * cf)) : bool =
  match s with
  |[] -> false
  |x::xs -> fst x = rid || mem_rid rid xs

let rec unique (l:list (nat * cf)) =
  match l with
  |[] -> true
  |x::xs -> not (mem_rid (fst x) xs) && unique xs 

// the concrete state type
type concrete_st = l:list (nat & cf){unique l} // (replica_id, ctr, flag) //replica ids are unique
 
let init_st = []
 
let rec get_cf (rid:nat) (s:concrete_st) 
  : Tot (r:cf{(not (mem_rid rid s) ==> r = (0,false))}) =
  match s with
  |[] -> (0, false)
  |(rid1,cf)::xs -> if rid = rid1 then cf else get_cf rid xs

let rec rem_rid (rid:nat) (s:concrete_st)
  : Tot (r:concrete_st{(forall id. mem_rid id r <==> mem_rid id s /\ id <> rid) /\ 
                       (forall id. mem_rid id r ==> (get_cf id s = get_cf id r))}) 
    (decreases s) =
  match s with
  |[] -> []
  |x::xs -> if rid = fst x then (assert (forall e. L.mem e s /\ fst e <> rid ==> L.mem e xs);  xs) else x::rem_rid rid xs

let eq_id (a b:concrete_st) =
  (forall id. mem_rid id a <==> mem_rid id b)

let eq (a b:concrete_st) =
  eq_id a b /\
  (forall rid. mem_rid rid a ==> (get_cf rid a = get_cf rid b))

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
type app_op_t:eqtype =
  |Enable 
  |Disable

type timestamp_t = pos 

type op_t = timestamp_t & (nat (*replica_id*) & app_op_t)

let get_rid (_,(rid,_)) = rid

let rec update (rid:nat) (s:concrete_st{mem_rid rid s}) (cf1:cf)
  : Tot (r:concrete_st{(forall id. mem_rid id s <==> mem_rid id r) /\ L.mem (rid, cf1) r /\
                        get_cf rid r = cf1 /\
                       (forall id. mem_rid id s /\ id <> rid ==> (get_cf id s = get_cf id r)) /\
                       (forall e. L.mem e r /\ fst e <> rid <==> L.mem e s /\ fst e <> rid)}) =
  match s with
  |[x] -> [(fst x, cf1)]
  |x::xs -> if fst x = rid then (rid, cf1)::xs else x::update rid xs cf1

let rec set_all_false (s:concrete_st) 
  : (r:concrete_st{(forall id. mem_rid id r <==> mem_rid id s) /\
                   (forall id. get_cf id r = (fst (get_cf id s), false))}) =
  match s with
  |[] -> []
  |(rid,(c,_))::xs -> (rid,(c,false))::set_all_false xs

// apply an operation to a state
let do (s:concrete_st) (o:op_t) 
  : (r:concrete_st{(Enable? (snd (snd o)) ==> (forall id. mem_rid id r <==> mem_rid id s \/ id = get_rid o) /\
                                       (not (mem_rid (get_rid o) s) ==> L.mem ((get_rid o), (1, true)) r /\
                                (forall id cf. L.mem (id, cf) s \/ (id, cf) = (get_rid o, (1, true)) <==> L.mem (id, cf) r)) /\
          (mem_rid (get_rid o) s ==> (L.mem (get_rid o, (fst (get_cf (get_rid o) s) + 1, true)) r) /\
                            fst (get_cf (get_rid o) r) = fst (get_cf (get_rid o) s) + 1) /\
             (forall id. id <> get_rid o ==> (get_cf id s = get_cf id r))) /\
                   (Disable? (snd (snd o)) ==> (forall id. mem_rid id r <==> mem_rid id s) /\
                     (forall id. get_cf id r = (fst (get_cf id s), false)))}) =
  match o with
  |(_, (rid, Enable)) -> if mem_rid rid s then update rid s (fst (get_cf rid s) + 1, true) else (rid, (1, true))::s
  |(_, (rid, Disable)) -> set_all_false s

let merge_flag (l a b:cf) =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac > lc
          else bc > lc

// concrete merge operation
let merge_cf (lca s1 s2:cf) : cf =
  (fst s1 + fst s2 - fst lca, merge_flag lca s1 s2)

#push-options "--z3rlimit 500 --fuel 1 --ifuel 1"
let rec concrete_merge (lca s1 s2:concrete_st) 
  : Pure concrete_st
    (requires true)
    (ensures (fun r -> (forall rid. mem_rid rid r <==> (mem_rid rid lca \/ mem_rid rid s1 \/ mem_rid rid s2)) /\ 
                    (forall id. (get_cf id r = merge_cf (get_cf id lca) (get_cf id s1) (get_cf id s2)))))    
    (decreases %[lca;s1;s2]) =
  match lca, s1, s2 with
  |[],[],[] -> []
  |(rid,cf)::xs,_,_ -> (rid, merge_cf cf (get_cf rid s1) (get_cf rid s2))::concrete_merge xs (rem_rid rid s1) (rem_rid rid s2)
  |[],(rid,cf)::ys,_ -> (rid, merge_cf (get_cf rid lca) cf (get_cf rid s2))::concrete_merge [] (rem_rid rid s1) (rem_rid rid s2)
  |[],[],(rid,cf)::zs -> (rid, merge_cf (get_cf rid lca) (get_cf rid s1) cf)::concrete_merge [] [] zs
#pop-options


#push-options "--z3rlimit 200"
let prop1 (l:concrete_st) (o1 o2 o3:op_t) //done
  : Lemma (requires fst o1 <> fst o3 /\ 
                    ((Enable? (snd (snd o1)) /\ Enable? (snd (snd o3)) /\ Enable? (snd (snd o2))) \/
                     (Enable? (snd (snd o1)) /\ Disable? (snd (snd o3))) \/
                     (Disable? (snd (snd o3)))) /\
                    get_rid o1 = get_rid o2 /\ get_rid o3 <> get_rid o1)
                    //resolve_conflict o1 o3 = First_then_second) //o3.o1
                    //not (resolve_conflict o2 o3 = Second_then_first) //not(o2.o3)
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = 
  (*let r2 = get_rid o2 in
  let lhs = (concrete_merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) in
  let rhs = (do (do (do l o3) o1) o2) in
  assert (forall id. fst (get_cf id lhs) = fst (get_cf id rhs));
  assert (forall id. id <> r2 ==> snd (get_cf id lhs) = snd (get_cf id rhs));
  assert (fst (get_cf r2 lhs) = fst (get_cf r2 rhs)); 
  assert (snd (get_cf r2 lhs) = snd (get_cf r2 rhs));
  assert (get_cf r2 lhs = get_cf r2 rhs);
  assert (forall id. snd (get_cf id lhs) = snd (get_cf id rhs));*)
  ()

let prop2 (l s s':concrete_st) (o1 o2 o3:op_t) //done
  : Lemma (requires eq (concrete_merge s (do s o2) s') (do s' o2) /\
                    eq (concrete_merge l s (do l o3)) s' /\
                    get_rid o1 = get_rid o2 /\ get_rid o1 <> get_rid o3)
          (ensures eq (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = 
  let lhs = (concrete_merge (do s o1) (do (do s o1) o2) (do s' o1)) in
  let rhs = (do (do s' o1) o2) in
  let r2 = get_rid o2 in 
  assume (forall id. fst (get_cf id lhs) = fst (get_cf id rhs)); //done
  assume (forall id. id <> r2 ==> snd (get_cf id lhs) = snd (get_cf id rhs)); //done 
  assume (fst (get_cf r2 lhs) = fst (get_cf r2 rhs)); //done
  assume (snd (get_cf r2 lhs) = snd (get_cf r2 rhs)); //done
  assert (get_cf r2 lhs = get_cf r2 rhs);
  assert (forall id. snd (get_cf id lhs) = snd (get_cf id rhs));
  ()

let prop3 (s s':concrete_st) (o2 o2':op_t) //done
  : Lemma (requires eq (concrete_merge s s s') s' /\
                    (forall o. eq (concrete_merge s (do s o) s') (do s' o)) /\
                    fst o2 <> fst o2' /\ get_rid o2 = get_rid o2')
          (ensures eq (concrete_merge s (do (do s o2') o2) s') (do (do s' o2') o2)) = 
  (*let r2 = get_rid o2 in
  let lhs = (concrete_merge s (do (do s o2') o2) s') in
  let rhs = (do (do s' o2') o2) in
  assert (forall id. fst (get_cf id lhs) = fst (get_cf id rhs)); 
  assert (forall id. id <> r2 ==> snd (get_cf id lhs) = snd (get_cf id rhs));
  assert (fst (get_cf r2 lhs) = fst (get_cf r2 rhs)); 
  assert (snd (get_cf r2 lhs) = snd (get_cf r2 rhs));
  assert (get_cf r2 lhs = get_cf r2 rhs);
  assert (forall id. snd (get_cf id lhs) = snd (get_cf id rhs));*)
  ()

let lem_merge3 (l a b c:concrete_st) (op op':op_t) //done
  : Lemma 
    (requires eq (concrete_merge l a b) c /\ 
              fst op <> fst op' /\ get_rid op = get_rid op' /\
              (forall (o:op_t). eq (concrete_merge l a (do b o)) (do c o)))
    (ensures eq (concrete_merge l a (do (do b op) op')) (do (do c op) op')) = 
  let r2 = get_rid op' in
  let lhs = (concrete_merge l a (do (do b op) op')) in
  let rhs = (do (do c op) op') in
  assert (forall id. fst (get_cf id lhs) = fst (get_cf id rhs)); 
  assert (forall id. id <> r2 ==> snd (get_cf id lhs) = snd (get_cf id rhs));
  assert (fst (get_cf r2 lhs) = fst (get_cf r2 rhs)); 
  assert (snd (get_cf r2 lhs) = snd (get_cf r2 rhs));
  assert (get_cf r2 lhs = get_cf r2 rhs);
  assert (forall id. snd (get_cf id lhs) = snd (get_cf id rhs));
  ()

#push-options "--z3rlimit 300"
let prop4 (l s:concrete_st) (o1 o2 o3 o3':op_t) //check
  : Lemma (requires fst o2 <> fst o3 /\ 
                    ((Enable? (snd (snd o1)) /\ Enable? (snd (snd o3))) \/
                     (Disable? (snd (snd o3)))) /\
                    ((Enable? (snd (snd o2)) /\ Enable? (snd (snd o3))) \/
                     (Disable? (snd (snd o3)))) /\
                    ((Enable? (snd (snd o1)) /\ Enable? (snd (snd o3'))) \/
                     (Disable? (snd (snd o3')))) /\
                    ((Enable? (snd (snd o2)) /\ Enable? (snd (snd o3'))) \/
                     (Disable? (snd (snd o3')))) /\
                    get_rid o1 = get_rid o2 /\ get_rid o3 = get_rid o3' /\
                    //o3.o1, o3'.o1, o3.o2, o3'.o2
                    eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) 
                      (do (do (do (do s o3') o3) o1) o2)) = 
  let r2 = get_rid o2 in
  let lhs = (concrete_merge (do l o1) (do (do l o1) o2) (do (do (do s o3') o3) o1)) in
  let rhs = (do (do (do (do s o3') o3) o1) o2) in
  assume (forall id. fst (get_cf id lhs) = fst (get_cf id rhs)); 
  assume (forall id. id <> r2 ==> snd (get_cf id lhs) = snd (get_cf id rhs));
  assume (fst (get_cf r2 lhs) = fst (get_cf r2 rhs)); 
  assume (snd (get_cf r2 lhs) = snd (get_cf r2 rhs));
  assert (get_cf r2 lhs = get_cf r2 rhs);
  assert (forall id. snd (get_cf id lhs) = snd (get_cf id rhs));
  ()

let lem_merge4 (s s':concrete_st) (op op':op_t) //done
  : Lemma (requires get_rid op = get_rid op' /\
                    eq (concrete_merge (do s op) (do s' op) (do s op)) (do s' op))
          (ensures eq (concrete_merge (do s op) (do (do s' op') op) (do s op)) (do (do s' op') op)) = ()
          
let idempotence (s:concrete_st)
  : Lemma (eq (concrete_merge s s s) s) = ()

let prop5' (l s s':concrete_st) (o o3:op_t)
  : Lemma (requires eq (concrete_merge s s s') s' /\
                    get_rid o <> get_rid o3 /\ eq (concrete_merge l s (do l o3)) s')
          (ensures eq (concrete_merge s s (do s' o)) (do s' o)) = 
  (*let r = get_rid o in
  let lhs = (concrete_merge s s (do s' o)) in
  let rhs = (do s' o) in
  assert (forall id. fst (get_cf id lhs) = fst (get_cf id rhs)); 
  assert (forall id. id <> r ==> snd (get_cf id lhs) = snd (get_cf id rhs));
  assert (fst (get_cf r lhs) = fst (get_cf r rhs));
  assert (snd (get_cf r lhs) = snd (get_cf r rhs));
  assert (get_cf r lhs = get_cf r rhs);
  assert (forall id. snd (get_cf id lhs) = snd (get_cf id rhs));*)
  ()

let prop5 (s s':concrete_st)
  : Lemma (ensures (//eq_id (concrete_merge s s s') s' /\ 
                    eq (concrete_merge s s' s) s')) = 
  admit()
