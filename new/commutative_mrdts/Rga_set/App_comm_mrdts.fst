module App_comm_mrdts

module S = Set_extended_new

#set-options "--query_stats"
let unique_st (s:S.t (nat & (nat & nat))) =
  forall e. S.mem e s ==> ~ (exists e1. S.mem e1 s /\ snd e <> snd e1 /\ fst e = fst e1)

let mem_id_s (id:nat) (s:S.t (nat & (nat & nat))) 
  : (r:bool {s = S.empty ==> r == false}) =
  S.exists_s s (fun e -> fst e = id)

// the concrete state type
type concrete_st = s:(S.t (nat & (nat & nat)) & S.t nat) {unique_st (fst s) /\ (forall id. S.mem id (snd s) ==> mem_id_s id (fst s))}
                   // first ele of the pair is a tuple of timestamp, 
                   //     id after which the ele is to be inserted and ele to be inserted
                   // second ele of the pair is a tombstone set

// init state
let init_st : concrete_st = (S.empty, S.empty)

// equivalence between 2 concrete states
let eq (a b:concrete_st) =
  S.equal (fst a) (fst b) /\
  S.equal (snd a) (snd b)

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
  |Add_after : after_id:nat -> ele:nat -> app_op_t //inserts ele after after_id
  |Remove : id:pos -> app_op_t //removes the element with identifier id

let get_ele (op:op_t{Add_after? (snd (snd op))}) : nat =
  let (_, (_, Add_after _ ele)) = op in ele

let get_after_id (op:op_t{Add_after? (snd (snd op))}) : nat =
  let (_, (_, Add_after id _)) = op in id

let get_rem_id (op:op_t{Remove? (snd (snd op))}) : pos =
  let (_, (_, Remove id)) = op in id
  
//pre-condition for do
let do_pre (s:concrete_st) (o:op_t) : prop = 
  match o with
  |(ts, (_, Add_after after_id ele)) -> ~ (mem_id_s ts (fst s)) /\ (~ (after_id = 0) ==> mem_id_s after_id (fst s))
  |(_, (_, Remove id)) -> mem_id_s id (fst s)

// apply an operation to a state
let do (s:concrete_st) (o:op_t{do_pre s o}) : concrete_st =
  match o with
  |(ts, (_, Add_after after_id ele)) -> (S.insert (ts, (after_id, ele)) (fst s), snd s)
  |(_, (_, Remove id)) -> (fst s, S.insert id (snd s))
  
let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b /\ do_pre a op)
           (ensures eq (do a op) (do b op)) = ()
           
//pre-condition for merge
let merge_pre (l a b:concrete_st) : prop = 
  (forall id. mem_id_s id (fst l) ==> ~ (mem_id_s id (S.difference (fst a) (fst l)))) /\
  (forall id. mem_id_s id (fst l) ==> ~ (mem_id_s id (S.difference (fst b) (fst l)))) /\
  (forall id. mem_id_s id (S.difference (fst a) (fst l)) ==> ~ (mem_id_s id (S.difference (fst b) (fst l))))

// concrete merge operation
let merge (l a:concrete_st) (b:concrete_st{merge_pre l a b}) : concrete_st =
  (S.union (fst l) (S.union (fst a) (fst b)),   
   S.union (snd l) (S.union (snd a) (snd b)))

let merge_comm (l a b:st)
  : Lemma (requires cons_reps l a b /\ merge_pre (v_of l) (v_of a) (v_of b))
          (ensures merge_pre (v_of l) (v_of b) (v_of a) /\
                   (eq (merge (v_of l) (v_of a) (v_of b)) 
                       (merge (v_of l) (v_of b) (v_of a)))) = ()
         
let merge_idem (s:st)
  : Lemma (requires merge_pre (v_of s) (v_of s) (v_of s))
          (ensures eq (merge (v_of s) (v_of s) (v_of s)) (v_of s)) = ()

#push-options "--z3rlimit 50 --ifuel 3"
let rec fast_fwd (a b:st)
  : Lemma (requires cons_reps a a b /\ merge_pre (v_of a) (v_of a) (v_of b))
          (ensures S.subset (fst (v_of a)) (fst (v_of b)) /\
                   S.subset (snd (v_of a)) (snd (v_of b)) /\
                   eq (merge (v_of a) (v_of a) (v_of b)) (v_of b)) 
          (decreases length (ops_of b)) =
  if ops_of a = ops_of b then ()
  else 
    (let b' = inverse_st b in
     cons_reps_b' a a b;
     fast_fwd a b')


let lin_prop1 (s:concrete_st) (op1 op2:op_t)
  : Lemma (requires do_pre s op1 /\ do_pre s op2 /\ do_pre (do s op1) op2 /\ do_pre (do s op2) op1)
          (ensures eq (do (do s op1) op2) (do (do s op2) op1)) = ()

let lin_prop3 (l a b:concrete_st) (last2:op_t) 
  :  Lemma (requires do_pre b last2 /\ merge_pre l a b /\ merge_pre l a (do b last2) /\
                     do_pre (merge l a b) last2)
           (ensures eq (do (merge l a b) last2) (merge l a (do b last2))) = ()

let inter_merge1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    do_pre l o1 /\ do_pre l o3 /\ do_pre (do l o1) o2 /\ do_pre (do l o3) o1 /\ do_pre (do (do l o3) o1) o2 /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do l o3) o1))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2)) = ()

let inter_merge2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o2 <> fst o3 /\ fst o1 <> fst o3 /\
                    do_pre l o3 /\ do_pre l o2 /\ do_pre s' o2 /\ do_pre s o2 /\
                    merge_pre l s (do l o3) /\ merge_pre s (do s o2) s' /\
                    eq (merge l s (do l o3)) s' /\
                    eq (merge s (do s o2) s') (do s' o2) /\
                    do_pre s o1 /\ do_pre s' o1 /\ do_pre (do s o1) o2 /\ do_pre (do s' o1) o2 /\
                    merge_pre (do s o1) (do (do s o1) o2) (do s' o1))
          (ensures eq (merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2)) = ()

let inter_merge3 (l a b c:concrete_st) (op op':op_t) 
  : Lemma (requires merge_pre l a b /\ eq (merge l a b) c /\
                    (forall (o:op_t). do_pre b o /\ do_pre c o /\ merge_pre l a (do b o) ==> eq (merge l a (do b o)) (do c o)) /\
                    do_pre b op /\ do_pre c op /\ do_pre (do b op) op' /\ do_pre (do c op) op' /\
                    merge_pre l a (do (do b op) op'))
          (ensures eq (merge l a (do (do b op) op')) (do (do c op) op')) = ()

let inter_merge4 (l s:concrete_st) (o1 o2 o3 o4:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o4 /\ fst o2 <> fst o3 /\
                    do_pre l o1 /\ do_pre s o3 /\ do_pre (do l o1) o2 /\ do_pre (do s o3) o1 /\ do_pre (do (do s o3) o1) o2 /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do s o3) o1) /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2) /\
                    do_pre s o4 /\ do_pre (do s o4) o3 /\ do_pre (do (do s o4) o3) o1 /\ do_pre (do (do (do s o4) o3) o1) o2 /\
                    merge_pre (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1)) 
                      (do (do (do (do s o4) o3) o1) o2)) = ()

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
type concrete_st_s = admit()

// init state 
let init_st_s = admit()

// apply an operation to a state 
let do_s (s:concrete_st_s) (op:op_t) : concrete_st_s = admit()

//equivalence relation between the concrete states of sequential type and MRDT
let eq_sm (st_s:concrete_st_s) (st:concrete_st) = admit()

//initial states are equivalent
let initial_eq _
  : Lemma (ensures eq_sm init_st_s init_st) = ()

//equivalence between states of sequential type and MRDT at every operation
let do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st /\ do_pre st op)
          (ensures eq_sm (do_s st_s op) (do st op)) = admit()

////////////////////////////////////////////////////////////////
