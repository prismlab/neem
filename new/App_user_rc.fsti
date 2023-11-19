module App_user_rc

open FStar.Seq
open FStar.Ghost
open SeqUtils

#set-options "--query_stats"

// the concrete state type
val concrete_st : Type0

// init state
val init_st : concrete_st

// equivalence between 2 concrete states
val eq (a b:concrete_st) : Type0

val symmetric (a b:concrete_st) 
  : Lemma (requires eq a b)
          (ensures eq b a)

val transitive (a b c:concrete_st)
  : Lemma (requires eq a b /\ eq b c)
          (ensures eq a c)

val eq_is_equiv (a b:concrete_st)
  : Lemma (requires a == b)
          (ensures eq a b)

// operation type
val app_op_t : eqtype

type timestamp_t = pos 

type op_t = timestamp_t & (nat (*replica ID*) & app_op_t)

type log = seq op_t

let get_rid (_,(rid,_)) = rid

let mem_rid (rid:nat) (l:log) =
  exists e. mem e l /\ fst (snd e) = rid
  
unfold
let ( ++ ) (l1 l2:log) = Seq.append l1 l2

unfold
let mem_id (id:timestamp_t) (l:log) : bool =
  mem_assoc_fst id l
  
unfold
let distinct_ops (l:log) = distinct_assoc_fst l

type st0 = concrete_st & erased log
  
let v_of (s:st0) : concrete_st = fst s
let ops_of (s:st0) : GTot log = snd s

// apply an operation to a state
val do (s:concrete_st) (o:op_t) : concrete_st

val lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b)
           (ensures eq (do a op) (do b op))

// applying a log of operations to a concrete state
let rec apply_log (x:concrete_st) (l:log) : Tot concrete_st (decreases length l) =
  match length l with
  |0 -> x
  |_ -> apply_log (do x (head l)) (tail l)                   

// property of apply_log
let rec lem_apply_log (x:concrete_st) (l:log)
  : Lemma (requires true)
          (ensures (length l > 0 ==> (apply_log x l == apply_log (do x (head l)) (tail l)) /\
                                    (apply_log x l == do (apply_log x (fst (un_snoc l))) (last l))) /\
                   (length l = 0 ==> apply_log x l == x))
          (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_apply_log (do x (head l)) (tail l)

type st1 = s:st0{(v_of s == apply_log init_st (ops_of s))}

// valid state
let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  (v_of s == apply_log init_st (ops_of s))

type st = s:st0{valid_st s}

//operations x and y are commutative
val comm_ops (x y:op_t) : bool

// if x and y are commutative ops, applying them in any order should give equivalent results
val commutative_prop (x y:op_t) 
  : Lemma (requires comm_ops x y)
          (ensures (forall s. eq (apply_log s (cons x (cons y empty))) (apply_log s (cons y (cons x empty)))))

//commutativity for a sequence of operation
let commutative_seq (x:op_t) (l:log) : bool =
  forallb (fun e -> comm_ops x e) l

type rc_res =
  | Fst_snd //op1 -> op2
  | Snd_fst //op2 -> op1

//conflict resolution
val rc (x:op_t) (y:op_t{fst x <> fst y /\ ~ (comm_ops x y)}) : rc_res

// concrete merge operation
val merge (l a b:concrete_st) : concrete_st

(*let comm_empty_log (x:op_t) (l:log)
  : Lemma (ensures length l = 0 ==> commutative_seq x l) = ()*)

// returns true if there exists an operation op in log l such that
// 1. last_op and op are non-commutative
// 2. op is commutative with all the operations in the suffix of l
// 3. op should be applied after last_op according to resolve_conflict
let reorder (last_op:op_t) (l:log)
  : (b:bool{b = true <==> (exists op. mem op l /\ fst last_op <> fst op /\
                         (let pre,suf = pre_suf l op in
                          ~ (comm_ops last_op op) /\
                          Fst_snd? (rc last_op op) /\
                          commutative_seq op suf))}) =
  existsb (fun (op:op_t) -> mem op l &&  fst last_op <> fst op &&
                              (let pre,suf = pre_suf l op in
                              not (comm_ops last_op op) &&
                              Fst_snd? (rc last_op op) &&
                              commutative_seq op suf)) l

let rec split_prefix (s:concrete_st) (l:log) (a:log)
  : Lemma (requires is_prefix l a)
          (ensures (apply_log s a == apply_log (apply_log s l) (diff a l)) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) == (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |1 -> ()
    |_ -> split_prefix (do s (head l)) (tail l) (tail a)

// returns the inverse state by undoing the last operation
#push-options "--z3rlimit 50"
let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{//(v_of s == do (v_of i) (last (ops_of s))) /\
               //(ops_of i == fst (un_snoc (ops_of s))) /\
               //(ops_of s == snoc (ops_of i) (last (ops_of s))) /\
               //length (ops_of i) = length (ops_of s) - 1 /\
               //is_prefix (ops_of i) (ops_of s) /\
               (let _, last2 = un_snoc (ops_of s) in
               //(lem_last (ops_of s);
               s == (do (v_of i) last2, hide (snoc (ops_of i) last2))) /\
               (forall id. mem_id id (ops_of i) <==> mem_id id (ops_of s) /\ id <> fst (last (ops_of s)))}) = 
  lem_apply_log init_st (ops_of s);
  let p, l = un_snoc (ops_of s) in
  let r = apply_log init_st p in
  lemma_split (ops_of s) (length (ops_of s) - 1); 
  lemma_append_count_assoc_fst p (snd (split (ops_of s) (length (ops_of s) - 1))); 
  distinct_invert_append p (snd (split (ops_of s) (length (ops_of s) - 1))); 
  (r, hide p)

(*let rec inverse_helper (s:concrete_st) (l':log) (op:op_t)
  : Lemma 
    (ensures (let l = Seq.snoc l' op in 
              (apply_log s l == do (apply_log s l') op)))
    (decreases length l')
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |_ ->  inverse_helper (do s (head l')) (tail l') op*)

let cons_reps (l a b:st1) =
  distinct_ops (ops_of l) /\ distinct_ops (ops_of a) /\ distinct_ops (ops_of b) /\
  is_prefix (ops_of l) (ops_of a) /\
  is_prefix (ops_of l) (ops_of b) /\
  (forall id. mem_id id (diff (ops_of a) (ops_of l)) ==> not (mem_id id (diff (ops_of b) (ops_of l)))) /\
  (forall rid. mem_rid rid (diff (ops_of a) (ops_of l)) ==> ~ (mem_rid rid (diff (ops_of b) (ops_of l))))

let cons_reps_s1_gt0 (l a b:st1) =
  cons_reps l a b /\
  length (ops_of a) > length (ops_of l)

let cons_reps_s2_gt0 (l a b:st1) =
  cons_reps l a b /\
  length (ops_of b) > length (ops_of l)

let cons_reps_s1s2_gt0 (l a b:st1) =
  cons_reps l a b /\
  length (ops_of a) > length (ops_of l) /\
  length (ops_of b) > length (ops_of l)

let do_st (s:st1) (o:op_t) : st1 =
  split_prefix init_st (ops_of s) (snoc (ops_of s) o); 
  (do (v_of s) o, hide (snoc (ops_of s) o))

let cons_reps_s1's2' (l a b:st)
  : Lemma (requires cons_reps_s1s2_gt0 l a b)
          (ensures cons_reps l (inverse_st a) (inverse_st b)) =
  lem_inverse (ops_of l) (ops_of a);
  lem_inverse (ops_of l) (ops_of b);
  inverse_diff_id_s1'_s2' (ops_of l) (ops_of a) (ops_of b);
  assume (forall rid. mem_rid rid (diff (ops_of (inverse_st a)) (ops_of l)) ==> 
                 ~ (mem_rid rid (diff (ops_of (inverse_st b)) (ops_of l)))); ()

let cons_reps_s2' (l a b:st)
  : Lemma (requires cons_reps_s2_gt0 l a b)
          (ensures cons_reps l a (inverse_st b)) =
  lem_inverse (ops_of l) (ops_of b);
  split_prefix init_st (ops_of l) (ops_of (inverse_st b));
  inverse_diff_id_s2' (ops_of l) (ops_of a) (ops_of b);
  assume (forall rid. mem_rid rid (diff (ops_of a) (ops_of l)) ==> 
                 ~ (mem_rid rid (diff (ops_of (inverse_st b)) (ops_of l)))); ()


let cons_reps_s1' (l a b:st)
  : Lemma (requires cons_reps_s1_gt0 l a b)
          (ensures cons_reps l (inverse_st a) b) =
  lem_inverse (ops_of l) (ops_of a);
  split_prefix init_st (ops_of l) (ops_of (inverse_st a));
  inverse_diff_id_s1' (ops_of l) (ops_of a) (ops_of b);
  assume (forall rid. mem_rid rid (diff (ops_of (inverse_st a)) (ops_of l)) ==> 
                 ~ (mem_rid rid (diff (ops_of b) (ops_of l)))); ()

/////////////////////////////////////////////////////////////////////////////

// Prove that merge is commutative
val merge_comm (l a b:st)
  : Lemma (requires cons_reps l a b)
          (ensures (eq (merge (v_of l) (v_of a) (v_of b)) 
                       (merge (v_of l) (v_of b) (v_of a)))) 

val merge_idem (s:st)
  : Lemma (ensures eq (merge (v_of s) (v_of s) (v_of s)) (v_of s))

val fast_fwd (a b:st)
  : Lemma (requires cons_reps a a b)
          (ensures eq (merge (v_of a) (v_of a) (v_of b)) (v_of b))

val merge_eq (l a b a':concrete_st)
  : Lemma (requires eq a a')
          (ensures eq (merge l a b)
                      (merge l a' b))

val lin_rc (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\
                    fst last1 <> fst last2 /\ ~ (comm_ops last1 last2) /\ Fst_snd? (rc last1 last2))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))

val lin_comm (l a b:st) (last1 last2:op_t)
  : Lemma (requires cons_reps l a b /\
                    fst last1 <> fst last2 /\ comm_ops last1 last2 /\
                    ~ (reorder last2 (diff (snoc (ops_of a) last1) (ops_of l))))
          (ensures eq (do (merge (v_of l) (do (v_of a) last1) (v_of b)) last2)
                      (merge (v_of l) (do (v_of a) last1) (do (v_of b) last2)))

val inter_merge1 (l:concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o2 <> fst o3 /\ 
                    ~ (comm_ops o3 o1) /\ ~ (comm_ops o3 o2) /\
                    Fst_snd? (rc o3 o1) /\ Fst_snd? (rc o3 o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do l o3) o1)) (do (do (do l o3) o1) o2))

val inter_merge2 (l s s':concrete_st) (o1 o2 o3:op_t)
  : Lemma (requires fst o2 <> fst o3 /\ fst o1 <> fst o3 /\
                    ~ (comm_ops o3 o1) /\ ~ (comm_ops o3 o2) /\
                    Fst_snd? (rc o3 o1) /\ Fst_snd? (rc o3 o2) /\
                    eq (merge l s (do l o3)) s' /\
                    eq (merge s (do s o2) s') (do s' o2))
          (ensures eq (merge (do s o1) (do (do s o1) o2) (do s' o1)) (do (do s' o1) o2))

val inter_merge3 (l a b c:concrete_st) (op op':op_t) 
  : Lemma (requires eq (merge l a b) c /\
                    (forall (o:op_t). eq (merge l a (do b o)) (do c o)))
          (ensures eq (merge l a (do (do b op) op')) (do (do c op) op'))

val inter_merge4 (l s:concrete_st) (o1 o2 o3 o4:op_t)
  : Lemma (requires fst o1 <> fst o3 /\ fst o1 <> fst o4 /\ fst o2 <> fst o3 /\
                    ~ (comm_ops o3 o1) /\ ~ (comm_ops o3 o2) /\ ~ (comm_ops o4 o1) /\
                    Fst_snd? (rc o3 o1) /\ Fst_snd? (rc o3 o2) /\ Fst_snd? (rc o4 o1) /\
                    eq (merge (do l o1) (do (do l o1) o2) (do (do s o3) o1)) (do (do (do s o3) o1) o2))
          (ensures eq (merge (do l o1) (do (do l o1) o2) (do (do (do s o4) o3) o1)) 
                      (do (do (do (do s o4) o3) o1) o2))

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
val concrete_st_s : Type0

// init state 
val init_st_s : concrete_st_s

// apply an operation to a state 
val do_s (st_s:concrete_st_s) (_:op_t) : concrete_st_s

// equivalence relation between the concrete states of sequential type and MRDT
val eq_sm (st_s:concrete_st_s) (st:concrete_st) : Type0

// initial states are equivalent
val initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st)

// equivalence between states of sequential type and MRDT at every operation
val do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op))

////////////////////////////////////////////////////////////////
