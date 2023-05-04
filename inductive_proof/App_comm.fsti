module App_comm

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

type op_t = timestamp_t & app_op_t

type log = seq op_t

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

let rec lem_seq_foldl_forall (l:log) 
  : Lemma (requires true)
          (ensures (forall x. (length l > 0 ==> (apply_log x l == apply_log (do x (head l)) (tail l)) /\
                                          (apply_log x l == do (apply_log x (fst (un_snoc l))) (last l))) /\
                         (length l = 0 ==> apply_log x l == x)))
                   
                   (decreases length l) =
  match length l with
  |0 -> ()
  |_ -> lem_seq_foldl_forall (tail l)

type st1 = s:st0{(v_of s == apply_log init_st (ops_of s))}

// valid state
let valid_st (s:st0) : prop =
  distinct_ops (ops_of s) /\
  (v_of s == apply_log init_st (ops_of s))

type st = s:st0{valid_st s}

type resolve_conflict_res =
  | First_then_second //consider both op1 & op2 but apply op1 at the end
  | Second_then_first //consider both op1 & op2 but apply op2 at the end

//conflict resolution
val resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res

// concrete merge operation
val concrete_merge (lca s1 s2:concrete_st) : concrete_st

//operations x and y are commutative
val commutative (x y:op_t) : bool

val comm_symmetric (x y:op_t) 
  : Lemma (requires commutative x y)
          (ensures commutative y x)
         // [SMTPat (commutative x y)]
          
// if x and y are commutative ops, applying them in any order should give equivalent results
val commutative_prop (x y:op_t) 
  : Lemma (requires commutative x y)
          (ensures (forall s. eq (apply_log s (cons x (cons y empty))) (apply_log s (cons y (cons x empty)))))

//commutativity for a sequence of operation
let commutative_seq (x:op_t) (l:log) : bool =
  forallb (fun e -> commutative x e) l

let comm_empty_log (x:op_t) (l:log)
  : Lemma (ensures length l = 0 ==> commutative_seq x l) = ()

// returns true if there exists an operation op in log l such that
// 1. last_op and op are non-commutative
// 2. op is commutative with all the operations in the suffix of l
// 3. op should be applied after last_op according to resolve_conflict
let exists_triple (last_op:op_t) (l:log)
  : (b:bool{b = true <==> (exists op. mem op l /\ fst last_op <> fst op /\
                         (let pre,suf = pre_suf l op in
                          not (commutative last_op op) /\
                          Second_then_first? (resolve_conflict last_op op) /\
                          commutative_seq op suf))}) =
  existsb (fun (op:op_t) -> mem op l &&  fst last_op <> fst op &&
                              (let pre,suf = pre_suf l op in
                              not (commutative last_op op) &&
                              Second_then_first? (resolve_conflict last_op op) &&
                              commutative_seq op suf)) l

let fst_t (f,_,_) = f
let snd_t (_,s,_) = s
let thr_t (_,_,t) = t

// returns an operation op in l such that
// 1. last_op and op are non-commutative
// 2. op is commutative with all the operations in the suffix of l
// 3. op should be applied after last_op according to resolve_conflict
#push-options "--z3rlimit 200" 
let rec find_op (last_op:op_t) (l l1:log)
  : Pure op_t
         (requires length l > 0 /\ length l1 > 0 /\
                   (exists op. mem op l /\ mem op l1 /\ 
                          fst last_op <> fst op /\ 
                          not (commutative last_op op) /\
                          Second_then_first? (resolve_conflict last_op op) /\
                          (let _, suf = pre_suf l1 op in
                          commutative_seq op suf)))
         (ensures (fun op -> mem op l /\ mem op l1 /\ 
                          fst last_op <> fst op /\
                          not (commutative last_op op) /\
                          Second_then_first? (resolve_conflict last_op op) /\
                          (let _, suf = pre_suf l1 op in
                          commutative_seq op suf))) (decreases length l) =

 match length l with
  |1 -> last l
  |_ -> let pre, op = un_snoc l in
       if (mem op l1 && fst last_op <> fst op &&
           not (commutative last_op op) &&
           Second_then_first? (resolve_conflict last_op op) &&
           (let _, suf = pre_suf l1 op in
            commutative_seq op suf)) then op 
        else (lemma_mem_snoc pre op;
              find_op last_op pre l1)
              
// returns a triple such that 
// 1. l = (snoc prefix op) ++ suffix
// 2. last_op and op are non-commutative
// 3. op is commutative with all the operations in the suffix of l
// 4. op should be applied after last_op according to resolve_conflict
let find_triple (last_op:op_t) (l:log{(exists_triple last_op l)}) 
  : (t:(log & op_t & log) {mem (snd_t t) l /\ (fst_t t, thr_t t) = pre_suf l (snd_t t) /\
                                is_prefix (fst_t t) l /\ is_suffix (thr_t t) l /\
                                Seq.equal l ((Seq.snoc (fst_t t) (snd_t t)) ++ (thr_t t)) /\
                                length l = length (fst_t t) + 1 + length (thr_t t) /\

                                fst last_op <> fst (snd_t t) /\
                                not (commutative last_op (snd_t t)) /\
                                Second_then_first? (resolve_conflict last_op (snd_t t)) /\
                                commutative_seq (snd_t t) (thr_t t)}) =
  let op = find_op last_op l l in
  let pre, suf = pre_suf l op in
  (pre, op, suf)

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

let rec split_prefix_forall (l:log) (a:log)
  : Lemma (requires is_prefix l a)
          (ensures (forall s. (apply_log s a == apply_log (apply_log s l) (diff a l))) /\
                   (forall e. mem e l ==> mem e a) /\
                   (Seq.length a > Seq.length l ==> (last a) == (last (diff a l))))
          (decreases Seq.length l)
  = match Seq.length l with
    |0 -> ()
    |1 -> ()
    |_ -> split_prefix_forall (tail l) (tail a)

// returns the inverse state by undoing the last operation
#push-options "--z3rlimit 50"
let inverse_st (s:st{Seq.length (ops_of s) > 0}) 
  : GTot (i:st{(v_of s == do (v_of i) (last (ops_of s))) /\
               (ops_of i == fst (un_snoc (ops_of s))) /\
               (ops_of s == snoc (ops_of i) (last (ops_of s))) /\
               length (ops_of i) = length (ops_of s) - 1 /\
               is_prefix (ops_of i) (ops_of s) /\
               (let _, last2 = un_snoc (ops_of s) in
               (lem_last (ops_of s);
               s == (do (v_of i) last2, hide (snoc (ops_of i) last2)))) /\
               (forall id. mem_id id (ops_of i) <==> mem_id id (ops_of s) /\ id <> fst (last (ops_of s)))}) = 
  lem_apply_log init_st (ops_of s);
  let p, l = un_snoc (ops_of s) in
  let r = apply_log init_st p in
  lemma_split (ops_of s) (length (ops_of s) - 1); 
  lemma_append_count_assoc_fst p (snd (split (ops_of s) (length (ops_of s) - 1))); 
  distinct_invert_append p (snd (split (ops_of s) (length (ops_of s) - 1))); 
  (r, hide p)

let rec inverse_helper (s:concrete_st) (l':log) (op:op_t)
  : Lemma 
    (ensures (let l = Seq.snoc l' op in 
              (apply_log s l == do (apply_log s l') op)))
    (decreases length l')
  = Seq.un_snoc_snoc l' op;
    match length l' with
    |0 -> ()
    |_ ->  inverse_helper (do s (head l')) (tail l') op

let lem_eq_is_equiv_st (x:concrete_st) (a b:log)
  : Lemma (requires (a == b /\ apply_log x a == apply_log x b))
          (ensures eq (apply_log x a) (apply_log x b))
          [SMTPat (eq (apply_log x a) (apply_log x b))] = 
  eq_is_equiv (apply_log x a) (apply_log x b)
  
let lem_eq_is_equiv (a b:log)
  : Lemma (requires (a == b /\ (forall x. apply_log x a == apply_log x b)))
          (ensures (forall x. eq (apply_log x a) (apply_log x b))) = ()

let lem_len_0 (l:log)
  : Lemma (requires length l = 0)
          (ensures (forall x. apply_log x l == x)) = ()

let lem_eq_is_equiv_c3_st (x:concrete_st) (l:log) (op hd:op_t) (tl:log)
  : Lemma (requires eq (apply_log x (cons op l)) (apply_log (do x hd) (cons op tl)) /\
                    eq (apply_log (do x hd) (cons op tl)) (apply_log (do x hd) (snoc tl op)))
          (ensures eq (apply_log x (cons op l)) (apply_log (do x hd) (snoc tl op)))
          [SMTPat (eq (apply_log x (cons op l)) (apply_log (do x hd) (snoc tl op)))] = 
  transitive (apply_log x (cons op l)) 
             (apply_log (do x hd) (cons op tl))
             (apply_log (do x hd) (snoc tl op))

let lem_case1 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. apply_log x (cons op l) == (apply_log (apply_log x (cons op (create 1 hd))) tl))))
          (decreases length l) = 
  let hd = head l in let tl = tail l in
  assert (is_prefix (cons op (create 1 hd)) (cons op l));
  assert (cons op l = cons op (cons hd tl));
  assert (cons op (cons hd tl) = cons op (append (create 1 hd) tl)); 
  append_assoc (create 1 op) (create 1 hd) tl;
  assert (cons op (append (create 1 hd) tl) = (cons op (create 1 hd)) ++ tl);
  assert ((cons op (cons hd tl)) = (cons op (create 1 hd)) ++ tl); 
  assert (cons op l = (cons op (create 1 hd)) ++ tl);

  lem_is_diff ((cons op (create 1 hd)) ++ tl) (cons op (create 1 hd)) tl;  
  assert (tl = diff (cons op l) (cons op (create 1 hd)));
  split_prefix_forall (cons op (create 1 hd)) (cons op l)
  
let lem_case3 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. apply_log x (cons hd (cons op tl)) == (apply_log (do x hd) (cons op tl)))))
                   (decreases length l) = 
  let hd = head l in let tl = tail l in
  assert (head (cons hd (cons op tl)) = hd); 
  lemma_tl hd (cons op tl);
  assert (tail (cons hd (cons op tl)) = (cons op tl));
  lem_seq_foldl_forall (cons hd (cons op tl))

let lem_case4 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                   (forall x. apply_log (do x hd) (snoc tl op) == (apply_log x (snoc l op)))))
          (decreases length l) = 
  let hd = head l in let tl = tail l in
  assert (head (cons hd (snoc tl op)) = hd);
  lemma_tl hd (snoc tl op);
  lemma_tail_snoc (cons hd tl) op;
  assert (tail (cons hd (snoc tl op)) = (snoc tl op));
  lem_seq_foldl_forall (cons hd (snoc tl op))

let rec lem_equiv_st_foldl_st (a b:concrete_st) (l:log)
  : Lemma (requires eq a b) 
          (ensures eq (apply_log a l) (apply_log b l))
          (decreases length l)
          [SMTPat (eq (apply_log a l) (apply_log b l))] =
  match length l with
  |0 -> ()
  |_ -> lem_do a b (head l);
       lem_equiv_st_foldl_st (do a (head l)) (do b (head l)) (tail l)
                         
let lem_equiv_st_foldl (a b:log) (l:log)
  : Lemma (ensures (forall x. eq (apply_log x a) (apply_log x b) ==>
                         eq (apply_log (apply_log x a) l) (apply_log (apply_log x b) l))) = ()
                         
let lem_case2_help (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0)
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. eq (apply_log (apply_log x (cons op (create 1 hd))) tl) 
                             (apply_log (apply_log x (cons hd (create 1 op))) tl))))
          (decreases length l) = 
  let hd = head l in let tl = tail l in
  commutative_prop op hd;
  assert (forall x. eq (apply_log x (cons op (create 1 hd))) (apply_log x (cons hd (create 1 op))));
  lem_equiv_st_foldl (cons op (create 1 hd)) (cons hd (create 1 op)) tl

let lem_case2_help1 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. eq (apply_log (apply_log x (cons op (create 1 hd))) tl) 
                             (apply_log (apply_log x (cons hd (create 1 op))) tl))))
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. apply_log (apply_log x (cons hd (create 1 op))) tl ==
                          apply_log x (cons hd (cons op tl))))) = 
  let hd = head l in let tl = tail l in
  assert (is_prefix (cons hd (create 1 op)) (cons hd (cons op tl)));
  append_assoc (create 1 hd) (create 1 op) tl;
  assert (cons hd (cons op tl) = (cons hd (create 1 op) ++ tl));
  lem_is_diff (cons hd (cons op tl)) (cons hd (create 1 op)) tl;
  assert (tl = diff (cons hd (cons op tl)) (cons hd (create 1 op)));
  split_prefix_forall (cons hd (create 1 op)) (cons hd (cons op tl));
  ()

let lem_case2 (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l /\ length l > 0 /\
                    (let hd = head l in let tl = tail l in
                    (forall x. eq (apply_log (apply_log x (cons op (create 1 hd))) tl) 
                             (apply_log (apply_log x (cons hd (create 1 op))) tl) /\
                          apply_log (apply_log x (cons hd (create 1 op))) tl ==
                          apply_log x (cons hd (cons op tl)))))
          (ensures (let hd = head l in let tl = tail l in
                    (forall x. eq (apply_log (apply_log x (cons op (create 1 hd))) tl) 
                             (apply_log x (cons hd (cons op tl)))))) = ()

let rec lem_foldl_comm (l:log) (op:op_t)
  : Lemma (requires commutative_seq op l /\ distinct_ops l)
          (ensures (forall x. eq (apply_log x (cons op l)) (apply_log x (snoc l op)))) (decreases length l) =
  match length l with
  |0 -> lemma_empty l; 
       append_empty_r (create 1 op); 
       append_empty_l (create 1 op);
       assert (forall x. apply_log x (cons op l) == apply_log x (snoc l op));
       lem_eq_is_equiv (cons op l) (snoc l op)
      
  |_ -> let hd = head l in let tl = tail l in
       assert (l == cons hd tl);
       distinct_invert_append (create 1 hd) tl;
       assert (commutative_seq op tl /\ distinct_ops tl);
       lem_foldl_comm tl op;  
       lem_case1 l op; // eq (apply_log x (cons op l)) (seq_foldl (apply_log x (cons op (create 1 hd))) tl))
       lem_case2_help l op;
       lem_case2_help1 l op;
       lem_case2 l op; // eq (apply_log (seq_foldl x (cons op (create 1 hd))) tl) (apply_log x (cons hd (cons op tl))));      
       lem_case3 l op; // eq (apply_log x (cons hd (cons op tl))) (apply_log (do x hd) (cons op tl)))       
       assert (forall x. eq (apply_log (do x hd) (cons op tl)) (apply_log (do x hd) (snoc tl op))); // from IH       
       lem_case4 l op // eq (apply_log (do x hd) (snoc tl op)) (apply_log x (snoc l op)));

let lem_seq_foldl_split (x:concrete_st) (p:log) (s:log)
  : Lemma (ensures apply_log (apply_log x p) s == (apply_log x (p ++ s)))
          (decreases length p) =
  lem_is_diff (p ++ s) p s;
  split_prefix x p (p ++ s)

let lem_seq_foldl_op (x:concrete_st) (l:log) (op:op_t)
  : Lemma (requires distinct_ops l /\ mem op l /\
                    (let _, s = pre_suf l op in commutative_seq op s))
          (ensures (let p,s = pre_suf l op in
                      eq (apply_log x l) (do (apply_log x (p ++ s)) op)))
          (decreases length l) = 
  let pre, suf = pre_suf l op in
  assert (commutative_seq op suf); 
  pre_suf_prop l op;
  lem_foldl_comm suf op;
  assert (forall x. eq (apply_log x (cons op suf)) (apply_log x (snoc suf op)));
  split_prefix x pre l;
  append_assoc pre (create 1 op) suf;
  assert (l == (snoc pre op) ++ suf /\ l == pre ++ (cons op suf)); 
  lem_is_diff l pre (cons op suf);

  pre_suf_prop l op;
  assert (distinct_ops (pre ++ suf));
  assert (not (mem_id (fst op) (pre ++ suf)));
  distinct_append pre suf;
  distinct_append (pre ++ suf) (create 1 op);
  append_assoc pre suf (create 1 op);
  assert (distinct_ops (pre ++ (snoc suf op)));

  append_assoc pre suf (create 1 op); 
  lem_is_diff (snoc (pre ++ suf) op) (pre ++ suf) (create 1 op);
  assert (is_prefix (pre ++ suf) (snoc (pre ++ suf) op));
  split_prefix x (pre ++ suf) (snoc (pre ++ suf) op); 
  assert (length (snoc (pre ++ suf) op) > 0);
  lem_apply_log x (snoc (pre ++ suf) op);
  lem_last (snoc (pre ++ suf) op); 
  un_snoc_snoc (pre ++ suf) op;
  
  assert (apply_log x l == apply_log (apply_log x pre) (cons op suf));
  assert (eq (apply_log x l) (apply_log (apply_log x pre) (snoc suf op))); 
  lem_seq_foldl_split x pre (snoc suf op);

  assert (apply_log x (snoc (pre ++ suf) op) == do (apply_log x (pre ++ suf)) op);
  assert (apply_log x (snoc (pre ++ suf) op) == apply_log x (pre ++ (snoc suf op)));
  assert (apply_log x (pre ++ (snoc suf op)) == apply_log (apply_log x pre) (snoc suf op));
  
  assert (apply_log (apply_log x pre) (snoc suf op) == do (apply_log x (pre ++ suf)) op);
  
  eq_is_equiv (apply_log (apply_log x pre) (snoc suf op)) (do (apply_log x (pre ++ suf)) op);
  transitive (apply_log x l) (apply_log (apply_log x pre) (snoc suf op)) (do (apply_log x (pre ++ suf)) op)

// returns the inverse state by undoing operation op in (ops_of s)
let inverse_st_op (s:st) (op:op_t{mem op (ops_of s) /\ 
                           (let _, suf = pre_suf (ops_of s) op in
                            commutative_seq op suf)})
  : GTot (i:st{(let (pre,suf) = pre_suf (ops_of s) op in
               eq (v_of s) (do (v_of i) op) /\
               (ops_of i == (pre ++ suf)) /\
               (ops_of s == (Seq.snoc pre op) ++ suf) /\
               is_prefix pre (ops_of s) /\ is_prefix pre (ops_of i) /\
               length (ops_of i) = length (ops_of s) - 1 /\
               (forall id. (mem_id id (ops_of i) \/ id = fst op) <==> mem_id id (ops_of s)) /\
               (forall id. mem_id id (ops_of i) <==> (mem_id id (ops_of s) /\ id <> fst op)))}) = 
  let pre, suf = pre_suf (ops_of s) op in
  pre_suf_prop (ops_of s) op;
  lem_seq_foldl_op init_st (ops_of s) op;
  let v_i = apply_log init_st (pre ++ suf) in
  assert (eq (v_of s) (do v_i op));
  (v_i, hide (pre ++ suf))

let inverse_diff_id_inv1' (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))) /\
                    (let _, last2 = un_snoc b in
                    exists_triple last2 (diff a l)))
          (ensures (let _, last2 = un_snoc b in
                    let (pre1, op1, suf1) = find_triple last2 (diff a l) in
                    not (mem_id (fst op1) l) /\
                    not (mem_id (fst op1) (pre1 ++ suf1)) /\
                    not (mem_id (fst op1) b) /\
                    (forall id. mem_id id pre1 ==> mem_id id (diff a l)) /\
                    (forall id. mem_id id suf1 ==> mem_id id (diff a l)))) = 
  let _, last2 = un_snoc b in
  let (pre1, op1, suf1) = find_triple last2 (diff a l) in
  lem_diff a l;
  pre_suf_prop (diff a l) op1; 
  assert (not (mem_id (fst op1) (pre1 ++ suf1))); 
  lem_suf_equal2 l a op1;
  assert (not (mem_id (fst op1) l));
  lem_diff b l;
  mem_ele_id op1 (diff a l);
  assert (not (mem_id (fst op1) (diff b l)));
  assert (not (mem_id (fst op1) b));
  ()
                    
let inverse_diff_id_inv2' (l a b:log)
  : Lemma (requires distinct_ops l /\ distinct_ops a /\ distinct_ops b /\
                    is_prefix l a /\ is_prefix l b /\
                    length a > length l /\ length b > length l /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff a l) ==> lt id id1) /\
                    (forall id id1. mem_id id l /\ mem_id id1 (diff b l) ==> lt id id1) /\
                    (forall id. mem_id id (diff a l) ==> not (mem_id id (diff b l))) /\
                    (let _, last1 = un_snoc a in
                    exists_triple last1 (diff b l)))
          (ensures (let _, last1 = un_snoc a in
                    let (pre2, op2, suf2) = find_triple last1 (diff b l) in
                    not (mem_id (fst op2) l) /\
                    not (mem_id (fst op2) (pre2 ++ suf2)) /\
                    not (mem_id (fst op2) a) /\
                    (forall id. mem_id id pre2 ==> mem_id id (diff b l)) /\
                    (forall id. mem_id id suf2 ==> mem_id id (diff b l)))) = 
  let _, last1 = un_snoc a in
  let (pre2, op2, suf2) = find_triple last1 (diff b l) in
  lem_diff b l;
  pre_suf_prop (diff b l) op2; 
  assert (not (mem_id (fst op2) (pre2 ++ suf2))); 
  lem_suf_equal2 l b op2;
  assert (not (mem_id (fst op2) l));
  lem_diff a l;
  mem_ele_id op2 (diff b l);
  assert (not (mem_id (fst op2) (diff a l)));
  assert (not (mem_id (fst op2) a));
  ()

let consistent_branches (lca s1 s2:st1) =
  distinct_ops (ops_of lca) /\ distinct_ops (ops_of s1) /\ distinct_ops (ops_of s2) /\
  is_prefix (ops_of lca) (ops_of s1) /\
  is_prefix (ops_of lca) (ops_of s2) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s1) (ops_of lca)) ==> lt id id1) /\
  (forall id id1. mem_id id (ops_of lca) /\ mem_id id1 (diff (ops_of s2) (ops_of lca)) ==> lt id id1) /\
  (forall id. mem_id id (diff (ops_of s1) (ops_of lca)) ==> not (mem_id id (diff (ops_of s2) (ops_of lca))))

let consistent_branches_s1_gt0 (lca s1 s2:st1) =
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca)

let consistent_branches_s2_gt0 (lca s1 s2:st1) =
  consistent_branches lca s1 s2 /\
  length (ops_of s2) > length (ops_of lca)

let consistent_branches_s1s2_gt0 (lca s1 s2:st1) =
  consistent_branches lca s1 s2 /\
  length (ops_of s1) > length (ops_of lca) /\
  length (ops_of s2) > length (ops_of lca)

let do_st (s:st1) (o:op_t) : st1 =
  split_prefix init_st (ops_of s) (snoc (ops_of s) o); 
  (do (v_of s) o, hide (snoc (ops_of s) o))

// Prove that merge is commutative
val merge_is_comm (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2)
          (ensures (eq (concrete_merge (v_of lca) (v_of s1) (v_of s2)) 
                       (concrete_merge (v_of lca) (v_of s2) (v_of s1)))) 
                       
val lem_trans_merge_s1' (lca s1 s2 s1':concrete_st)
  : Lemma (requires eq s1 s1' /\
                    (exists l1' l1 l2. s1' == apply_log lca l1' /\ s1 == apply_log lca l1 /\ s2 == apply_log lca l2))
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1' s2))

val lem_trans_merge_s2' (lca s1 s2 s2':concrete_st)
  : Lemma (requires eq s2 s2' /\
                    (exists l1 l2' l2. s1 == apply_log lca l1 /\ s2' == apply_log lca l2' /\ s2 == apply_log lca l2))
          (ensures eq (concrete_merge lca s1 s2)
                      (concrete_merge lca s1 s2'))
                      
// branch s1 does not see new operations
val linearizable_s1_0 (lca s1 s2:st)
  : Lemma (requires consistent_branches lca s1 s2 /\
                    ops_of s1 == ops_of lca)
          (ensures eq (v_of s2) (concrete_merge (v_of lca) (v_of s1) (v_of s2)))

val linearizable_gt0_s2'_op (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     exists_triple last1 (diff (ops_of s2) (ops_of lca)) /\                   
                     (let (_, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                      suf2 == snd (pre_suf (ops_of s2) op2) /\
                      (let s2' = inverse_st_op s2 op2 in
                      consistent_branches lca s1 s2' /\
                      consistent_branches lca s1 (do_st s2' op2)))))
     
          (ensures (let _, last1 = un_snoc (ops_of s1) in
                    let (pre2, op2, suf2) = find_triple last1 (diff (ops_of s2) (ops_of lca)) in
                    let s2' = inverse_st_op s2 op2 in                      
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of s2')) op2)
                       (concrete_merge (v_of lca) (v_of s1) (do (v_of s2') op2))))

val linearizable_gt0_s1'_op (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\                                          
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     exists_triple last2 (diff (ops_of s1) (ops_of lca)) /\                    
                     (let (_, op1, suf1) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                      suf1 == snd (pre_suf (ops_of s1) op1) /\
                      (let s1' = inverse_st_op s1 op1 in
                      consistent_branches lca s1' s2 /\
                      consistent_branches lca (do_st s1' op1) s2))))
       
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    let (pre1, op1, suf2) = find_triple last2 (diff (ops_of s1) (ops_of lca)) in
                    let s1' = inverse_st_op s1 op1 in                     
                    eq (do (concrete_merge (v_of lca) (v_of s1') (v_of s2)) op1)
                       (concrete_merge (v_of lca) (do (v_of s1') op1) (v_of s2))))

val linearizable_gt0_s1' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\                    
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     First_then_second? (resolve_conflict last1 last2) /\
                     consistent_branches lca (inverse_st s1) s2))
        
          (ensures (let _, last1 = un_snoc (ops_of s1) in                  
                    eq (do (concrete_merge (v_of lca) (v_of (inverse_st s1)) (v_of s2)) last1)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))

val linearizable_gt0_s2' (lca s1 s2:st)
  : Lemma (requires consistent_branches_s1s2_gt0 lca s1 s2 /\ 
                    (let _, last1 = un_snoc (ops_of s1) in
                     let _, last2 = un_snoc (ops_of s2) in
                     fst last1 <> fst last2 /\
                     not (exists_triple last1 (diff (ops_of s2) (ops_of lca))) /\
                     not (exists_triple last2 (diff (ops_of s1) (ops_of lca))) /\
                     Second_then_first? (resolve_conflict last1 last2) /\
                     consistent_branches lca s1 (inverse_st s2)))
        
          (ensures (let _, last2 = un_snoc (ops_of s2) in
                    eq (do (concrete_merge (v_of lca) (v_of s1) (v_of (inverse_st s2))) last2)
                       (concrete_merge (v_of lca) (v_of s1) (v_of s2))))

////////////////////////////////////////////////////////////////
//// Sequential implementation //////

// the concrete state 
val concrete_st_s : Type0

// init state 
val init_st_s : concrete_st_s

// apply an operation to a state 
val do_s (st_s:concrete_st_s) (_:op_t) : concrete_st_s

// equivalence relation between the concrete states of sequential type and MRDT
val eq_sm (st_s:concrete_st_s) (st:concrete_st) : prop

// initial states are equivalent
val initial_eq (_:unit)
  : Lemma (ensures eq_sm init_st_s init_st)

// equivalence between states of sequential type and MRDT at every operation
val do_eq (st_s:concrete_st_s) (st:concrete_st) (op:op_t)
  : Lemma (requires eq_sm st_s st)
          (ensures eq_sm (do_s st_s op) (do st op))

////////////////////////////////////////////////////////////////


(*// convergence theorem
val convergence (lca s1 s2 s1':concrete_st) (o:log_entry)
  : Lemma (requires concrete_merge_pre lca s1 s2 /\
                    concrete_merge_pre lca s1' s2 /\
                    concrete_do_pre s1 o /\ eq s1' (do s1 o) /\
                    concrete_merge_pre s1 (concrete_merge lca s1 s2) s1')
          (ensures eq (concrete_merge lca s1' s2) (concrete_merge s1 (concrete_merge lca s1 s2) s1'))*)

