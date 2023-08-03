module App_do_pre_merge_pre

open SeqUtils
module L = FStar.List.Tot

type node =
//| Leaf 
| Node : (pos & nat) -> list node -> node

type concrete_st' =
| Root : list node -> concrete_st'

let get_lst (s:concrete_st') = 
  let Root l = s in l

let rec mem' (value:(pos & nat)) (l:list node) =
  match l with
  |[] -> false
  |x::xs -> match x with
          //|Leaf -> false
          |Node x lst -> value = x || mem' value lst || mem' value xs

let mem (value:(pos & nat)) (s:concrete_st') = mem' value (get_lst s)

let rec mem_id_s' (id:pos) (l:list node) 
  : Tot (b:bool{b = true <==> (exists ele. mem' (id, ele) l)}) =
  match l with
  |[] -> false
  |x::xs -> match x with
          //|Leaf -> false
          |Node (v,_) lst -> id = v || mem_id_s' id lst || mem_id_s' id xs

let mem_id_s (id:pos) (s:concrete_st') = mem_id_s' id (get_lst s)

let _ = assert (mem_id_s 1 (Root 
                            [(Node (4,1) 
                              [(Node (1,1) [])]); 
                               (Node (1,1) []); 
                                ]))

let rec unique_st' (l:list node) =
  match l with
  |[] -> True
  |x::xs -> match x with
          //|Leaf -> True
          |Node (id,_) lst -> not (mem_id_s' id lst) /\ not (mem_id_s' id xs) /\ unique_st' lst /\ unique_st' xs
                             /\ (forall id. mem_id_s' id xs ==> not (mem_id_s' id lst))

let rec count (id:pos) (l:list node) : nat =
  match l with
  | [] -> 0
  | x::xs -> match x with
           //|Leaf -> count id xs
           |Node (node_id, _) xs' -> let rest_count = count id xs in
                                    let rest_count' = count id xs' in
                                    let node_count = if node_id = id then 1 else 0 in
                                    rest_count + node_count + rest_count'

let _ = assert (count 1 [(Node (2,1) 
                           [(Node (1,1) [])]);
                         (Node (1,1) []); 
                         (Node (1,1) [])] = 3)

let rec sorted_lst (l:list (pos * nat)) =
  match l with
  |[] -> true
  |[x] -> true
  |x::y::xs -> fst x > fst y && sorted_lst (y::xs)

let rec get_children (id:pos) (l:list node{mem_id_s' id l /\ unique_st' l}) = 
  match l with
  |x::xs -> match x with
          |Node value children -> if fst value = id then children 
                                 else if mem_id_s' id children then get_children id children
                                 else get_children id xs

let rec get_chldn_lst (l:list node) =
  match l with
  |[] -> []
  |(Node v _)::xs -> v::get_chldn_lst xs

let rec get_children_lst (id:pos) (l:list node{mem_id_s' id l}) =
  match l with
  |Node value chldn::xs -> if fst value = id then get_chldn_lst chldn 
                         else if mem_id_s' id chldn then get_children_lst id chldn
                         else get_children_lst id xs
                         
let unique_st (s:concrete_st') = unique_st' (get_lst s)

let sorted' (l:list node) = sorted_lst (get_chldn_lst l) /\
                            (forall id. mem_id_s' id l ==> sorted_lst (get_children_lst id l))

let sorted (s:concrete_st') = sorted' (get_lst s)

type concrete_st = s:concrete_st'{unique_st s /\ sorted s}

let _ = assert (mem (4,1) (Root [(Node (4,1) [(Node (2,1) [])]); (Node (3,1) [])]))

// init state
let init_st = (Root [])

// equivalence between 2 concrete states
let eq (a b:concrete_st) = a == b

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
// (the only operation is Add, so nat is fine)
type app_op_t:eqtype = 
  |Add_after : after_id:nat -> ele:nat -> app_op_t //inserts ele after after_id

let get_after_id (o:op_t) : nat =
  let (_, Add_after id _) = o in id

let get_ele (o:op_t) : nat =
  let (_, Add_after _ ele) = o in ele
  
let do_pre (s:concrete_st) (o:op_t) =
  let (ts, Add_after after_id _) = o in
  ~ (mem_id_s ts s) /\
  (~ (after_id = 0) ==> mem_id_s after_id s) /\
  (forall id. mem_id_s id s ==> fst o > id)

let rec contains_child (child:(pos & nat)) (children:list node) =
  match children with
  |[] -> false
  |x::xs -> match x with
          //|Leaf -> contains_child child xs
          |Node y _ -> child = y || contains_child child xs

//immediate child
let rec is_child (child:(pos & nat)) (parent:pos) (l:list node) =
  match l with
  |[] -> false
  |x::xs -> match x with
          //|Leaf -> is_child child parent xs
          |Node x children -> if fst x = parent then contains_child child children 
                             else (is_child child parent children || is_child child parent xs)


let rec lem_same (l l1:list node) 
  : Lemma (requires unique_st' l /\ unique_st' l1 /\
                    (get_chldn_lst l = get_chldn_lst l1) /\
                    (forall id. mem_id_s' id l /\ mem_id_s' id l1 ==>
                           get_children_lst id l = get_children_lst id l1))
          (ensures l = l1) 
          (decreases %[l;l1]) =
  match l, l1 with
  |[],[] -> ()
  |[],_ |_,[] -> ()
  |Node p1 c1::xs, Node p2 c2::ys -> lem_same c1 c2; lem_same xs ys
  
let check' (l:list node)
  : Lemma (requires l == [(Node (2,1) 
                           [(Node (4,1) 
                             [(Node (5,1) 
                               [(Node (6,1) []);
                                (Node (7,1) [])])]);
                            (Node (10,1) [])]);
                         (Node (1,1) []); 
                         (Node (3,1) [])])
          (ensures mem_id_s' 3 l /\ unique_st' l /\ get_children 5 l = [(Node (6,1) []);
                                                                      (Node (7,1) [])]) = ()
          
let rec is_sibling (s1 s2:(pos * nat)) (l:list node) =
  match l with
  |[] -> false 
  |[x] -> (match x with
         //|Leaf -> false
         |Node y children -> is_sibling s1 s2 children)
  |x::y::xs -> match x,y with
            //|Leaf, Leaf -> is_sibling s1 s2 xs
            //|Leaf, _ -> is_sibling s1 s2 (y::xs)
            //|_, Leaf -> is_sibling s1 s2 xs
            |Node x1 chld1, Node x2 chld2 -> (x1 = s1 && x2 = s2) || is_sibling s1 s2 chld1
                                            || is_sibling s1 s2 chld2 || is_sibling s1 s2 (y::xs)

let check (l:list node)
  : Lemma (requires l == [(Node (2,1) 
                           [(Node (4,1) 
                             [(Node (5,1) 
                               [(Node (6,1) [])])])]);
                         (Node (1,1) []); 
                         (Node (3,1) [])])
          (ensures is_child (6,1) 5 l /\ not (is_child (5,1) 2 l)) = ()

let check1 (l:list node)
  : Lemma (requires l == [(Node (2,1) 
                           [(Node (4,1) 
                             [(Node (5,1) 
                               [(Node (6,1) []);
                                (Node (7,1) [])])]);
                            (Node (10,1) [])]);
                         (Node (1,1) []); 
                         (Node (3,1) [])])
          (ensures is_sibling (4,1) (10,1) l) = ()
          
#push-options "--z3rlimit 50 --ifuel 1"
let rec add_after_id (l:list node{unique_st' l /\ sorted' l}) 
                     (ts:pos{not (mem_id_s' ts l) /\ (forall id. mem_id_s' id l ==> ts > id)}) 
                     (after_id:pos{mem_id_s' after_id l}) 
                     (ele:nat) 
   : Tot (r:list node{unique_st' r /\ mem_id_s' ts r /\ sorted' r /\
                      (forall id. mem_id_s' id r <==> mem_id_s' id l \/ id = ts) /\
                      is_child (ts, ele) after_id r /\
                      get_children_lst after_id r = (ts, ele)::get_children_lst after_id l /\
                      get_chldn_lst l = get_chldn_lst r /\
                      (forall id. mem_id_s' id l /\ id <> after_id ==>
                         (get_children_lst id l = get_children_lst id r))})
     (decreases l) =
  match l with
  |x::xs -> if mem_id_s' after_id [x] then 
    (let child' = (match x with
                  |Node value children -> if fst value = after_id 
                                        then (//assert (forall id. mem_id_s' id children ==>
                                                //            get_children_lst id l = get_children_lst id children);
                                              Node value (Node (ts,ele) []::children))
                                        else (//assert (mem_id_s' after_id children); 
                                              Node value (add_after_id children ts after_id ele))) in
                                        
      (assert (not (mem_id_s' after_id xs)); 
       assert (forall id. mem_id_s' id xs ==> get_children_lst id xs = get_children_lst id l);
       let r = child'::xs in
       (*assert (is_child (ts,ele) after_id r);
       assert (mem_id_s' ts r); 
       assert (unique_st' r);
       assert (forall id. mem_id_s' id l /\ id <> after_id ==>
                         (get_children_lst id l = get_children_lst id r)); *)
       r))
    else
    (let r = x::(add_after_id xs ts after_id ele) in 
     (*assert (is_child (ts,ele) after_id r);
     assert (mem_id_s' ts r); 
     assert (unique_st' r);*)
     r)

let do (s:concrete_st) (op:op_t{do_pre s op}) 
  : (r:concrete_st{(get_after_id op = 0 ==> 
         (get_chldn_lst (get_lst r) = (fst op, get_ele op)::get_chldn_lst (get_lst s) /\
         (forall id. mem_id_s id s /\ mem_id_s id r ==>
                get_children_lst id (get_lst s) = get_children_lst id (get_lst r))))}) =
  
  if get_after_id op = 0 then (Root ((Node (fst op, get_ele op) [])::(get_lst s)))
  else (assert (get_after_id op > 0);
        Root (add_after_id (get_lst s) (fst op) (get_after_id op) (get_ele op)))

let lem_do (a b:concrete_st) (op:op_t)
   : Lemma (requires eq a b /\ do_pre a op)
           (ensures eq (do a op) (do b op)) = ()

//conflict resolution
let resolve_conflict (x:op_t) (y:op_t{fst x <> fst y}) : resolve_conflict_res = 
  match x, y with
  |(ts1, (Add_after id1 _)), (ts2, (Add_after id2 _)) -> if id1 = id2 then 
                                                           if ts1 > ts2 then First_then_second else Second_then_first 
                                                        else First_then_second //ts1 <> id2 /\ ts2 <> id1


(*
type concrete_st' = 
  |Leaf
  |Node : (pos * nat) -> list concrete_st' -> concrete_st' 
  
let rec mem_id_s (id:pos) (t:concrete_st) : Tot bool =
  match t with
  |Leaf -> false
  |Node x children -> fst x = id || mem_child_id_s id children

and mem_child_id_s (id:pos) (children:list concrete_st') : Tot bool =
  match children with
  |[] -> false
  |x::xs -> mem_id_s id x || mem_child_id_s id xs

let rec count_id_s (id:pos) (t:concrete_st'): Tot int =
  let rec count_id_helper (id:pos) (t: concrete_st'): Tot int =
    match t with
    | Leaf -> 0 
    //| Node (0,_) [] -> 0
    | Node x children ->
      let occurrences = if fst x = id then 1 else 0 in
      let child_occurrences = count_id_children id children in
      occurrences + child_occurrences
  and count_id_children (id:pos) (children: list concrete_st'): Tot int =
    match children with
    | [] -> 0
    | c::cs -> count_id_helper id c + count_id_children id cs
  in
  count_id_helper id t
  
let unique_st (t:concrete_st') = (forall id. count_id_s id t <= 1)

let preorder_traversal (t:concrete_st') : Tot (list (nat * nat)) =
  let rec traverse (acc:list (nat * nat)) (lst:list concrete_st') : Tot (list (nat * nat)) (decreases lst) =
    match lst with
    |[] -> acc
    |Leaf::xs -> traverse acc xs
    |Node x children::xs ->
      let acc' = x::acc in
      let acc'' = traverse acc' children in
      traverse acc'' xs in
  traverse [] [t]

let rec mem' (value:(pos * nat)) (t:node) : Tot bool =
  match t with
  |Leaf -> false
  |Node x children -> x = value || mem_child value children

and mem_child (value:(pos * nat)) (children:list node) : Tot bool =
  match children with
  |[] -> false
  |x::xs -> mem' value x || mem_child value xs

let rec contains_child (child:(pos * nat)) (children:list concrete_st') =
  match children with
  |[] -> false
  |x::xs -> match x with
          |Leaf -> contains_child child xs
          |Node y _ -> child = y || contains_child child xs

let rec is_child (child parent:(pos * nat)) (t:concrete_st') =
  match t with
  |Leaf -> false
  |Node x children -> if x = parent then contains_child child children 
                     else is_child_helper child parent children

and is_child_helper (child parent:(pos * nat)) (lst:list concrete_st') =
  match lst with
  |[] -> false
  |x::xs -> is_child child parent x || is_child_helper child parent xs

let add_at_front (ele:(pos * nat)) (t:concrete_st') 
  : (r:concrete_st'{(forall e. mem e r <==> mem e t \/ e = ele)
                    ///\ (forall c p. mem c t /\ mem p t /\ is_child c p t ==> mem c r /\ mem p r /\ is_child c p r)
                    }) =
  match t with
  |Leaf ->  Node ele []
  |Node x children -> Node ele [Node x children] 

let rec add_after (id:pos) (ele:(pos * nat)) (t:concrete_st') : Tot concrete_st' =
  match t with
  |Leaf -> Leaf
  |Node value children -> if fst value = id then (Node value ((Node ele [])::children))
                         else Node value (add_after_helper id ele children)

and add_after_helper (id:pos) (ele:(pos * nat)) (lst:list concrete_st') : Tot (list concrete_st') =
  match lst with
  |[] -> []
  |x::xs -> let child' = add_after id ele x in
          child'::add_after_helper id ele xs


*)
