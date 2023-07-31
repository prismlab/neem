module App_do_pre_merge_pre

open SeqUtils
module L = FStar.List.Tot

type node =
| Leaf 
| Node : (pos & nat) -> list node -> node

type concrete_st =
| Root : list node -> concrete_st

let (a:concrete_st) = (Root [(Node (1,0) [Leaf])])

let get_lst (s:concrete_st) = 
  let Root l = s in l

let rec mem' (value:(pos * nat)) (l:list node) =
  match l with
  |[] -> false
  |x::xs -> match x with
          |Leaf -> false
          |Node x lst -> value = x || mem' value lst || mem' value xs

let mem (value:(pos * nat)) (s:concrete_st) = mem' value (get_lst s)

let _ = assert (mem (4,1) (Root [(Node (4,1) [(Node (2,1) [])]); (Node (3,1) [])]))

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
