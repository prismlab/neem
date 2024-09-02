let debug_mode = ref false 

type repId = int (* unique replica ID *)

(* unique version number *)
type ver = repId * int (* replicaID, version number *)

type rc_res = (* conflict resolution type *)
  | Fst_then_snd
  | Snd_then_fst
  | Either

(*type state = int 
type op = Incr 
type state = int * bool (* counter, flag *)
type op = 
  | Enable
  | Disable*)

module Ts_ele_pair = struct
  type t = (int * int)
  let compare = compare
end
module Orset = Set.Make(Ts_ele_pair)

type state = Orset.t
type op = 
  | Add of int
  | Rem of int

(* event type *)
type event = int * repId * op (* timestamp, replicaID, operation *)
let get_ts ((t,_,_):event) = t
let init_st = Orset.empty
let mrdt_do s e =
  match e with
  | ts, _, Add e -> Orset.add (ts, e) s
  | _, _, Rem e -> Orset.filter (fun e1 -> snd e1 <> e) s

let mrdt_merge l a b =
  let i = Orset.inter l (Orset.inter a b) in
  let da = Orset.diff a l in
  let db = Orset.diff b l in
  Orset.union i (Orset.union da db)

let rc e1 e2 =
  match e1, e2 with
  | (_, _, Add ele1), (_, _, Rem ele2) -> if ele1 = ele2 then Snd_then_fst else Either
                                            (*else if t1 > t2 then Snd_then_fst 
                                            else if t1 < t2 then Fst_then_snd
                                            else Either*)
  | (_, _, Rem ele1), (_, _, Add ele2) -> if ele1 = ele2 then Fst_then_snd else Either
                                            (*else if t1 > t2 then Snd_then_fst 
                                            else if t1 < t2 then Fst_then_snd
                                            else Either*)
  | (_, _, _), (_, _, _) -> (*if t1 > t2 then Snd_then_fst 
                              else if t1 < t2 then Fst_then_snd
                              else*) Either

(*let init_st = (0, false)
let mrdt_do s e =
  match e with
  | _, _, Enable -> (fst s + 1, true)
  |_, _, Disable -> (fst s, false)

let merge_flag l a b =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
  if af && bf then true
    else if not af && not bf then false
      else if af then ac - lc > 0
        else bc - lc > 0

let mrdt_merge (l:state) (a:state) (b:state) : state =
  (fst a + fst b - fst l, merge_flag l a b)

let rc e1 e2 =
  let _,_,o1 = e1 in let _,_,o2 = e2 in
  match o1, o2 with
  | Enable, Disable -> Snd_then_fst
  | Disable, Enable -> Fst_then_snd
  | _ -> Either

let init_st = 0 
let mrdt_do s _ = s + 1
let mrdt_merge l a b = a + b - l
let rc _ _ = Either*)

let verNo = ref 0
let ts = ref 1

(* generates unique version numbers *)
let gen_ver (r:repId) =
  let v = !verNo in 
  incr verNo;           
  (r, v)

(* generates increasing timestamps *)
let gen_ts _ =
  let t = !ts in
  incr ts; 
  t

(* Types of edges in the version graph *)
type edgeType = 
  | CreateBranch of repId * repId (* fork r2 from r1 *)
  | Apply of event (* apply op on the head version of r *)
  | Merge of repId * repId (* merge the head versions of r1 and r2 *)

module Event = struct
  type t = event
  let compare = compare
end
module EventSet = Set.Make(Event)

module Ver = struct
  type t = ver
  let compare = compare
end
module VerSet = Set.Make(Ver)

module Rep = struct
  type t = repId
  let compare = compare
end
module RepSet = Set.Make(Rep)

module EventPair = struct
  type t = event * event
  let compare = compare
end
module VisSet = Set.Make(EventPair)

(* edgeType in the version graph *)
type edge = { 
  src : ver;
  label : edgeType;
  dst : ver;
}

module Edge = struct
  type t = edge
  let compare = compare
end
module EdgeSet = Set.Make(Edge)

(* DAG *)
type dag = { 
  vertices : VerSet.t;   (* Set of vertices *)
  edges : edge list;  (* List of edges *)
}

(* Configuration type *)
type config = {
  r : RepSet.t;         (* Set of replicas *)
  n : ver -> state;   (* n maps versions to their states *)
  h : repId -> ver;   (* h maps replicas to their head version *)
  l : ver -> EventSet.t; (* l maps a version to the set of MRDT operations that led to this version *)
  g : dag;              (* g is a version graph whose vertices represent the v1ly active versions 
                           and whose edges represent relationship between different versions. *)
  vis : VisSet.t        (* vis is a partial order over events *)
}

let commutes_with (s:state) (e1:event) (e2:event) : bool =
  let r = Orset.equal (mrdt_do (mrdt_do s e1) e2) (mrdt_do (mrdt_do s e2) e1) in
  assert (if r = true then (if rc e1 e2 = Either then true else false) 
          else (if rc e1 e2 <> Either then true else false));
  r

(* Add an edge to the graph *)
(* assumption : source vertex is already present in the dag *)
let add_edge (g:dag) (src:ver) (label:edgeType) (dst:ver) : dag = {
  vertices = VerSet.add dst g.vertices;
  edges = {src; label; dst} :: g.edges;
}

(* Check if an edge exists between two vertices *)
let edge_exists (g:dag) (src:ver) (dst:ver) : bool =
  List.exists (fun e -> e.src = src && e.dst = dst) g.edges

(* Check is a vertex is present in the vertex set *)
let version_exists (vs:VerSet.t) (v:ver) : bool = 
  VerSet.mem v vs

let initR : RepSet.t = RepSet.singleton 0
let initN _ : state = init_st
let initH _ : ver = (0, 0)
let initL _ : EventSet.t = EventSet.empty
let initG : dag = { 
  vertices = VerSet.singleton (gen_ver 0); 
  edges = []
}
let initVis : VisSet.t = VisSet.empty

(* Initial configuration *)
let init_config = {r = initR; n = initN; h = initH; l = initL; g = initG; vis = initVis}

let debug_print fmt =
  if !debug_mode then Printf.printf fmt
  else Printf.ifprintf stdout fmt

(* CreateBranch function *)
let createBranch (c:config) (srcRid:repId) (dstRid:repId) : config =
  let newVer = gen_ver dstRid in
  if srcRid = dstRid then failwith "CreateBranch: Destination replica must be different from source replica";
  if version_exists c.g.vertices newVer then failwith "CreateBranch: New version already exists in the configuration";

  let srcVer = c.h srcRid in
  let newR = RepSet.add dstRid c.r in
  let newN = fun v -> if v = newVer then c.n srcVer else c.n v in
  let newH = fun r -> if r = dstRid then newVer else c.h r in
  let newL = fun v -> if v = newVer then c.l srcVer else c.l v in
  let newG = add_edge c.g srcVer (CreateBranch (srcRid, dstRid)) newVer in
  {r = newR; n = newN; h = newH; l = newL; g = newG; vis = c.vis}

(* Apply function *)
let apply (c:config) (srcRid:repId) (o:event) : config = 
  let newVer = gen_ver srcRid in
  if version_exists c.g.vertices newVer then failwith "Apply: New version already exists in the configuration";

  let srcVer = c.h srcRid in
  let newN = fun v -> if v = newVer then (mrdt_do (c.n srcVer) o) else c.n v in
  let newH = fun r -> if r = srcRid then newVer else c.h r in
  let newL = fun v -> if v = newVer then EventSet.add o (c.l srcVer) else c.l v in
  let newG = add_edge c.g srcVer (Apply o) newVer in
  let newVis = VisSet.fold (fun (o1,o2) acc -> VisSet.add (o1,o) (VisSet.add (o2,o) acc)) c.vis c.vis in
  {r = c.r; n = newN; h = newH; l = newL; g = newG; vis = newVis}

(* Check if path exists between v1 and v2 *)
let path_exists (e:edge list) (v1:ver) (v2:ver) : bool =
  let rec path_exists_aux (e:edge list) (visited:VerSet.t) (v1:ver) (v2:ver) : bool =
    if v1 = v2 then true
    else
      let visited = VerSet.add v1 visited in
      let neighbors = List.fold_left (fun acc e ->
        if e.src = v1 && not (VerSet.mem e.dst visited) then e.dst :: acc else acc) [] e in
      List.exists (fun n -> path_exists_aux e visited n v2) neighbors in
  path_exists_aux e VerSet.empty v1 v2

(* Find potential LCAs. ca is candidate LCAs set *)
let potential_lca (e:edge list) (v1:ver) (v2:ver) (ca:VerSet.t) : VerSet.t =
  
  (*Checks if a candidate LCA v' is not reachable to another version in ca *)
  let is_lca (v':ver) : bool = (* Ln 38 of the appendix *)
    VerSet.for_all (fun v -> 
      if v = v' then true 
      else not (path_exists e v v1 && path_exists e v v2 && path_exists e v' v)) ca in 

  VerSet.filter (fun v' -> path_exists e v' v1 && path_exists e v' v2 && is_lca v') ca

(* Find the ancestors of a given version *)
let rec find_ancestors (d:dag) (v:ver) : VerSet.t =
  if not (version_exists d.vertices v) then failwith "Version does not exist in the graph";
  List.fold_left (fun acc edge -> 
    if edge.dst = v then VerSet.union acc (VerSet.add edge.src (find_ancestors d edge.src))
    else acc) (VerSet.add v VerSet.empty) d.edges

let no_path_exists (vs:VerSet.t) (e:edge list) : bool =
  VerSet.for_all (fun v ->
    VerSet.for_all (fun v' ->
      if v = v' then true else not (path_exists e v v' || path_exists e v' v)) vs) vs
   
(* Find the LCA of two versions *)
let find_lca (c:config) (v1:ver) (v2:ver) : ver option =
  let a1 = find_ancestors c.g v1 in
  let a2 = find_ancestors c.g v2 in
  let ca = VerSet.inter a1 a2 in (* common ancestors *)
  let pa = potential_lca c.g.edges v1 v2 ca in (* potential LCAs *)
  assert (no_path_exists pa c.g.edges); (* checks if not path exists between any 2 distinct vertices in pa *)
  assert (VerSet.cardinal pa = 1); (* checks if there is only one LCA *)
  if VerSet.is_empty pa then None else Some (VerSet.choose pa) (* LCA *)

(* Merge function *)
let merge (c:config) (r1:repId) (r2:repId) : config =
  let newVer = gen_ver r1 in
  if version_exists c.g.vertices newVer then failwith "Merge: New version already exists in the configuration";

  let v1 = c.h r1 in let v2 = c.h r2 in
  let s1 = c.n v1 in let s2 = c.n v2 in
  let lca = find_lca c v1 v2 in
  match lca with
    | None -> failwith "lCA is not found"
    | Some vl -> let sl = c.n vl in  
                 (*debug_print "LCA is (%d,%b)\n" (fst sl) (snd sl); *)
                 let m = mrdt_merge sl s1 s2 in
  (*debug_print "merge of c.n(v(%d,%d)) = (%d,%b), c.n(v(%d,%d)) = (%d,%b), c.n(v(%d,%d)) = (%d,%b) is (%d,%b)\n" 
      (fst vl) (snd vl) (fst sl) (snd sl) 
      (fst v1) (snd v1) (fst s1) (snd s1) 
      (fst v2) (snd v2) (fst s2) (snd s2) 
      (fst m) (snd m);*)
  
  let newN = fun v -> if v = newVer then m else c.n v in
  let newH = fun r -> if r = r1 then newVer else c.h r in
  let newL = fun v -> if v = newVer then c.l v1 else c.l v in
  let newG = let e = add_edge c.g (c.h r1) (Merge (r1, r2)) newVer in
             add_edge e (c.h r2) (Merge (r1, r2)) newVer in
  {r = c.r; n = newN; h = newH; l = newL; g = newG; vis = c.vis}

let is_add o =
  match o with
  | Add _ -> true
  | _ -> false

let get_ele o : int =
  match o with
  | Add e -> e
  | Rem e -> e

let print_orset (s:state) =
  Orset.iter (fun (t,e) -> Printf.printf "(%d, %d)" t e) s

(* BEGIN of helper functions to print the graph *)
let string_of_event ((t, r, o):event) =
  Printf.sprintf "(%d, %d, (%s %d))" t r (if is_add o then "Add" else "Rem") (get_ele o)

let str_of_edge = function
  | CreateBranch (r1, r2) -> Printf.sprintf "Fork r%d from r%d" r2 r1
  | Apply e -> string_of_event e
  | Merge (r1, r2) -> Printf.sprintf "Merge r%d into r%d" r2 r1

let print_edge e = Printf.printf "v(%d,%d) --> [%s] --> v(%d,%d)\n" 
    (fst e.src) (snd e.src) (str_of_edge e.label) (fst e.dst) (snd e.dst)

(*let print_vertex (c:config) (v:ver) =
  let state = c.n v in
  Printf.printf "v(%d,%d) => state:(%d,%b)\n" (fst v) (snd v) (fst state) (snd state)*)

let print_dag (c:config) =
  Printf.printf "\nReplicas:\n";
  RepSet.iter (fun r -> Printf.printf "r%d\n" r) c.r;
  Printf.printf "\nVertices:\n";
  (*VerSet.iter (print_vertex c) c.g.vertices;*)
  Printf.printf "\nEdges:\n";
  List.iter print_edge (List.rev c.g.edges)

(* END of helper functions to print the graph *)

(* Get vertices set from edge list *)
let vertices_from_edges (el:edge list) : VerSet.t =
  List.fold_left (fun acc e -> VerSet.add e.src (VerSet.add e.dst acc)) VerSet.empty el

(*let rec collect_events (c:config) (v:ver) : EventSet.t =
  List.fold_left (fun acc edge ->
    if edge.dst = v then
      let src_events = collect_events(c) edge.src in
      EventSet.union src_events (c.l edge.src)
    else acc) (c.l v) c.g.edges*)

let is_visible (c:config) (e1:event) (e2:event) : bool =
  let edge1 = List.find (fun e -> e.label = Apply e1) c.g.edges in
  let edge2 = List.find (fun e -> e.label = Apply e2) c.g.edges in
  path_exists c.g.edges edge1.dst edge2.dst

let are_concurrent (c:config) (e1:event) (e2:event) : bool =
  not (is_visible c e1 e2 || is_visible c e2 e1)

(* Function to collect all Apply events from a dag *)
let collect_apply_events (d:dag) : event list =
  List.fold_left (fun acc edge ->
    match edge.label with
    | Apply e -> e :: acc
    | _ -> acc
  ) [] d.edges

let rec lo (c:config) (e1:event) (e2:event) : bool =
  let el = collect_apply_events c.g in
  if not (List.mem e1 el) || not (List.mem e2 el) then failwith "Event not in config";
  e1 <> e2 &&
  ((is_visible c e1 e2 && not (commutes_with init_st e1 e2)) ||

   (are_concurrent c e1 e2 && 
    (rc e1 e2 = Fst_then_snd && not (List.exists (fun e3 -> lo c e2 e3) el)) ||
    (rc e1 e2 = Snd_then_fst && not (List.exists (fun e3 -> lo c e1 e3) el)) (*||
    (rc e1 e2 = Either && get_ts e1 <= get_ts e2*)))
  
let linearize (c:config) (r:repId) : event list =
  let rec collect_events (v:ver) (acc:event list) (visited:VerSet.t) : (event list * VerSet.t) =
    if VerSet.mem v visited then acc, visited
    else
      let visited = VerSet.add v visited in
      let edges_to_v = List.filter (fun e -> e.dst = v) c.g.edges in
      let new_acc, visited =
        List.fold_left (fun (acc, visited) e ->
          let acc = 
            match e.label with
            | Apply e -> e :: acc
            | Merge (_, _) -> acc
            | CreateBranch (_, _) -> acc
          in
          collect_events e.src acc visited
        ) (acc, visited) edges_to_v
      in
      new_acc, visited
  in

  let event_list, _ = collect_events (c.h r) [] VerSet.empty in

  (* Sort events based on their visibility and the rc relation for concurrent events *)
    let sort_events (c:config) (event_list:event list) : event list =
    try
      List.sort (fun e1 e2 -> if lo c e1 e2 then -1 else 1) event_list
    with
    | e ->
      Printf.eprintf "Exception occurred during sorting: %s\n" (Printexc.to_string e);
      event_list in

  sort_events c event_list

let print_linearization (el:event list) =
  Printf.printf "\nLinearized Events:\n";
  List.iter (fun e -> Printf.printf "%s\n" (string_of_event e)) el

let apply_events el =
  let apply_events_aux (acc:state) (el:event list) : state =
    List.fold_left (fun acc e -> mrdt_do acc e) acc el in
  apply_events_aux init_st el
