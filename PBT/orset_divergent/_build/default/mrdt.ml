let debug_mode = ref false 

type repId = int (* unique replica ID *)

(* unique version number *)
type ver = repId * int (* replicaID, version number *)

type rc_res = (* conflict resolution type *)
  | Fst_then_snd
  | Snd_then_fst
  | Either

module Ts_ele_pair = struct
  type t = (int * char)
  let compare = compare
end
module Orset = Set.Make(Ts_ele_pair)

type state = Orset.t
type op = 
  | Add of char
  | Rem of char

(* event type *)
type event = int * repId * op (* timestamp, replicaID, operation *)
let get_ts ((t,_,_):event) = t
let init_st = Orset.empty
let mrdt_do s e =
  match e with
  | ts, _, Add e -> let s' = Orset.filter (fun (_,e1) -> e <> e1) s in 
                    Orset.add (ts, e) s'
  | _, _, Rem e -> Orset.filter (fun e1 -> snd e1 <> e) s

let mem_ele (ele:char) (s:state) =
  Orset.exists (fun (_,e) -> e = ele) s

let get_ts_st (ele:char) (s:state) =
  fst (Orset.find_first (fun (_,e) -> e = ele) s)

let mrdt_merge l a b =
  let i = Orset.inter l (Orset.inter a b) in
  let da = Orset.diff a l in
  let db = Orset.diff b l in
  let da1 = Orset.filter (fun (_,e) -> not (mem_ele e db)) da in
  let db1 = Orset.filter (fun (_,e) -> not (mem_ele e da)) db in
  let da2 = Orset.filter (fun (t,e) -> mem_ele e db && t > get_ts_st e b) da in
  let db2 = Orset.filter (fun (t,e) -> mem_ele e da && t > get_ts_st e a) db in
  Orset.union i (Orset.union da1 (Orset.union da2 (Orset.union db1 (Orset.union db2 Orset.empty))))

let rc e1 e2 =
  match e1, e2 with
  | (_, _, Add ele1), (_, _, Rem ele2) -> if ele1 = ele2 then Snd_then_fst else Either
  | (_, _, Rem ele1), (_, _, Add ele2) -> if ele1 = ele2 then Fst_then_snd else Either
  | (t1, _, Add ele1), (t2, _, Add ele2) -> if ele1 = ele2 then
                                              (if t1 > t2 then Snd_then_fst
                                              else if t2 > t1 then Fst_then_snd
                                              else Either)
                                            else Either
  | _ -> Either

let eq s1 s2 = Orset.equal s1 s2

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
  r : RepSet.t;         (* Set of active replicas *)
  n : ver -> state;   (* n maps versions to their states *)
  h : repId -> ver;   (* h maps replicas to their head version *)
  l : ver -> event list; (* l maps a version to the list of MRDT events that led to this version *)
  g : dag;              (* g is a version graph whose vertices represent the v1ly active versions 
                           and whose edges represent relationship between different versions. *)
  vis : VisSet.t        (* vis is a partial order over events *)
}

let commutes_with (s:state) (e1:event) (e2:event) : bool =
  let r = eq (mrdt_do (mrdt_do s e1) e2) (mrdt_do (mrdt_do s e2) e1) in
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
let initL _ : event list = []
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
  let newL = fun v -> if v = newVer then o::c.l srcVer else c.l v in
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

let can_reorder (e:event) (l:event list) : (int * bool) =
let rec can_reorder_aux (e:event) (l:event list) (acc:(int * bool)) : (int * bool) =
  match l with
  | [] -> acc
  | hd::tl -> if rc e hd = Fst_then_snd then (0, true)
              else if rc e hd = Snd_then_fst then (0, false)
              else can_reorder_aux e tl (fst (acc) + 1, snd acc) in
  can_reorder_aux e l (0, false)
              
let rec insert_at_index lst element index =
  match (lst, index) with
  | [], _ -> [element] 
  | _, 0 -> element::lst
  | hd::tl, n -> hd::insert_at_index tl element (n - 1)
 
let rec linearize (l1:event list) (l2:event list) : event list =
  match (l1, l2) with
  | [], [] -> []
  | [], _ -> l2
  | _, [] -> l1
  | e1::tl1, e2::tl2 -> if rc e1 e2 = Fst_then_snd then 
                          (let l2' = linearize l1 tl2 in if not (List.mem e2 l2') then e2::l2' else l2')
                        else if rc e1 e2 = Snd_then_fst then 
                          (let l1' = linearize tl1 l2 in if not (List.mem e1 l1') then e1::l1' else l1')
                        else 
                          (let (i,b) = can_reorder e1 l2 in
                            if b = true then 
                              (let l2' = linearize l1 (insert_at_index tl2 e2 (i-1)) in
                                if not (List.mem (List.nth l2 i) l2') then (List.nth l2 i)::l2' else l2')
                            else 
                            (let (i,b) = can_reorder e2 l1 in
                              if b = true then 
                                (let l1' = linearize (insert_at_index tl1 e1 (i-1)) l2 in
                                  if not (List.mem (List.nth l1 i) l1') then (List.nth l1 i)::l1' else l1')
                              else 
                                (let l2' = linearize tl1 l2 in
                                if not (List.mem e1 l2') then e1::l2' else l2')))
                       
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
                 let m = mrdt_merge sl s1 s2 in
  let newR = RepSet.add r1 (RepSet.add r2 c.r) in
  let newN = fun v -> if v = newVer then m else c.n v in
  let newH = fun r -> if r = r1 then newVer else c.h r in
  let newL = fun v -> if v = newVer then (linearize ( (c.l(c.h(r1)))) ( (c.l(c.h(r2))))) else c.l v in
  let newG = let e = add_edge c.g (c.h r1) (Merge (r1, r2)) newVer in
             add_edge e (c.h r2) (Merge (r1, r2)) newVer in
  {r = newR; n = newN; h = newH; l = newL; g = newG; vis = c.vis}

let is_add o =
  match o with
  | Add _ -> true
  | _ -> false

let get_ele o : char =
  match o with
  | Add e -> e
  | Rem e -> e

(* BEGIN of helper functions to print the graph *)
let print_st (s:state) =
  Printf.printf "{";
  Orset.iter (fun (t,e) -> Printf.printf "(%d,%c)" t e) s;
  Printf.printf "}"
  
let string_of_event ((t, r, o):event) =
  Printf.sprintf "(%d, %d, (%s %c))" t r (if is_add o then "Add" else "Rem") (get_ele o)

let str_of_edge = function
  | CreateBranch (r1, r2) -> Printf.sprintf "Fork r%d from r%d" r2 r1
  | Apply e -> string_of_event e
  | Merge (r1, r2) -> Printf.sprintf "Merge r%d into r%d" r2 r1

let print_edge e = Printf.printf "v(%d,%d) --> [%s] --> v(%d,%d)\n" 
    (fst e.src) (snd e.src) (str_of_edge e.label) (fst e.dst) (snd e.dst)

let print_vertex (c:config) (v:ver) =
  let st = c.n v in
  Printf.printf "\nv(%d,%d) => state:" (fst v) (snd v);
  print_st st

let print_dag (c:config) =
  Printf.printf "\nReplicas:\n";
  RepSet.iter (fun r -> Printf.printf "r%d\n" r) c.r;
  Printf.printf "\nVertices:\n";
  VerSet.iter (print_vertex c) c.g.vertices;
  Printf.printf "\nEdges:\n";
  List.iter print_edge (List.rev c.g.edges)

(* END of helper functions to print the graph *)

(* Get vertices set from edge list *)
let vertices_from_edges (el:edge list) : VerSet.t =
  List.fold_left (fun acc e -> VerSet.add e.src (VerSet.add e.dst acc)) VerSet.empty el

let print_linearization (el:event list) =
  Printf.printf "\nLinearized Events:\n";
  List.iter (fun e -> Printf.printf "%s\n" (string_of_event e)) el

let apply_events el =
  let apply_events_aux (acc:state) (el:event list) : state =
    List.fold_left (fun acc e -> mrdt_do acc e) acc el in
  apply_events_aux init_st el
