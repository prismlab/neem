let debug_mode = ref false

type state = int 
type op = Incr 
let init_st = 0 
let do_op s _ = s + 1
let merge l a b = a + b - l

type verNo = int (* version number *)
type repId = int (* replica ID *)

(* Types of edges in the version graph *)
type edgeType = 
  | CreateBranch of repId * repId
  | Apply of repId * op
  | Merge of repId * repId 

module Op = struct
  type t = op
  let compare = compare
end
module OpSet = Set.Make(Op)

module Ver = struct
  type t = verNo
  let compare = compare
end
module VerSet = Set.Make(Ver)

module Rep = struct
  type t = repId
  let compare = compare
end
module RepSet = Set.Make(Rep)

module OpPair = struct
  type t = op * op
  let compare = compare
end
module VisSet = Set.Make(OpPair)

(* edgeType in the version graph *)
type edge = { 
  src : verNo;
  label : edgeType;
  dst : verNo;
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
  n : verNo -> state;   (* n maps versions to their states *)
  h : repId -> verNo;   (* h maps replicas to their head version *)
  l : verNo -> OpSet.t; (* l maps a version to the set of MRDT operations that led to this version *)
  g : dag;              (* g is a version graph whose vertices represent the currently active versions 
                           and whose edges represent relationship between different versions. *)
  vis : VisSet.t        (* vis is a partial order over events *)
}

(* Add a vertex to the graph *)
let add_vertex (g:dag) (v:verNo) : dag = {
  vertices = VerSet.add v g.vertices;
  edges = g.edges
}

(* Add an edge to the graph *)
let add_edge (g:dag) (src:verNo) (label:edgeType) (dst:verNo) : dag = {
  vertices = VerSet.add src (VerSet.add dst g.vertices);
  edges = {src; label; dst} :: g.edges;
}

(* Check if an edge exists between two vertices *)
let edge_exists (g:dag) (src:verNo) (dst:verNo) : bool =
  List.exists (fun e -> e.src = src && e.dst = dst) g.edges

(* Check if an edge exists between two vertices *)
let version_exists (vs:VerSet.t) (v:verNo) : bool = 
  VerSet.mem v vs

let initR : RepSet.t = RepSet.singleton 0
let initN _ : state = init_st
let initH _ : verNo = 0
let initL _ : OpSet.t = OpSet.empty
let initG : dag = { 
  vertices = VerSet.singleton 0; 
  edges = []
}
let initVis : VisSet.t = VisSet.empty

(* Initial configuration *)
let init_config = {r = initR; n = initN; h = initH; l = initL; g = initG; vis = initVis }

let debug_print fmt =
  if !debug_mode then Printf.printf fmt
  else Printf.ifprintf stdout fmt

(* CreateBranch function *)
let createBranch (c:config) (srcRid:repId) (dstRid:repId) (newVer:verNo) : config =
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
let apply (c:config) (srcRid:repId) (newVer:verNo) (o:op) : config = 
  if version_exists c.g.vertices newVer then failwith "Apply: New version already exists in the configuration";

  let srcVer = c.h srcRid in
  let newN = fun v -> if v = newVer then (do_op (c.n srcVer) o) else c.n v in
  let newH = fun r -> if r = srcRid then newVer else c.h r in
  let newL = fun v -> if v = newVer then OpSet.add o (c.l srcVer) else c.l v in
  let newG = add_edge c.g srcVer (Apply (srcRid, o)) newVer in
  let newVis = VisSet.fold (fun (o1,o2) acc -> VisSet.add (o1,o) (VisSet.add (o2,o) acc)) c.vis c.vis in
  {r = c.r; n = newN; h = newH; l = newL; g = newG; vis = newVis}

  (* Find the ancestors of a given version *)
let rec find_ancestors (c:config) (v:verNo) : VerSet.t =
  if not (version_exists c.g.vertices v) then failwith "Version does not exist in the graph";
  List.fold_left (fun acc edge -> 
    if edge.dst = v then VerSet.union acc (VerSet.add edge.src (find_ancestors c edge.src))
    else acc) (VerSet.add v VerSet.empty) c.g.edges

(* Find the LCA of two versions *)
let find_lca (c:config) (v1:verNo) (v2:verNo) : verNo option =
  let a1 = VerSet.add v1 (find_ancestors c v1) in
  let a2 = VerSet.add v2 (find_ancestors c v2) in
  let ca = VerSet.inter a1 a2 in (* common ancestors *)
  if VerSet.is_empty ca then None else Some (VerSet.max_elt ca) (* LCA *)

(* Merge function *)
let merge (c:config) (r1:repId) (r2:repId) (newVer:verNo) : config =
  if version_exists c.g.vertices newVer then failwith "Merge: New version already exists in the configuration";

  let v1 = c.n (c.h r1) in
  let v2 = c.n (c.h r2) in
  let lca = find_lca c v1 v2 in
  let m = match lca with
    | None -> failwith "lCA is not found"
    | Some vl -> debug_print "LCA is %d\n" vl; let m = merge vl v1 v2 in
  debug_print "merge of %d %d %d is %d\n" vl v1 v2 m; m in
  
  let newN = fun v -> if v = newVer then m else c.n v in
  let newH = fun r -> if r = r1 then newVer else c.h r in
  let newL = fun v -> if v = newVer then c.l v1 else c.l v in
  let newG = let e = add_edge c.g v1 (Merge (r1, r2)) newVer in
             if r1 = r2 then e else add_edge e v2 (Merge (r1, r2)) newVer in
  {r = c.r; n = newN; h = newH; l = newL; g = newG; vis = c.vis}

(* BEGIN of helper functions to print the graph *)
let str_of_edge = function
  | CreateBranch (r1, r2) -> Printf.sprintf "Fork r%d from r%d" r2 r1
  | Apply (r, _) -> Printf.sprintf "Apply %s to r%d" "Incr" r
  | Merge (r1, r2) -> Printf.sprintf "Merge r%d into r%d" r2 r1

let print_edge e = Printf.printf "v%d --> [%s] --> v%d\n" e.src (str_of_edge e.label) e.dst

let print_vertex (c:config) (v:verNo) =
  let state = c.n v in
  Printf.printf "v%d => state:%d\n" v state

let print_dag (c:config) =
  Printf.printf "Replicas:\n";
  RepSet.iter (fun r -> Printf.printf "r%d\n" r) c.r;
  Printf.printf "\nVertices:\n";
  VerSet.iter (print_vertex c) c.g.vertices;
  Printf.printf "\nEdges:\n";
  List.iter print_edge (List.rev c.g.edges)

(* END of helper functions to print the graph *)

