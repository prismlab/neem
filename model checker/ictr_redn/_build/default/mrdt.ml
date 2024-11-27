let debug_mode = true
let debug_print fmt =
  if debug_mode then Printf.printf fmt
  else Printf.ifprintf stdout fmt

let nv = 3

(* unique replica ID *)
type repId = int 

(* unique version number *)
type ver = repId * int (* replicaID, version number *)

(* conflict resolution type *)
type rc_res = 
  | Fst_then_snd
  | Snd_then_fst
  | Either

type state = int

module RepSet = Set.Make (struct
  type t = repId
  let compare = compare
end)

type op = 
  | Incr

(* event type *)
type event = int * repId * op (* timestamp, replicaID, operation *)
let get_ts ((t,_,_):event) = t

let init_st = 0

let mrdt_do s _ = s + 1

let mrdt_merge (l:state) (a:state) (b:state) : state =
  a + b - l

let rc _ _ = Either

let eq s1 s2 = 
  s1 = s2

(*let verNo = ref 1*)
(* the entries grows as we increase |nv| *)
let verTbl = Hashtbl.create 10;;
Hashtbl.add verTbl 0 0

let tsTbl = Hashtbl.create 10
(*let ts = ref 1*)
let cid = ref 1

(* generates unique version numbers *)
(*let gen_ver (r:repId) =
  let v = !verNo in 
  incr verNo;           
  (r, v)*)

let gen_ver (r:repId) =
  let c = 
    match Hashtbl.find_opt verTbl r with
    | Some ctr -> ctr + 1
    | None -> 0
  in
  Hashtbl.replace verTbl r c;
  (r, c)

(* generates increasing timestamps *)
(*let gen_ts _ =
  let t = !ts in
  incr ts; 
  t*)

let gen_ts (r:repId) =
  let t = 
    match Hashtbl.find_opt tsTbl r with
    | Some ts -> ts + 1
    | None -> 1
  in
  Hashtbl.replace tsTbl r t;
  t

(* generates increasing config IDs*)
let gen_cid _ =
  let i = !cid in
  incr cid; 
  i

module VerSet = Set.Make (struct
  type t = ver
  let compare = compare
end)

module VisSet = Set.Make (struct
  type t = event * event
  let compare = compare
end)

module RepIdMap = Map.Make (struct
  type t = repId
  let compare = compare 
end)

module VerMap = Map.Make (struct
  type t = ver
  let compare = compare 
end)

module IntSet = Set.Make (struct
  type t = int
  let compare = compare
end)

module IntForkSet = Set.Make (struct
  type t = int * ver * int
  let compare = compare
end)

module IntMergeSet = Set.Make (struct
  type t = int * int * ver
  let compare = compare
end)

(* Types of edges in the version graph *)
type edgeType = 
  | CreateBranch of repId * ver * repId (* fork r2 from a version of r1  *)
  | Apply of event (* apply op on the head version of r *)
  | Merge of repId * repId * ver (* merge the a version v of r2 into r1 *)

(* edgeType in the version graph *)
type edge = { 
  src : ver;
  label : edgeType;
  dst : ver;
}

(* DAG *)
type dag = { 
  vertices : VerSet.t;   (* Set of active vertices *)
  edges : edge list;  (* List of edges *)
}

type tr = {
  f : IntForkSet.t;
  a : IntSet.t;
  m : IntMergeSet.t;
}

(* Configuration type *)
type config = {
  i : int;                 (* i is unique config ID *)
  r : int list;            (* r is a list of active replicas *)
  n : state VerMap.t;      (* n maps versions to their states *)
  h : ver RepIdMap.t;      (* h maps replicas to their head version *)
  v : ver list RepIdMap.t; (* v maps a replica to the list of versions generated at that replica *)
  l : event list VerMap.t; (* l maps a version to the list of MRDT events that led to this version *)
  g : dag;                 (* g is a version graph whose vertices represent the active versions 
                              and whose edges represent relationship between different versions. *)
  vis : VisSet.t;          (* vis is a partial order over events *)
  es : tr;                 (* es is the set of enabled transitions *)
  ss : tr                  (* ss is the sleep set *)
}

let commutes_with (s:state) (e1:event) (e2:event) : bool =
  let r = eq (mrdt_do (mrdt_do s e1) e2) (mrdt_do (mrdt_do s e2) e1) in
  assert (if r = true then (if rc e1 e2 = Either then true else false) 
          else (if rc e1 e2 <> Either then true else false));
  r

(* Add an edge to the graph *)
let add_edge (g:dag) (src:ver) (label:edgeType) (dst:ver) : dag = {
  vertices = VerSet.add src (VerSet.add dst g.vertices);
  edges = {src; label; dst}::g.edges;
}

let print_st (s:state) =
  debug_print "%d" s

let initI : int = 1
let initNs : int = 0
let initR : int list = [0]
let initN : state VerMap.t = VerMap.add (0,0) init_st VerMap.empty
let initH : ver RepIdMap.t = RepIdMap.add 0 (0,0) RepIdMap.empty
let initV : ver list RepIdMap.t = RepIdMap.add 0 [(0,0)] RepIdMap.empty
let initL : event list VerMap.t = VerMap.add (0,0) [] VerMap.empty
let initG : dag = { 
  vertices = VerSet.add (0,0) VerSet.empty;
  edges = []
}
let initVis : VisSet.t = VisSet.empty
let initEs : tr = {
  f = IntForkSet.add (0, (0,0), 1) IntForkSet.empty;
  a = IntSet.add 0 IntSet.empty;
  m = IntMergeSet.empty
}
let initSs : tr = {
  f = IntForkSet.empty;
  a = IntSet.empty;
  m = IntMergeSet.empty
}

(* Initial configuration *)
let init_config = {i = initI; r = initR; n = initN; h = initH; v = initV; l = initL; g = initG; vis = initVis; es = initEs; ss = initSs}

let apply_events el =
  let apply_events_aux (acc:state) (el:event list) : state =
    List.fold_right (fun e acc -> mrdt_do acc e) el acc in
  apply_events_aux init_st el

(* return value : (index, can_reorder) *)
let can_reorder (e:event) (l:event list) : (int * bool) =
  let rec can_reorder_aux (e:event) (l:event list) (acc:(int * bool)) : (int * bool) =
    match l with
    | [] -> acc
    | hd::tl -> if rc e hd = Fst_then_snd then (0, true)
                else if rc e hd = Snd_then_fst then (0, false)
                else 
                  begin match tl with
                  | [] -> can_reorder_aux e tl (fst acc + 1, snd acc)
                  | hd1::_ -> if commutes_with init_st hd hd1 then can_reorder_aux e tl (fst acc + 1, snd acc)
                              else (0, false)
                  end in
    can_reorder_aux e l (0, false)
              
let rec insert_at_index l ele i =
  match l, i with
  | [], _ -> [ele] 
  | _, 0 -> ele::l
  | hd::tl, n -> hd::insert_at_index tl ele (n - 1)

let rec get_prefix p lst =
  match lst with
  | [] -> []
  | x::xs -> if p x then x::get_prefix p xs else []

let find_reorder_ele e l : event option =
  List.find_opt (fun e' -> 
    rc e e' = Fst_then_snd &&
    let prefix = get_prefix ((<>) e') l in
    List.for_all (fun e'' -> commutes_with init_st e'' e') prefix
    ) l

let rec linearize (l1:event list) (l2:event list) : event list =
  match (l1, l2) with
  | [], [] -> []
  | [], _ -> l2
  | _, [] -> l1
  | e1::tl1, e2::tl2 -> let rc_cmp = rc e1 e2 in
                        if rc_cmp = Fst_then_snd then 
                          (let l2' = linearize l1 tl2 in 
                           if List.exists ((=) e2) l1 then l2' else e2 :: l2')
                        else if rc_cmp = Snd_then_fst then 
                          (let l1' = linearize tl1 l2 in 
                           if List.exists ((=) e1) l2 then l1' else e1 :: l1')
                        else 
                           match (find_reorder_ele e1 l2) with
                                | Some e2' -> e2'::linearize l1 (List.filter (fun e -> e <> e2') l2)
                                | None -> begin match (find_reorder_ele e2 l1) with
                                                  | Some e1' -> e1'::linearize (List.filter (fun e -> e <> e1') l1) l2
                                                  | None -> let l2' = linearize tl1 l2 in
                                                            if List.exists ((=) e1) l2 then l2' else e1 :: l2'
                                          end
                             
(* not needed as config has field r *)                                
(*let get_rids (c:config) : repId list =
  List.sort compare (List.map fst (RepIdMap.bindings c.h))*)
  
(* Check linearization for a replica r *)                                
let lin_check (r:int) (c:config) =
  if nv = VerSet.cardinal c.g.vertices then 
    let h = RepIdMap.find r c.h in
    let st = VerMap.find h c.n in
    let l = VerMap.find h c.l in
    debug_print "\n\nTesting config with nv=%d" (VerSet.cardinal c.g.vertices);
    debug_print "\n\n***Testing linearization for R%d" r;
    debug_print "\nLin result = ";
    print_st (apply_events l);
    debug_print "\nState = ";
    print_st st;
    eq (apply_events l) st
  else true

let rem_dup_lst lst =
  let rec rem_dup_aux seen lst =
    match lst with
    | [] -> List.rev seen 
    | hd :: tl ->
      if List.mem hd seen then rem_dup_aux seen tl 
      else rem_dup_aux (hd :: seen) tl 
  in
  rem_dup_aux [] lst

let rem_dup_set lst =
  IntSet.fold (fun x acc -> IntSet.add x acc) lst IntSet.empty
  
let read (r:repId) (c:config) =
  VerMap.find (RepIdMap.find r c.h) c.n

let sim (r:repId) (c:config) =
  List.length (VerMap.find (RepIdMap.find r c.h) c.l)
  
(* Check simulation relation *)
let sim_check (r:repId) (c:config) =
  let s = read r c in
  let abs = sim r c in
  debug_print "\n\nTesting config with nv=%d" (VerSet.cardinal c.g.vertices);
  debug_print "\n\n***Testing simulation relation for R%d" r;
  debug_print "\nAbs sim result = ";
  print_st (sim r c);
  debug_print "\nState = ";
  print_st (read r c);
  eq s abs  

(* BEGIN of helper functions to print the graph *)
let string_of_event ((t, r, _):event) =
  Printf.sprintf "(%d, r%d, %s)" t r "Incr"

let str_of_edge = function
| CreateBranch (r1, v1, r2) -> Printf.sprintf "Fork v(%d,%d) of r%d to r%d" (fst v1) (snd v1) r1 r2
| Apply e -> string_of_event e
| Merge (r1, r2, v2) -> Printf.sprintf "Merge v(%d,%d) of r%d into r%d" (fst v2) (snd v2) r2 r1

let print_edge e = 
  debug_print "\nv(%d,%d) --> [%s] --> v(%d,%d)" 
  (fst e.src) (snd e.src) (str_of_edge e.label) (fst e.dst) (snd e.dst)

(*let print_edge e = 
  debug_print " [%s]" 
  (str_of_edge e.label)*)

let print_vertex (c:config) (v:ver) =
  match VerMap.find_opt v c.n with
  | Some st ->
      debug_print "\nv(%d,%d) => state:" (fst v) (snd v);
      print_st st
  | None ->
      debug_print "\nv(%d,%d) => state: not found!" (fst v) (snd v)

let print_dag (c:config) =
  debug_print "\n\nConfig ID:c%d" c.i;
  debug_print "\n\nReplicas:\n";
  List.iter (fun r -> debug_print "r%d\n" r) c.r;
  debug_print "\nVertices:";
  VerSet.iter (print_vertex c) c.g.vertices;
  debug_print "\n\nEdges:";
  List.iter print_edge (List.rev c.g.edges)

(* END of helper functions to print the graph *)

(* CreateBranch function *)
let createBranch (c:config) (srcRid:repId) (srcVer:ver) (dstRid:repId) : config =
  let newVer = gen_ver dstRid in
  if srcRid = dstRid then failwith "CreateBranch: Destination replica must be different from source replica";
  if List.mem dstRid c.r then failwith (Printf.sprintf "CreateBranch: Destination replica (r%d) is already forked" dstRid);
  if VerSet.mem newVer c.g.vertices then failwith "CreateBranch: New version already exists in the configuration";

  (*let srcVer = RepIdMap.find srcRid c.h in*)
  let newI = gen_cid () in
  let newR = dstRid::c.r in
  let newN = VerMap.add newVer (VerMap.find srcVer c.n) c.n in
  let newH = RepIdMap.add dstRid newVer c.h in
  let newV = RepIdMap.add dstRid [newVer] c.v in
  let newL = VerMap.add newVer (VerMap.find srcVer c.l) c.l in
  let newG = add_edge c.g srcVer (CreateBranch (srcRid, srcVer, dstRid)) newVer in
  let newEs = {
    f = List.fold_left (fun acc x -> 
          List.fold_right (fun v acc' ->
            IntForkSet.add (x, v, List.length newR) acc'
          ) (RepIdMap.find x newV) acc
        ) IntForkSet.empty newR;
    a = IntSet.of_list newR;
    m = List.fold_left (fun acc x ->
          List.fold_left (fun acc' y -> 
            List.fold_right (fun v acc'' ->
              if x <> y then IntMergeSet.add (x, y, v) acc'' else acc''
            ) (RepIdMap.find y newV) acc'
          ) acc newR
        ) IntMergeSet.empty newR
  } in
  let newSs = {
    f = c.ss.f; (*IntPairSet.filter (fun (i,j) -> i < srcRid || (i = srcRid && j < dstRid)) c.es.f;*)
    a = IntSet.filter (fun i -> i < srcRid && i <> dstRid) c.es.a;
    m = IntMergeSet.filter (fun (i,j,_) -> i < srcRid || (i = srcRid && j < dstRid)) c.es.m
  } in
  let new_c = {i = newI; r = newR; n = newN; h = newH; v = newV; l = newL; g = newG; vis = c.vis; es = newEs; ss = newSs} in
  print_dag new_c;
  (*debug_print "\nLinearization check for createBranch started.";*)
  assert (lin_check dstRid new_c);
  (*assert (not (tr_eq new_c.es new_c.ss));*)
  (*debug_print "\nLinearization check for createBranch successful.";*)
  debug_print "\n******************************************";
  new_c

(* Apply function *)
let apply (c:config) (srcRid:repId) (o:event) : config = 
  let newVer = gen_ver srcRid in
  if VerSet.mem newVer c.g.vertices then failwith "Apply: New version already exists in the configuration";

  let srcVer = RepIdMap.find srcRid c.h in
  let newI = gen_cid () in
  (*let newR = srcRid::c.r in*)
  let newN = VerMap.add newVer (mrdt_do (VerMap.find srcVer c.n) o) c.n in
  let newH = RepIdMap.add srcRid newVer c.h in
  let newV = RepIdMap.add srcRid (newVer::RepIdMap.find srcRid c.v) c.v in
  let newL = VerMap.add newVer (o::VerMap.find srcVer c.l) c.l in
  let newG = add_edge c.g srcVer (Apply o) newVer in
  let newVis = List.fold_left (fun acc o1 -> VisSet.add (o1,o) acc) c.vis (VerMap.find srcVer c.l) in
  let newEs = {
    f = List.fold_left (fun acc x -> IntForkSet.add (x, RepIdMap.find x newH, List.length c.r) acc) IntForkSet.empty c.r;
    a = IntSet.of_list c.r;
    m = List.fold_left (fun acc x ->
          List.fold_left (fun acc' y -> if x <> y then IntMergeSet.add (x, y, RepIdMap.find y newH) acc' else acc'
          ) acc c.r
        ) IntMergeSet.empty c.r
  } in
  let newSs = {
    f = IntForkSet.filter (fun (i,_,_) -> i < srcRid) c.es.f;
    a = IntSet.filter (fun i -> i < srcRid) c.es.a;
    m = IntMergeSet.filter (fun (i,j,_) -> i < srcRid && srcRid <> j) c.es.m;
  } in
  let new_c = {i = newI; r = c.r; n = newN; h = newH; v = newV; l = newL; g = newG; vis = newVis; es = newEs; ss = newSs} in
  print_dag new_c;
  (*debug_print "\nLinearization check for apply started...";*)
  assert (lin_check srcRid new_c); 
  (*assert (not (tr_eq new_c.es new_c.ss));*)
  (*assert (sim_check srcRid new_c);*)
  (*debug_print "\nLinearization check for apply successful.";*)
  debug_print "\n******************************************";
  new_c

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
  let is_lca (v:ver) : bool = (* Ln 38 of the appendix *)
    not (VerSet.exists (fun v' -> path_exists e v' v1 && path_exists e v' v2 && path_exists e v v') (VerSet.remove v ca)) in
  
    VerSet.filter (fun v' -> path_exists e v' v1 && path_exists e v' v2 && is_lca v') ca

(* Find the ancestors of a given version *)
let rec find_ancestors (d:dag) (v:ver) : VerSet.t =
  (*if not (version_exists d.vertices v) then failwith "Version does not exist in the graph";*)
  List.fold_left (fun acc edge -> 
    if edge.dst = v then VerSet.union acc (VerSet.add edge.src (find_ancestors d edge.src))
    else acc) (VerSet.empty) d.edges

let no_path_exists (vs:VerSet.t) (e:edge list) : bool =
  VerSet.for_all (fun v ->
    VerSet.for_all (fun v' ->
      if v = v' then true else not (path_exists e v v' || path_exists e v' v)) vs) vs
    
let rec recursive_merge (c:config) (pa:VerSet.t) : (VerSet.t * config) =
  if VerSet.cardinal pa = 1 then (pa, c)
  else 
    let v1 = VerSet.choose pa in
    let v2 = VerSet.choose (VerSet.remove v1 pa) in
    let r1 = fst v1 in let r2 = fst v2 in
    match List.find_opt (fun e1 -> 
        e1.src = v1 &&
        List.exists (fun e2 ->
          e2.src = v2 && e2.dst = e1.dst && e1.label = Merge (r1, r2, v2) && e2.label = Merge (r1, r2, v2)) 
        c.g.edges
      ) c.g.edges with
      | Some e1 ->
          let newVer = e1.dst in
          let new_pa = VerSet.add newVer (VerSet.remove v1 (VerSet.remove v2 pa)) in
          recursive_merge c new_pa
      | None -> 
          (let s1 = VerMap.find v1 c.n in let s2 = VerMap.find v2 c.n in
          let newVer = gen_ver (fst v1) in
          let (lca, _) = find_lca c v1 v2 in
          match lca with
          | None -> failwith "LCA not found"
          | Some vl -> 
            let sl = VerMap.find vl c.n in
            let m = mrdt_merge sl s1 s2 in
            let newN = VerMap.add newVer m (VerMap.add vl sl c.n) in
            let newH = RepIdMap.add (fst v1) newVer c.h in
            let newL = c.l in (* didn't change linearization *)
            let newG = let e = add_edge c.g (RepIdMap.find r1 c.h) (Merge (r1, r2, v2)) newVer in
                      add_edge e (RepIdMap.find r2 c.h) (Merge (r1, r2, v2)) newVer in
            let new_config = {c with n = newN; h = newH; l = newL; g = newG} in
            let new_pa = VerSet.add newVer (VerSet.remove v1 (VerSet.remove v2 pa)) in
            recursive_merge new_config new_pa)

(* Find LCA function *)
and find_lca (c:config) (v1:ver) (v2:ver) : (ver option * config) =
  let a1 = VerSet.add v1 (find_ancestors c.g v1) in
  debug_print "\nAncestors of (%d,%d) are:" (fst v1) (snd v1);
  VerSet.iter (fun v -> debug_print "(%d,%d)" (fst v) (snd v)) a1; 
  let a2 = VerSet.add v2 (find_ancestors c.g v2) in
  debug_print "\nAncestors of (%d,%d) are:" (fst v2) (snd v2);
  VerSet.iter (fun v -> debug_print "(%d,%d)" (fst v) (snd v)) a2; 
  let ca = VerSet.inter a1 a2 in (* common ancestors *)
  let pa = potential_lca c.g.edges v1 v2 ca in (* potential LCAs *)
  if VerSet.is_empty pa then (None, c) 
  else 
    (debug_print "\nPotential LCAs of (%d,%d) and (%d,%d) are:" (fst v1) (snd v1) (fst v2) (snd v2);
    VerSet.iter (fun v -> debug_print "(%d,%d)" (fst v) (snd v)) pa; 
    assert (no_path_exists pa c.g.edges); (* checks if not path exists between any 2 distinct vertices in pa *)
    let lca_set, new_config = recursive_merge c pa in
    assert (VerSet.cardinal lca_set = 1); (* checks if there is only one LCA *)
    debug_print "\nActual LCAs of (%d,%d) and (%d,%d) is (%d,%d):" (fst v1) (snd v1) (fst v2) (snd v2)
            (fst (VerSet.choose lca_set)) (snd (VerSet.choose lca_set));
    (Some (VerSet.choose lca_set), new_config))

(* Merge function *)
let merge (c:config) (r1:repId) (r2:repId) (v2:ver) : config =
  let newVer = gen_ver r1 in
  if VerSet.mem newVer c.g.vertices then failwith "Merge: New version already exists in the configuration";

  let v1 = RepIdMap.find r1 c.h in 
  (*let v2 = RepIdMap.find r2 c.h in *)
  let s1 = VerMap.find v1 c.n in 
  let s2 = VerMap.find v2 c.n in 
  let lca_v, new_config = find_lca c v1 v2 in
  match lca_v with
    | None -> failwith "LCA is not found"
    | Some vl -> let sl = VerMap.find vl new_config.n in  
                 let m = mrdt_merge sl s1 s2 in
  let newI = gen_cid () in
  (*let newR = RepSet.add r1 (RepSet.add r2 c.r) in*)
  let newN = VerMap.add newVer m c.n in
  let newH = RepIdMap.add r1 newVer c.h in
  let newV = RepIdMap.add r1 (newVer::RepIdMap.find r1 c.v) c.v in
  let newL = VerMap.add newVer (linearize (VerMap.find (RepIdMap.find r1 c.h) c.l) (VerMap.find v2 c.l)) c.l in
  let newG = let e = add_edge c.g (RepIdMap.find r1 c.h) (Merge (r1, r2, v2)) newVer in
              add_edge e v2 (Merge (r1, r2, v2)) newVer in
  let newEs = {
    f = List.fold_left (fun acc x -> 
          List.fold_right (fun v acc' -> 
            IntForkSet.add (x, v, List.length c.r) acc'
          ) (RepIdMap.find x newV) acc
        ) IntForkSet.empty c.r;
    a = IntSet.of_list c.r;
    m = List.fold_left (fun acc x ->
          List.fold_left (fun acc' y -> 
            List.fold_right (fun v acc'' -> 
              if x <> y then IntMergeSet.add (x, y, v) acc'' else acc''
            ) (RepIdMap.find y newV) acc'
          ) acc c.r
        ) IntMergeSet.empty c.r
  } in
  let newSs = {
    f = IntForkSet.filter (fun (i,_,j) -> i < r1 && j <> r2) c.es.f;
    a = IntSet.filter (fun i -> i < r1) c.es.a;
    m = IntMergeSet.filter (fun (i,j,_) -> i < r1 && j = r2) c.es.m
  } in
  let new_c = {i = newI; r = c.r; n = newN; h = newH; v = newV; l = newL; g = newG; vis = c.vis; es = newEs; ss = newSs} in
  print_dag new_c;
  debug_print "\n****Head after merge of r%d and r%d is (%d,%d) " r1 r2 (fst newVer) (snd newVer);
  (*debug_print "\nLinearization check for merge started.";*)
  assert (lin_check r1 new_c);
  (*assert (not (tr_eq new_c.es new_c.ss));*)
  (*assert (sim_check r1 new_c);*)
  (*debug_print "\nLinearization check for merge successful.";*)
  debug_print "\n******************************************";
  new_c

(* Get vertices set from edge list *)
let vertices_from_edges (el:edge list) : VerSet.t =
  List.fold_left (fun acc e -> VerSet.add e.src (VerSet.add e.dst acc)) VerSet.empty el

let print_linearization (el:event list) =
  debug_print "\nLinearized Events:\n";
  List.iter (fun e -> debug_print "%s\n" (string_of_event e)) el