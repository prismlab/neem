
open Mrdt
(*open Mrdt_nofork_merge2sides*)

let rec explore_configs_nr (cl:config list) (nv:int) (n:int) : int =
  match cl with
  | [] -> n
  | c1::cn ->
      if VerSet.cardinal c1.g.vertices = nv then explore_configs_nr cn nv (n+1)
      else if VerSet.cardinal c1.g.vertices > nv then (explore_configs_nr cn nv n)
      else
        let rids = c1.r in
        let nr = List.length c1.r in
        let new_f = 
          List.fold_right (fun r1 acc ->
            List.fold_right (fun v1 acc' ->
              let new_f = createBranch c1 r1 v1 nr in 
              new_f::acc'
            ) (RepIdMap.find r1 c1.v) acc
          ) rids [] in

        let new_do = 
          List.fold_right (fun r1 acc ->
            let new_d = apply c1 r1 (gen_ts r1, r1, Incr) in
            new_d::acc
          ) rids [] in

        let new_m = 
          List.fold_right (fun r1 acc ->
            List.fold_right (fun r2 acc' ->
              List.fold_right (fun v2 acc'' -> 
              if r1 = r2 then acc''
              else 
                let new_m = merge c1 r1 r2 v2 in
                new_m::acc'
              ) (RepIdMap.find r2 c1.v) acc'
            ) rids acc
          ) rids [] in
        
        explore_configs_nr (new_f @ new_do @ new_m @ cn) nv n

let _ =
  let start_time = Unix.gettimeofday () in
  try
    let n = explore_configs_nr [init_config] nv 0 in
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    Printf.printf "\n\nNo. of possible executions: %d" n;
    (*Printf.printf "\nNo. of unique executions after reduction: %d" (List.length configs);*)
    (*Printf.printf "\n\nUnique exec after reduction:\n";
    List.iter (fun c -> Printf.printf "c%d, " c.i) configs;*)
    Printf.printf "\n\nTotal execution time: %.6f seconds\n" total_time
  with
  | exn ->
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    Printf.printf "\nException caught. Total execution time: %.6f seconds\n" total_time;
    raise exn


(*open Mrdt_nofork_merge2sides

let rec explore_configs_nr (cl:config list) (nv:int) (acc:config list) : config list =
  match cl with
  | [] -> acc
  | c1::cn ->
      if VerSet.cardinal c1.g.vertices = nv then explore_configs_nr cn nv (c1::acc)
      else if VerSet.cardinal c1.g.vertices > nv then explore_configs_nr cn nv acc
      else
        (*let new_f = 
          let rids = get_rids c1 in
          List.fold_left (fun acc r1 ->
            List.fold_left (fun acc' r2 ->
              let new_f = createBranch c1 r1 r2 in 
              new_f::acc'
            ) acc (List.filter (fun r2 -> 
                    (*rid <> i &&*) not (List.mem r2 rids) && 
                    (List.for_all (fun r2 -> 
                      List.mem r2 rids
                    ) (List.init r2 (fun i -> i))) (*&& rid - i = 1*)
                  ) (List.init nv (fun i -> i)))
          ) [] rids in*)

        let rids = RepSet.elements c1.r in
        let new_do = 
          List.fold_left (fun acc r1 ->
            let new_d = apply c1 r1 (gen_ts (), r1, Incr) in
            new_d::acc
          ) [] rids in

        let rids = List.init nv (fun i -> i) in
        let new_m = 
          List.fold_left (fun acc r1 ->
            List.fold_left (fun acc' r2 ->
              let new_m = merge c1 r1 r2 in
              new_m::acc'
            ) acc (List.filter (fun r2 -> r1 <> r2) rids)
          ) [] rids in
      
        explore_configs_nr (new_do @ new_m @ cn) nv acc

let _ =
  let start_time = Unix.gettimeofday () in
  let nv = 5 in (* nv >= 1*) (* no. of versions *)
  try
    let configs = explore_configs_nr [init_config] nv [] in
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    Printf.printf "\n\nLength of config list: %d" (List.length configs);
    Printf.printf "\nTotal execution time: %.6f seconds\n" total_time
  with
  | exn ->
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    Printf.printf "\nException caught. Total execution time: %.6f seconds\n" total_time;
    raise exn*)