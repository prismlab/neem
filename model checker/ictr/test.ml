
open Mrdt
(*open Mrdt_nofork_merge2sides*)

let rec explore_configs_nr (cl:config list) (nv:int) (acc:config list) (n:int) : (config list * int) =
  match cl with
  | [] -> (acc,n)
  | c1::cn ->
        if VerSet.cardinal c1.g.vertices = nv &&
          (let match_found =
            List.exists (fun c ->
              (let is_matching = 
                (get_rids c = get_rids c1 &&
                RepSet.for_all (fun r ->
                ev_eq (VerMap.find (RepIdMap.find r c1.h) c1.l)
                      (VerMap.find (RepIdMap.find r c.h) c.l)
                (*ev_eq (List.rev (VerMap.find (RepIdMap.find r c1.h) c1.l))
                      (List.rev (VerMap.find (RepIdMap.find r c.h) c.l))*)
                ) c1.r) in
                if is_matching then
                  debug_print "\nMatching configs c%d and c%d" c.i c1.i;
                is_matching)
            ) acc
          in
          not match_found)
      then explore_configs_nr cn nv (c1::acc) (n+1)
      else if VerSet.cardinal c1.g.vertices = nv then explore_configs_nr cn nv acc (n+1)
      else if VerSet.cardinal c1.g.vertices > nv then (explore_configs_nr cn nv acc n)
      else
        let new_f = 
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
          ) [] rids in

        let new_do = 
          List.fold_left (fun acc r1 ->
            let new_d = apply c1 r1 (gen_ts (), r1, Incr) in
            new_d::acc
          ) [] (get_rids c1) in

        let new_m = 
          let rids = get_rids c1 in
          List.fold_left (fun acc r1 ->
            List.fold_left (fun acc' r2 ->
              let new_m = merge c1 r1 r2 in
              new_m::acc'
            ) acc (List.filter (fun r2 -> r2 > r1) rids)
          ) [] rids in
        
        explore_configs_nr (new_f @ new_do @ new_m @ cn) nv acc n

let _ =
  let start_time = Unix.gettimeofday () in
  let nv = 8 in (* nv >= 1*) (* no. of versions *)
  try
    let (configs, n) = explore_configs_nr [init_config] nv [] 0 in
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    Printf.printf "\n\nNo. of possible executions: %d" n;
    Printf.printf "\nNo. of unique executions after reduction: %d" (List.length configs);
    Printf.printf "\n\nUnique exec after reduction:\n";
    List.iter (fun c -> Printf.printf "c%d, " c.i) configs;
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