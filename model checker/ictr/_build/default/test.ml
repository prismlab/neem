
open Mrdt
(*open Mrdt_nofork_merge2sides*)

let rec explore_configs_nr (cl:config list) (nv:int) (acc:config list) (n:int) : (config list * int) =
  match cl with
  | [] -> (acc,n)
  | c1::cn ->
      if VerSet.cardinal c1.g.vertices = nv then explore_configs_nr cn nv (c1::acc) (n+1)
      else if VerSet.cardinal c1.g.vertices > nv then (explore_configs_nr cn nv acc n)
      else
        let rids = List.rev c1.r in
        let new_f = 
          List.fold_left (fun acc r1 ->
              let new_f = createBranch c1 r1 (List.length rids) in 
              new_f::acc
          ) [] rids in

        let new_do = 
          List.fold_left (fun acc r1 ->
            let new_d = apply c1 r1 (gen_ts (), r1, Incr) in
            new_d::acc
          ) [] rids in

        let new_m = 
          List.fold_left (fun acc r1 ->
            List.fold_left (fun acc' r2 ->
              let new_m = merge c1 r1 r2 in
              new_m::acc'
            ) acc (List.filter (fun r2 -> r2 <> r1) rids)
          ) [] rids in
        
        explore_configs_nr (new_f @ new_do @ new_m @ cn) nv acc n

let _ =
  let start_time = Unix.gettimeofday () in
  let nv = 9 in (* nv >= 1*) (* no. of versions *)
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