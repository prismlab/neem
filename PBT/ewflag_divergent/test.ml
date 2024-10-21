
open Mrdt

let rec explore_configs_nr (cl:config list) (nv:int) (acc:config list) : config list =
  match cl with
  | [] -> acc
  | c1::cn ->
      if VerSet.cardinal c1.g.vertices = nv then explore_configs_nr cn nv (c1::acc)
      else if VerSet.cardinal c1.g.vertices > nv then explore_configs_nr cn nv acc
      else
        let new_c0 = 
          List.fold_left (fun acc i ->
            List.fold_left (fun inner_acc j ->
              let new_f = createBranch c1 i j in
              new_f::inner_acc
            ) acc (List.filter (fun rid -> rid <> i && not (List.mem rid (get_rids c1)) && rid - i = 1) (List.init nv (fun i -> i)))
          ) [] (get_rids c1) in

        let new_cl = 
          List.fold_left (fun acc r1 ->
            let new_e = apply c1 r1 (gen_ts (), r1, Enable) in
            let new_d = apply c1 r1 (gen_ts (), r1, Disable) in
            new_e::new_d::acc
          ) [] (get_rids c1) in

        let new_cl1 = 
          List.fold_left (fun acc i ->
            List.fold_left (fun inner_acc j ->
              let new_m = merge c1 i j in
              new_m::inner_acc
            ) acc (List.filter (fun rid -> rid <> i && rid > i) (get_rids c1))
          ) [] (get_rids c1) in
        
        explore_configs_nr (new_c0@((new_cl@new_cl1@cn))) nv acc

let _ =
  let start_time = Unix.gettimeofday () in
  let nv = 8 in (* nv >= 1*) (* no. of versions *)
  try
    let configs =
      if nv = 1 then [init_config]
      else (debug_print "\nexploring started"; explore_configs_nr [init_config] nv []) in
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    Printf.printf "\n\nLength of config list: %d" (List.length configs);
    Printf.printf "\nTotal execution time: %.6f seconds\n" total_time
  with
  | exn ->
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    Printf.printf "\nException caught. Total execution time: %.6f seconds\n" total_time;
    raise exn