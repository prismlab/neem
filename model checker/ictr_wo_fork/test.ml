
open Mrdt
(*open Mrdt_nofork_merge2sides*)

let c = init_config;;
let c1 = apply c 4 (gen_ts (), 4, Incr) in
let c2 = apply c1 3 (gen_ts (), 3, Incr) in
let c3 = apply c2 2 (gen_ts (), 2, Incr) in
let c4 = apply c3 1 (gen_ts (), 1, Incr) in 
let c5 = merge c4 4 3 in
let c6 = merge c5 4 2 in
let c7 = merge c6 4 1 in
let c8 = merge c7 1 2 in
let c9 = merge c8 1 3 in
merge c9 1 4 

(*let rec explore_configs_nr (cl:config list) (ns:int) (acc:config list) (acc':config list) (n:int) : (config list * config list * int) =
  match cl with
  | [] -> (acc,[],n)
  | c1::cn ->
        if c1.ns = ns then
          let new_c1 = (RepSet.fold (fun r acc_c -> merge acc_c 1 r) (RepSet.remove 1 c1.r) c1) in 
          let match_found =
            List.exists (fun new_c ->
              let is_matching = 
                ev_eq (List.rev (new_c1.l (new_c1.h 1)))
                      (List.rev (new_c.l (new_c.h 1))) in
                if is_matching then
                  debug_print "\nMatching configs c%d and c%d" new_c.i c1.i;
                is_matching
            ) acc'
          in
          if not match_found then explore_configs_nr cn ns (c1::acc) (new_c1::acc') (n+1)
          else explore_configs_nr cn ns acc (new_c1::acc') (n+1)
      else if c1.ns > ns then (explore_configs_nr cn ns acc acc' n)
      else
        let rids = (List.filter (fun r -> r <> 0)) (List.init (ns+1) (fun i -> i)) in
        let new_do = 
          List.fold_left (fun acc r1 ->
            let new_i = apply c1 r1 (gen_ts (), r1, Incr) in
            new_i::acc
          ) [] rids in

        let new_m = 
          RepSet.fold (fun r1 acc ->
            RepSet.fold (fun r2 acc' ->
              let new_m = merge c1 r1 r2 in
              new_m::acc'
            ) (RepSet.remove r1 c1.r) acc (*List.filter (fun r2 -> r2 <> r1) (List.init (ns+1) (fun i -> i))*)
          ) c1.r [] (*List.init (ns+1) (fun i -> i)*) in
        
        explore_configs_nr (new_do @ new_m @ cn) ns acc acc' n

let _ =
  let start_time = Unix.gettimeofday () in
  let ns = 7 in (* nv >= 1*) (* no. of versions *)
  try
    let (configs, _, n) = explore_configs_nr [init_config] ns [] [] 0 in
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
    raise exn*)


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