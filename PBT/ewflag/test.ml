open OUnit2
open Mrdt

let max_rep = 4 (* for generating 3 replicas *)

let gen_op = QCheck.Gen.oneof [
  QCheck.Gen.return Enable;
  QCheck.Gen.return Disable;
]

let gen_rep = QCheck.Gen.int_range 0 max_rep

let rec gen_diff_id id =
  let new_id = QCheck.Gen.generate1 gen_rep in
  if new_id = id then gen_diff_id id else new_id

let gen_test_config () =
  let ridc1 = QCheck.Gen.generate1 gen_rep in
  let ridc2 = gen_diff_id ridc1 in
  debug_print "\nCB r%d to r%d" ridc1 ridc2;
  let c1 = createBranch init_config ridc1 ridc2 in

  let rid1 = QCheck.Gen.generate1 gen_rep in
  let op1 = QCheck.Gen.generate1 gen_op in
  debug_print "\nAPPLY r%d %s" rid1 (if is_enable op1 then "Enable" else "Disable");
  let c2 = apply c1 rid1 (gen_ts (), rid1, op1) in

  let ridm1 = QCheck.Gen.generate1 gen_rep in
  let ridm2 = QCheck.Gen.generate1 gen_rep in
  debug_print "\nMERGE r%d r%d" ridm1 ridm2;
  let c3 = merge c2 ridm1 ridm2 in 

  let rid2 = QCheck.Gen.generate1 gen_rep in
  let op2 = QCheck.Gen.generate1 gen_op in
  debug_print "\nAPPLY r%d %s" rid2 (if is_enable op2 then "Enable" else "Disable");
  let c4 = apply c3 rid2 (gen_ts (), rid2, op2) in

  let rid3 = QCheck.Gen.generate1 gen_rep in
  let op3 = QCheck.Gen.generate1 gen_op in
  debug_print "\nAPPLY r%d %s" rid3 (if is_enable op3 then "Enable" else "Disable");
  let c6 = apply c4 rid3 (gen_ts (), rid3, op3) in

  let rid4 = QCheck.Gen.generate1 gen_rep in
  let op4 = QCheck.Gen.generate1 gen_op in
  debug_print "\nAPPLY r%d %s" rid4 (if is_enable op4 then "Enable" else "Disable");
  let c7 = apply c6 rid4 (gen_ts (), rid4, op4) in
  
  let ridm3 = QCheck.Gen.generate1 gen_rep in
  let ridm4 = QCheck.Gen.generate1 gen_rep in
  debug_print "\nMERGE r%d r%d" ridm3 ridm4;
  let c8 = merge c7 ridm3 ridm4 in

  let ridm5 = QCheck.Gen.generate1 gen_rep in
  let ridm6 = QCheck.Gen.generate1 gen_rep in
  debug_print "\nMERGE r%d r%d" ridm5 ridm6;
  let c10 = merge c8 ridm5 ridm6 in 
  
  let ridm7 = QCheck.Gen.generate1 gen_rep in
  let ridm8 = QCheck.Gen.generate1 gen_rep in
  debug_print "\nMERGE r%d r%d" ridm7 ridm8;
  let c11 = merge c10 ridm7 ridm8 in 
  c11
 
let sanity_check (c:config) = 
  assert (VerSet.equal c.g.vertices (vertices_from_edges c.g.edges))

let create_tc (r:repId) (c:config) =
  Printf.printf "\n\nTesting linearization for R%d" r;
  print_linearization (List.rev (c.l(c.h(r))));
  Printf.printf "Lin result = ";
  print_st (apply_events (List.rev (c.l(c.h(r)))));
  Printf.printf "\nState = ";
  print_st (c.n (c.h r));
  assert (eq (apply_events (List.rev (c.l(c.h(r))))) (c.n (c.h r)))

let gen_tc (c:config) : unit =
  RepSet.iter (fun r -> create_tc r c) c.r
  
let run_tests_multiple_times n =
  for i = 1 to n do
    Printf.printf "\n\n********** Test run %d **********\n" i;
    let test_config = gen_test_config () in
    let tests = "Test suite for MRDT" >::: [
      "sanity_check" >:: (fun _ -> sanity_check test_config);
      "print_dag" >:: (fun _ -> print_dag test_config);
      "test_lin" >:: (fun _ -> gen_tc test_config);
    ] in
    run_test_tt_main tests
  done

let _ =
let start_time = Unix.gettimeofday () in
run_tests_multiple_times 1;
let end_time = Unix.gettimeofday () in
let total_time = end_time -. start_time in
Printf.printf "Total execution time: %.6f seconds\n" total_time

let rec explore_configs (cl:config list) (nr:int) (nv:int) (acc:config list): config list =
  if (List.for_all (fun c -> (VerSet.cardinal c.g.vertices = nv)) cl) then (cl @ acc)
  else
    match cl with
    | [] -> acc
    | c1::cn -> 
        if VerSet.cardinal c1.g.vertices = nv then 
          (Printf.printf "\nDONE!!"; explore_configs cn nr nv (c1::acc))
        else if VerSet.cardinal c1.g.vertices > nv then explore_configs cn nr nv acc
        else 
          let r1 = QCheck.Gen.generate1 (QCheck.Gen.int_range 0 nr) in
          let op = QCheck.Gen.generate1 gen_op in
          debug_print "\nAPPLY** r%d %s" r1 (if op = Enable then "Enable" else "Disable");
          let new_c0 = apply c1 r1 (gen_ts (), r1, op) in
          if VerSet.cardinal new_c0.g.vertices = nv then 
            (Printf.printf "\nDONE!!"; explore_configs cn nr nv (new_c0::acc))
          else
            (let mr1 = QCheck.Gen.generate1 (QCheck.Gen.int_range 0 nr) in
            let mr2 = gen_diff_id mr1 in
            debug_print "\nMERGE** r%d r%d" mr1 mr2;
            let new_c1 = merge c1 mr1 mr2 in
            if VerSet.cardinal new_c1.g.vertices = nv then 
              (Printf.printf "\nDONE!!"; explore_configs (new_c0::cn) nr nv (new_c1::acc))
            else 
              (*let mr1 = QCheck.Gen.generate1 (QCheck.Gen.int_range 0 nr) in
              let mr2 = QCheck.Gen.generate1 (QCheck.Gen.int_range 0 nr) in
              debug_print "\nMERGE** r%d r%d" mr1 mr2;*)
              let new_c2 = merge new_c0 mr1 mr2 in 
              if VerSet.cardinal new_c2.g.vertices = nv then 
                (Printf.printf "\nDONE!!"; explore_configs (new_c0::new_c1::cn) nr nv (new_c2::acc))
              else 
                explore_configs (new_c0::new_c1::new_c2::cn) nr nv acc)

let nr = 2 (* Example: number of replicas [0;1;2]*)    

let run_tests_for_config c =
  print_dag c;
    for i = 0 to nr do
      Printf.printf "\n\n***Testing linearization for R%d" i;
      Printf.printf "\nNo. of vertices at R%d: %d" i (VerSet.cardinal (c.g.vertices));
      Printf.printf "\nThe vertices are :";
      VerSet.iter (fun v -> Printf.printf "(%d,%d), " (fst v) (snd v)) (vertices_from_edges c.g.edges);
      (*print_linearization (List.rev (c.l(c.h(i))));
      Printf.printf "Lin result = ";
      print_st (apply_events (List.rev (c.l(c.h(i)))));
      Printf.printf "\nState = ";
      print_st (c.n (c.h i));*)
      assert (eq (apply_events (List.rev (c.l(c.h(i))))) (c.n (c.h i)));
    done;
    Printf.printf "\n******************************************"

let _ =
  let start_time = Unix.gettimeofday () in
  let init_config = init_config (* Initialize with your actual initial config *) in
  let nv = 15 in (* Example: number of versions *)
  let configs = explore_configs [init_config] nr nv [] in
  List.iter run_tests_for_config configs;
  let end_time = Unix.gettimeofday () in
  let total_time = end_time -. start_time in
  Printf.printf "\n\nLength of config list: %d" (List.length configs);
  Printf.printf "\nTotal execution time: %.6f seconds\n" total_time