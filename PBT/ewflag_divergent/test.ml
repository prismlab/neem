(*open OUnit2
open Mrdt

let max_rep = 2 (* for generating 3 replicas *)

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
run_tests_multiple_times 200;
let end_time = Unix.gettimeofday () in
let total_time = end_time -. start_time in
Printf.printf "Total execution time: %.6f seconds\n" total_time*)
  
(*open OUnit2*)
open Mrdt

(*let max_rep = 2 *)(* for generating 3 replicas *)

(*let gen_op = QCheck.Gen.oneof [
  QCheck.Gen.return Enable;
  QCheck.Gen.return Disable;
]*)

(*let gen_rep = QCheck.Gen.int_range 0 max_rep

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
Printf.printf "Total execution time: %.6f seconds\n" total_time*)

(*let gen_rep n = QCheck.Gen.int_bound n (*[0..n]*)
let rec gen_diff_id id n =
  let new_id = QCheck.Gen.generate1 (gen_rep n) in
  if new_id = id then gen_diff_id id n else new_id*)

(*let rec gen_fork_id (n:int) (r:RepSet.t) (*no. of replicas *) =
  let id = QCheck.Gen.generate1 (gen_rep n) in
  if RepSet.mem id r then gen_fork_id n r else id

let rec gen_diff_fork_id n r id =
  let new_id = gen_fork_id n r in
  if new_id = id then gen_diff_fork_id n r id else new_id*)

  (*let explore_configs (cl:config list) (ns:int) : config list =*)
    let rec explore_configs_nr (cl:config list) (ns:int) (acc:config list) : config list =
      match cl with
      | [] -> acc
      | c1::cn ->
          if c1.ns = ns then explore_configs_nr cn ns (c1::acc)
          else if c1.ns > ns then explore_configs_nr cn ns acc
          else
            let new_cl = List.fold_left
              (fun acc r1 ->
                (*debug_print "\nAPPLY** r%d Enable" r1;*)
                let new_e = apply c1 r1 (gen_ts (), r1, Enable) in
                (*debug_print "\nAPPLY** r%d Disable" r1;*)
                let new_d = apply c1 r1 (gen_ts (), r1, Disable) in
                new_e::new_d::acc) [] (List.init ns (fun i -> i)) in

            (*if ns = 1 then new_cl@acc
            else *)
            let new_cl1 = 
              List.fold_left (fun acc i ->
                List.fold_left (fun inner_acc j ->
                  let new_m = merge c1 i j in
                  new_m::inner_acc
               ) acc (RepSet.elements (RepSet.remove i (c1.r))) (*List.init (ns - i) (fun k -> i + k + 1)*)
             ) [] (RepSet.elements c1.r) (*List.init (ns + 1) (fun i -> i)*) in


              (*let mr1 = QCheck.Gen.generate1 (gen_rep (ns)) in
              let mr2 = gen_diff_id mr1 (ns) in
              (*debug_print "\nMERGE** r%d r%d" mr1 mr2;*)
              let new_m1 = merge c1 mr1 mr2 in*)
              explore_configs_nr (new_cl@(new_cl1@cn)) ns acc (*in
    List.fold_left (fun acc nr -> explore_configs_nr cl nr ns acc) [] (List.init ns (fun i -> i))*)
  
  
(*let run_tests c =
  print_dag c;
    for i = 0 to RepSet.cardinal c.r do
      Printf.printf "\n\n***Testing linearization for R%d" i;
      Printf.printf "\nNo. of vertices at R%d: %d" i (VerSet.cardinal (c.g.vertices));
      Printf.printf "\nThe vertices are :";
      VerSet.iter (fun v -> Printf.printf "(%d,%d), " (fst v) (snd v)) (vertices_from_edges c.g.edges);
      print_linearization (List.rev (c.l(c.h(i))));
      Printf.printf "Lin result = ";
      print_st (apply_events (List.rev (c.l(c.h(i)))));
      Printf.printf "\nState = ";
      print_st (c.n (c.h i));
      assert (eq (apply_events (List.rev (c.l(c.h(i))))) (c.n (c.h i)));
    done;
    Printf.printf "\n******************************************"*)

let _ =
  let start_time = Unix.gettimeofday () in
  let ns = 9 in
  let configs =
    if ns = 0 then [init_config]
    else explore_configs_nr [init_config] ns [] in
    Printf.printf "\n\nLength of config list: %d" (List.length configs);
    (*List.iter run_tests configs;*)
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    Printf.printf "\n\nLength of config list: %d" (List.length configs);
    Printf.printf "\nTotal execution time: %.6f seconds\n" total_time


    (* COUNTER EXAMPLE generated with ns = 6 
       min time = *)