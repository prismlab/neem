open OUnit2
open Mrdt

let test_config =
  let c1 = createBranch init_config 0 1 in
  let c2 = apply c1 1 (gen_ts (), 1, Enable) in
  let c3 = merge c2 0 1 in 
  let c4 = apply c3 1 (gen_ts (), 1, Disable) in
  let c6 = apply c4 2 (gen_ts (), 2, Enable) in
  let c7 = apply c6 2 (gen_ts (), 2, Disable) in
  let c8 = merge c7 0 2 in
  let c10 = merge c8 0 1 in 
  let c11 = merge c10 2 1 in 
  c11
 
let sanity_check (c:config) = 
  assert (VerSet.equal c.g.vertices (vertices_from_edges c.g.edges))

let tests = "Test suite for MRDT" >::: [
  "sanity_check" >:: (fun _ -> sanity_check test_config);
  "print_dag" >:: (fun _ -> print_dag test_config);
  "print_lin" >:: (fun _ -> print_linearization (List.rev (test_config.l(test_config.h(0)))));
  "print_res" >:: (fun _ -> Printf.printf "\nLin result = ";
                            print_st (apply_events (List.rev (test_config.l(test_config.h(0)))));
                            Printf.printf "\nState = ";
                            print_st (test_config.n (test_config.h 0)));
  "test_lin1" >:: (fun _ -> assert (eq (apply_events (List.rev (test_config.l(test_config.h(0))))) (test_config.n (test_config.h 0))));
  "test_lin2" >:: (fun _ -> assert (eq (apply_events (List.rev (test_config.l(test_config.h(1))))) (test_config.n (test_config.h 1))));
  "test_lin3" >:: (fun _ -> assert (eq (apply_events (List.rev (test_config.l(test_config.h(2))))) (test_config.n (test_config.h 2))));
]

let _ = run_test_tt_main tests
