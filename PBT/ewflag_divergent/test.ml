open OUnit2
open Mrdt

let test_config =
  let c = init_config in
  let c1 = createBranch c 0 1 in
  let c2 = apply c1 1 (gen_ts (), 1, Enable) in
  let c3 = merge c2 0 1 in 
  let c4 = apply c3 1 (gen_ts (), 1, Disable) in
  let c5 = merge c4 0 1 in
  let c6 = apply c5 0 (gen_ts (), 0, Enable) in
  let c7 = createBranch c6 0 2 in
  let c8 = merge c7 2 1 in
  let c9 = apply c8 2 (gen_ts (), 2, Disable) in
  let c10 = merge c9 1 2 in 
  let c11 = merge c10 0 1 in c11
 
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
  "test_lin" >:: (fun _ -> assert (eq (apply_events (List.rev (test_config.l(test_config.h(0))))) 
                                      (test_config.n (test_config.h 0))));
]

let _ = run_test_tt_main tests
