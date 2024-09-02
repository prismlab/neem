open OUnit2
open Mrdt

(*let opt_to_val opt =
  match opt with
  | None -> 0
  | Some value -> value*)

  (*let test_config =
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
    let c11 = merge c10 0 1 in c11*)
  
  (*let test_config =
    let c = apply init_config 1 (gen_ts (), 1, Enable) in
    let c1 = merge c 0 1 in
    let c2 = apply c1 1 (gen_ts (), 1, Disable) in
    let c3 = apply c2 2 (gen_ts (), 2, Enable) in
    let c4 = apply c3 2 (gen_ts (), 2, Disable) in
    let c5 = merge c4 0 2 in
    let c6 = merge c5 0 1 in
    let c7 = merge c6 2 1 in
    c7*)

  let test_config =
    let c = apply init_config 1 (gen_ts (), 1, Add 1) in
    let c1 = merge c 0 1 in
    let c2 = apply c1 2 (gen_ts (), 2, Add 2) in
    let c3 = apply c2 1 (gen_ts (), 1, Rem 2) in
    let c4 = apply c3 2 (gen_ts (), 2, Rem 2) in
    let c5 = merge c4 0 2 in
    let c6 = merge c5 0 1 in
    let c7 = merge c6 2 1 in
    let c8 = apply c7 2 (gen_ts (), 2, Rem 2) in
    c8

let sanity_check (c:config) = 
  assert (VerSet.equal c.g.vertices (vertices_from_edges c.g.edges))

let tests = "Test suite for MRDT" >::: [
  "sanity_check" >:: (fun _ -> sanity_check test_config);
  "print_dag" >:: (fun _ -> print_dag test_config);
  "print_lin" >:: (fun _ -> print_linearization (linearize test_config 2));
  (*"lo check1" >:: (fun _ -> assert (not (lo test_config (1, 1, (Add 1)) (3, 1, (Rem 2)))));
  "lo check2" >:: (fun _ -> assert ((lo test_config (3, 1, (Rem 2)) (2, 2, (Add 2)))));*)
  (*"vis_check" >:: (fun _ -> assert (is_visible test_config (1, 1, (Add 1)) (2, 1, (Rem 2)) &&
                                    is_visible test_config (3, 2, (Add 2)) (4, 2, (Rem 1)) &&
                                    are_concurrent test_config (1, 1, (Add 1)) (4, 2, (Rem 1)) &&
                                    are_concurrent test_config (3, 2, (Add 2)) (2, 1, (Rem 2))));*)
  "print_res" >:: (fun _ -> Printf.printf "\nLin result = ";
                            print_orset (apply_events (linearize test_config 2));
                            Printf.printf "\nState = ";
                            print_orset (test_config.n (test_config.h 2)));


      (*(fst (apply_events (linearize test_config 0))) (snd (apply_events (linearize test_config 0)))  
      (fst (test_config.n (test_config.h 0))) (snd (test_config.n (test_config.h 0))));*)
  "test_lin" >:: (fun _ -> assert (apply_events (linearize test_config 2) = test_config.n (test_config.h 2)))
]

let _ = run_test_tt_main tests
