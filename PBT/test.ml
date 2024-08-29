open OUnit2
open Mrdt

(*let opt_to_val opt =
  match opt with
  | None -> 0
  | Some value -> value*)

  let test_config =
    let c = init_config in
    let c1 = createBranch c 0 1 1 in
    let c2 = apply c1 1 2 Incr in
    let c3 = merge c2 0 1 3 in 
    let c4 = apply c3 1 4 Incr in
    let c5 = merge c4 0 1 5 in
    let c6 = apply c5 0 6 Incr in c6
    
let sanity_check (c:config) = 
  assert (VerSet.equal c.g.vertices (vertices_from_edges c.g.edges))

let tests = "Test suite for MRDT" >::: [
  "sanity_check" >:: (fun _ -> sanity_check test_config);
  "first_test" >:: (fun _ -> print_dag test_config);
]

let _ = run_test_tt_main tests
