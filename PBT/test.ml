open OUnit2
open Mrdt

(*let opt_to_val opt =
  match opt with
  | None -> 0
  | Some value -> value*)

let tests = "Test suite for MRDT" >::: [
  ("first_test" >:: (fun _ -> 
    let c = init_config in
    let c1 = createBranch c 0 1 1 in
    let c2 = apply c1 1 2 Incr in
    (*let l = find_lca c2 0 1 in*)
    (*Printf.printf "LCA of 1 and 2 is %d\n" (opt_to_val l);*)
    let c3 = merge c2 0 1 3 in 
    let c4 = apply c3 1 4 Incr in
    let c5 = merge c4 0 1 5 in
    let c6 = apply c5 0 6 Incr in
    let c7 = merge c6 0 0 7 in
    let c8 = createBranch c7 1 2 8 in
    let c9 = merge c8 0 2 9 in
    print_dag c9))
    (*Printf.printf "LCA of 1 and 2 is %d\n" (opt_to_val l)))*)
  (*"empty" >:: (fun _ -> let f = init_config in assert_equal f.vis f.vis);*)
]

let _ = run_test_tt_main tests

