module Set_extended

open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality

let t (a:eqtype) = F.restricted_t a (fun _ -> bool)

let empty #a = F.on_dom a (fun x -> false)
let singleton #a x = F.on_dom a (fun y -> y = x)
let mem #a x s = s x
let equal #a s1 s2 = F.feq s1 s2
let union #a s1 s2 = F.on_dom a (fun x -> s1 x || s2 x)
let intersection #a s1 s2 = F.on_dom a (fun x -> s1 x && s2 x)
let difference #a s1 s2 = F.on_dom a (fun x -> s1 x && not (s2 x))
let filter #a s1 p = F.on_dom a (fun x -> s1 x && p x)
let remove #a s1 x = F.on_dom a (fun y -> s1 y && x <> y)

let mem_empty #a x = ()
let equal_intro #a s1 s2 = ()
let equal_elim #a s1 s2 = () 
let insert_mem # a x s = ()

let mem_subset #a s1 s2 = ()
let subset_mem #a s1 s2 = ()
let mem_union #a s1 s2 x = ()
let mem_singleton #a x y = ()
let mem_intersection #a s1 s2 x = ()
let mem_difference #a s1 s2 x = ()
let mem_filter #a s p x = ()
let mem_remove_x #a s x = ()
let mem_remove_y #a s x y = ()
          
