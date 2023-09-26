module ListUtils

open FStar.List.Tot

let rec diff_s (s1 s2:list (pos * string)) 
  : Tot (d:list (pos * string){(forall e. mem e d <==> mem e s1 /\ not (mem e s2))}) (decreases s1) =
  match s1 with
  |[] -> []
  |x::xs -> if mem x s2 then diff_s xs s2 else x::diff_s xs s2

let rec lem_diff (s1 s2:list (pos * string))
  : Lemma (requires s1 = s2)
          (ensures diff_s s1 s2 = [])
          (decreases %[s1;s2]) =
  match s1,s2 with
  |[],[] -> ()
  |x::xs,y::ys -> assert (x=y);lem_diff xs ys
