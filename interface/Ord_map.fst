(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
(**
 * Implementation of partial maps with extensional equality
 *)
 
module Ord_map
open FStar.FunctionalExtensionality
module FLT = FStar.List.Tot
module FSet = Finite_set //FStar.FiniteSet.Base
open Finite_set //FStar.FiniteSet.Ambient
module T = FStar.Tactics.V2

(* The main "trick" in the representation of the type `t`
 * is to use a domain-restricted function type `key ^-> value`
 * from the FStar.FunctionalExtensionality library.
 * These restricted function types enjoy extensional equality,
 * which is necessary if Map.t is to also enjoy extensional equality.
 *)

type t (a: eqtype) (b: Type u#b) = (keys: FSet.t a) & (setfun_t a b keys)

let domain (#a: eqtype) (#b: Type u#b) (m: t a b) : FSet.t a =
  let (| keys, _ |) = m in 
  keys
  
let elements (#a: eqtype) (#b: Type u#b) (m: t a b) : (setfun_t a b (domain m)) =
  let (| _, f |) = m in
  f

let cardinality (#a: eqtype) (#b: Type u#b) (m: t a b) : GTot nat =
  FSet.cardinality (domain m)

(*let upd (#a: eqtype) (#b: Type u#b) (m: t a b) (k: a) (v: b) : t a b =
  let keys' = FSet.insert k (domain m) in
  let f' = on_domain a (fun key -> if key = k then Some v else (elements m) key) in
  (| keys', f' |)*)

let upd (#a: eqtype) (#b: Type u#b) (m: t a b) (k: a) (v: b) : t a b =
  let keys' = FSet.union (FSet.singleton k) (domain m) in
  let f' = on_domain a (fun key -> if key = k then Some v else (elements m) key) in
  (| keys', f' |)
  
let emptymap (#a: eqtype) (#b: Type u#b) : (t a b) =
  (| FSet.empty, on_domain a (fun key -> None) |)

let subtract (#a: eqtype) (#b: Type u#b) (m: t a b) (s: FSet.t a) : t a b =
  let keys' = FSet.difference (domain m) s in
  let f' = on_domain a (fun key -> if FSet.mem key keys' then (elements m) key else None) in
  (| keys', f' |)

let map_val (#a: eqtype) (#b: Type u#b) (#c: Type u#c)
            (f: b -> c)
            (m: t a b)
            : t a c =
  let keys = domain m in
  let new_setfun = on_domain a (fun (key: a) -> 
    match (elements m) key with
    | Some v -> Some (f v)
    | None -> None)
  in
  (|keys, new_setfun|)

let iter_upd (#a: eqtype) (#b: Type u#b) (#c: Type u#c)
            (f: a -> b -> c)
            (m: t a b)
            : t a c =
  let keys = domain m in
  let new_setfun = on_domain a (fun (key: a) -> 
    match (elements m) key with
    | Some v -> Some (f key v)
    | None -> None)
  in
  (|keys, new_setfun|)
 
let const_on (#a: eqtype) (#b: Type u#b)
             (keys: FSet.t a)
             (value: b)
             : t a b =
  let setfun = on_domain a (fun (key: a) ->
    if FSet.mem key keys then Some value else None)
  in
  (|keys, setfun|)
  
let values (#a: eqtype) (#b: Type u#b) (m: t a b) : GTot (b -> prop) =
  fun value -> exists key. ((elements m) key == Some value)

let items (#a: eqtype) (#b: Type u#b) (m: t a b) : GTot ((a * b) -> prop) =
  fun item -> ((elements m) (fst item) == Some (snd item))

let equal (#a: eqtype) (#b: Type u#b) (m1: t a b) (m2: t a b) : prop =
  feq (elements m1) (elements m2) /\ True //a bit ugly, a prop coercion

let choose (#a: eqtype) (#b: Type u#b) (m: t a b{exists key. mem key m}) : GTot (key: a{mem key m}) =
  FSet.choose (domain m)

let cardinality_zero_iff_empty_fact' m = 
  introduce forall (a: eqtype) (b:Type u#b) (m: t a b). cardinality m = 0 <==> m == emptymap
  with (
    introduce cardinality m = 0 ==> m == emptymap
    with _. assert (feq (elements m) (elements emptymap))
  )
  
let empty_or_domain_occupied_fact' m = 
  introduce forall (a: eqtype) (b:Type u#b) (m: t a b). m == emptymap \/ (exists k. mem k m)
    with (  
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists k. mem k m)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_fact' m
      )
    else
      introduce m == emptymap \/ (exists k. mem k m)
      with Right ()
    )

let empty_or_values_occupied_fact' m = 
  introduce forall (a: eqtype) (b:Type u#b) (m: t a b). m == emptymap \/ (exists v. (values m) v)
  with
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists v. (values m) v)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_fact' m
      )
    else
      introduce m == emptymap \/ (exists v. (values m) v)
      with Right (
        let k = choose m in
        let v = Some?.v ((elements m) k) in
        assert ((values m) v)
      )

let empty_or_items_occupied_fact' m =
  introduce forall (a: eqtype) (b: Type u#b) (m: t a b). m == emptymap \/ (exists item. (items m) item)
  with
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists v. (values m) v)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_fact' m
      )
    else
      introduce m == emptymap \/ (exists item. (items m) item)
      with Right (
        let k = choose m in
        let v = Some?.v ((elements m) k) in
        assert ((items m) (k, v))
      )

let map_cardinality_matches_domain_fact' m = ()
let values_contains_fact' m v = ()
let items_contains_fact' m item = ()
let empty_domain_empty_fact' u = ()

#set-options "--z3rlimit 300 --ifuel 3"
let upd_elements_fact' m k k' v = ()

let const_on_elements_fact' s v = ()
let cons_on_member_cardinality_fact' s v = ()

let upd_member_cardinality_fact' m k v = ()

let upd_nonmember_cardinality_fact' m k v = ()

let iter_upd_domain_fact' f m = ()

let iter_upd_element_fact' f m k = ()

let subtract_domain_fact' m s = ()
let subtract_element_fact' m s k = ()
let map_equal_fact' m1 m2 = ()
let map_extensionality_fact' m1 m2 = 
  introduce forall (a: eqtype) (b:Type u#b) (m1: t a b) (m2: t a b). equal m1 m2 ==> m1 == m2
  with (
    introduce equal m1 m2 ==> m1 == m2
    with _. (
      assert (FSet.equal (domain m1) (domain m2));
      assert (feq (elements m1) (elements m2))
    )
  )

(*let cardinality_zero_iff_empty_lemma ()
: Lemma (cardinality_zero_iff_empty_fact u#b) =
  introduce forall (a: eqtype) (b:Type u#b) (m: t a b). cardinality m = 0 <==> m == emptymap
  with (
    introduce cardinality m = 0 ==> m == emptymap
    with _. assert (feq (elements m) (elements emptymap))
  )

let empty_or_domain_occupied_lemma ()
  : Lemma (empty_or_domain_occupied_fact u#b)
  = introduce forall (a: eqtype) (b:Type u#b) (m: t a b). m == emptymap \/ (exists k. mem k m)
    with (  
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists k. mem k m)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_lemma ()
      )
    else
      introduce m == emptymap \/ (exists k. mem k m)
      with Right ()
    )

let empty_or_values_occupied_lemma ()
: Lemma (empty_or_values_occupied_fact u#b) =
  introduce forall (a: eqtype) (b:Type u#b) (m: t a b). m == emptymap \/ (exists v. (values m) v)
  with
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists v. (values m) v)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_lemma u#b ()
      )
    else
      introduce m == emptymap \/ (exists v. (values m) v)
      with Right (
        let k = choose m in
        let v = Some?.v ((elements m) k) in
        assert ((values m) v)
      )

let empty_or_items_occupied_lemma ()
: Lemma (empty_or_items_occupied_fact u#b) =
  introduce forall (a: eqtype) (b: Type u#b) (m: t a b). m == emptymap \/ (exists item. (items m) item)
  with
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists v. (values m) v)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_lemma u#b ()
      )
    else
      introduce m == emptymap \/ (exists item. (items m) item)
      with Right (
        let k = choose m in
        let v = Some?.v ((elements m) k) in
        assert ((items m) (k, v))
      )

let map_cardinality_matches_domain_lemma ()
: Lemma (map_cardinality_matches_domain_fact u#b) =
  ()

let values_contains_lemma ()
: Lemma (values_contains_fact u#b) =
  ()

let items_contains_lemma ()
: Lemma (items_contains_fact u#b) =
  ()

let empty_domain_empty_lemma ()
: Lemma (empty_domain_empty_fact u#b) =
  ()

let upd_elements_lemma ()
: Lemma (upd_elements_fact u#b) =
  ()

let upd_member_cardinality_lemma ()
: Lemma (upd_member_cardinality_fact u#b) =
  ()

let upd_nonmember_cardinality_lemma ()
: Lemma (upd_nonmember_cardinality_fact u#b) =
  ()

let subtract_domain_lemma ()
: Lemma (subtract_domain_fact u#b) =
  ()

let subtract_element_lemma ()
: Lemma (subtract_element_fact u#b) =
  ()


let map_equal_lemma ()
: Lemma (map_equal_fact u#b) //Surprising; needed to split this goal into two
= assert (map_equal_fact u#b)
    by (T.norm [delta_only [`%map_equal_fact]];
        let _ = T.forall_intro () in
        let _ = T.forall_intro () in
        let _ = T.forall_intro () in         
        let _ = T.forall_intro () in                 
        T.split ();
        T.smt();
        T.smt())


let map_extensionality_lemma ()
: Lemma (map_extensionality_fact u#b) =
  introduce forall (a: eqtype) (b:Type u#b) (m1: t a b) (m2: t a b). equal m1 m2 ==> m1 == m2
  with (
    introduce equal m1 m2 ==> m1 == m2
    with _. (
      assert (FSet.equal (domain m1) (domain m2));
      assert (feq (elements m1) (elements m2))
    )
  )

let lemma_equal_intro m1 m2 = ()
let lemma_equal_elim m1 m2 = admit()
let lemma_equal_intro' m1 m2 = admit()

let all_finite_map_facts_lemma (_:unit)
  : Lemma (all_finite_map_facts u#b)
  = cardinality_zero_iff_empty_lemma u#b ();
    empty_or_domain_occupied_lemma u#b ();
    empty_or_values_occupied_lemma u#b ();
    empty_or_items_occupied_lemma u#b ();
    map_cardinality_matches_domain_lemma u#b ();
    values_contains_lemma u#b ();
    items_contains_lemma u#b ();
    empty_domain_empty_lemma u#b ();
    upd_elements_lemma u#b ();
    upd_member_cardinality_lemma u#b ();
    upd_nonmember_cardinality_lemma u#b ();
    subtract_domain_lemma u#b ();
    subtract_element_lemma u#b ();
    map_equal_lemma u#b ();
    map_extensionality_lemma u#b ()
*)
