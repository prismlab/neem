(*
   Copyright 2008-2021 John Li, Jay Lorch, Rustan Leino, Alex Summers,
   Dan Rosen, Nikhil Swamy, Microsoft Research, and contributors to
   the Dafny Project

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Includes material from the Dafny project
   (https://github.com/dafny-lang/dafny) which carries this license
   information:

     Created 9 February 2008 by Rustan Leino.
     Converted to Boogie 2 on 28 June 2008.
     Edited sequence axioms 20 October 2009 by Alex Summers.
     Modified 2014 by Dan Rosen.
     Copyright (c) 2008-2014, Microsoft.
     Copyright by the contributors to the Dafny Project
     SPDX-License-Identifier: MIT
*)

(**
This module declares a type and functions used for modeling
finite maps as they're modeled in Dafny.

@summary Type and functions for modeling finite maps
*)

module Finite_map
open FStar.FunctionalExtensionality
module FLT = FStar.List.Tot
module FSet = Finite_set
open Finite_set
module T = FStar.Tactics.V2

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

let cardinality_zero_iff_empty_fact m = 
  introduce forall (a: eqtype) (b:Type u#b) (m: t a b). cardinality m = 0 <==> m == emptymap
  with (
    introduce cardinality m = 0 ==> m == emptymap
    with _. assert (feq (elements m) (elements emptymap))
  )
  
let empty_or_domain_occupied_fact m = 
  introduce forall (a: eqtype) (b:Type u#b) (m: t a b). m == emptymap \/ (exists k. mem k m)
    with (  
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists k. mem k m)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_fact m
      )
    else
      introduce m == emptymap \/ (exists k. mem k m)
      with Right ()
    )

let empty_or_values_occupied_fact m = 
  introduce forall (a: eqtype) (b:Type u#b) (m: t a b). m == emptymap \/ (exists v. (values m) v)
  with
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists v. (values m) v)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_fact m
      )
    else
      introduce m == emptymap \/ (exists v. (values m) v)
      with Right (
        let k = choose m in
        let v = Some?.v ((elements m) k) in
        assert ((values m) v)
      )

let empty_or_items_occupied_fact m =
  introduce forall (a: eqtype) (b: Type u#b) (m: t a b). m == emptymap \/ (exists item. (items m) item)
  with
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists v. (values m) v)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_fact m
      )
    else
      introduce m == emptymap \/ (exists item. (items m) item)
      with Right (
        let k = choose m in
        let v = Some?.v ((elements m) k) in
        assert ((items m) (k, v))
      )

let map_cardinality_matches_domain_fact m = ()
let values_contains_fact m v = ()
let items_contains_fact m item = ()
let empty_domain_empty_fact u = ()

let upd_elements_fact m k k' v = ()

let const_on_elements_fact s v = ()

let cons_on_member_cardinality_fact s v = ()
let upd_member_cardinality_fact m k v = ()
let upd_nonmember_cardinality_fact m k v = ()
let iter_upd_domain_fact f m = ()
let iter_upd_element_fact f m k = ()
let subtract_domain_fact m s = ()
let subtract_element_fact m s k = ()
let map_equal_fact m1 m2 = ()
let map_extensionality_fact m1 m2 = 
  introduce forall (a: eqtype) (b:Type u#b) (m1: t a b) (m2: t a b). equal m1 m2 ==> m1 == m2
  with (
    introduce equal m1 m2 ==> m1 == m2
    with _. (
      assert (FSet.equal (domain m1) (domain m2));
      assert (feq (elements m1) (elements m2))
    )
  )
