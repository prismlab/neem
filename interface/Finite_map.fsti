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
module FSet = Finite_set

type setfun_t (a: eqtype)
              (b: Type u#b)
              (s: FSet.t a) =
   f: (a ^-> option b){forall (key: a). FSet.mem key s == Some? (f key)}
   
(* Map.t key value: The main type provided by this module *)
val t (key:eqtype) ([@@@strictly_positive] value:Type u#a)
  : Type u#a

(* domain m : The set of keys on which this partial map is defined *)
val domain: #key:eqtype -> #value:Type -> t key value -> Tot (FSet.t key)

val elements (#a: eqtype) (#b: Type u#b) (m: t a b) : setfun_t a b (domain m)
  
let contains (#a: eqtype) (#b: Type u#b) (m: t a b) (key: a) =
  FSet.mem key (domain m)
  
let sel (#a: eqtype) (#b: Type u#b) (key: a) (m: t a b{contains m key}) : b =
  Some?.v ((elements m) key)

val cardinality (#a: eqtype) (#b: Type u#b) (m: t a b) : GTot nat
  
val upd (#a: eqtype) (#b: Type u#b) (m: t a b) (k: a) (v: b) : t a b
  
val emptymap (#a: eqtype) (#b: Type u#b) : t a b

val subtract (#a: eqtype) (#b: Type u#b) (m: t a b) (s: FSet.t a) : t a b

let remove (#a: eqtype) (#b: Type u#b) (key: a) (m: t a b) : t a b =
  subtract m (FSet.singleton key)

val map_val (#key: eqtype) (#val1: Type u#b) (#val2:Type u#c) (f:(val1 -> val2)) (m:t key val1) : Tot (t key val2)

val iter_upd (#key: eqtype) (#val1: Type u#b) (#val2:Type u#c) (f:(key -> val1 -> val2)) (m:t key val1) : Tot (t key val2)

val const_on (#key:eqtype) (#val1:Type u#b) (k:FSet.t key) (v:val1) : Tot (t key val1)

val values (#a: eqtype) (#b: Type u#b) (m: t a b) : GTot (b -> prop)

val items (#a: eqtype) (#b: Type u#b) (m: t a b) : GTot ((a * b) -> prop)

val equal (#a: eqtype) (#b: Type u#b) (m1: t a b) (m2: t a b) : prop

let mem (#a: eqtype) (#b: Type u#b) (key: a) (m: t a b) =
  FSet.mem key (domain m)

val choose (#a: eqtype) (#b: Type u#b) (m: t a b{exists key. mem key m}) : GTot (key: a{mem key m})

val cardinality_zero_iff_empty_fact (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures cardinality m = 0 <==> m == emptymap)
          [SMTPat (cardinality m)]

val empty_or_domain_occupied_fact (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures m == emptymap \/ (exists k. mem k m))
          [SMTPat (domain m)]

val empty_or_values_occupied_fact (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures m == emptymap \/ (exists v. (values m) v))
          [SMTPat (values m v)]
  
val empty_or_items_occupied_fact (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures m == emptymap \/ (exists item. (items m) item))
          [SMTPat (exists item. items m item)]
   
val map_cardinality_matches_domain_fact (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures FSet.cardinality (domain m) = cardinality m)
          [SMTPat (FSet.cardinality (domain m))]

val values_contains_fact (#a: eqtype) (#b: Type u#b) (m: t a b) (v:b) 
  : Lemma (ensures (values m) v <==> (exists (u: a).FSet.mem u (domain m) /\ (elements m) u == Some v))
          [SMTPat ((values m) v)]
  
val items_contains_fact (#a: eqtype) (#b: Type u#b) (m: t a b) (item: a * b)
  : Lemma (ensures (items m) item <==> FSet.mem (fst item) (domain m) /\ (elements m) (fst item) == Some (snd item))
          [SMTPat ((items m) item)]

val empty_domain_empty_fact (#a: eqtype) (#b: Type u#b) (u:a)
  : Lemma (ensures not (FSet.mem u (domain (emptymap #a #b))))
          [SMTPat (FSet.mem u (domain (emptymap #a #b)))]

val upd_elements_fact (#a: eqtype) (#b: Type u#b) (m: t a b) (key:a) (key':a) (value:b)
  : Lemma (ensures (key' = key ==> FSet.mem key' (domain (upd m key value)) /\ (elements (upd m key value)) key' == Some value)
                   /\ (key' <> key ==> FSet.mem key' (domain (upd m key value)) = FSet.mem key' (domain m)
                   /\ (elements (upd m key value)) key' == (elements m) key'))
          [SMTPat (upd m key value)]

val const_on_elements_fact (#a: eqtype) (#b: Type u#b) (s: FSet.t a) (value:b)
  : Lemma (ensures (forall k. FSet.mem k s <==> (FSet.mem k (domain (const_on s value)))) /\
                   (forall k. FSet.mem k s ==> (elements (const_on s value)) k == Some value))
          [SMTPat (const_on s value)]

val cons_on_member_cardinality_fact (#a: eqtype) (#b: Type u#b) (s: FSet.t a) (value:b)
  : Lemma (ensures (forall k. FSet.mem k (domain (const_on s value)) ==> cardinality (const_on s value) = FSet.cardinality s))
          [SMTPat (cardinality (const_on s value))]

val upd_member_cardinality_fact (#a: eqtype) (#b: Type u#b) (m: t a b) (key:a) (value:b)
  : Lemma (ensures FSet.mem key (domain m) ==> cardinality (upd m key value) = cardinality m)
          [SMTPat (cardinality (upd m key value))]

val upd_nonmember_cardinality_fact (#a: eqtype) (#b: Type u#b) (m: t a b) (key: a) (value: b)
  : Lemma (not (FSet.mem key (domain m)) ==> cardinality (upd m key value) = cardinality m + 1)
          [SMTPat (cardinality (upd m key value))]

val iter_upd_domain_fact (#a: eqtype) (#b: Type u#b) (#c: Type u#c) (f:a -> b -> c) (m: t a b) 
  : Lemma (ensures domain (iter_upd f m) == domain m)
          [SMTPat (domain (iter_upd f m))]

val iter_upd_element_fact (#a: eqtype) (#b: Type u#b) (#c: Type u#c) (f:a -> b -> c) (m: t a b) (key:a)
  : Lemma (ensures FSet.mem key (domain (iter_upd f m)) ==> FSet.mem key (domain m) /\ 
                   (if Some? ((elements m) key) then 
                     (let Some v = (elements m) key in
                       (elements (iter_upd f m)) key == Some (f key v)) //(f key v))
                    else true))
          [SMTPat ((elements (iter_upd f m)) key)]

val subtract_domain_fact (#a: eqtype) (#b: Type u#b) (m: t a b) (s:FSet.t a)
  : Lemma (ensures domain (subtract m s) == FSet.difference (domain m) s)
          [SMTPat (domain (subtract m s))]

val subtract_element_fact (#a: eqtype) (#b: Type u#b) (m: t a b) (s:FSet.t a) (key:a) 
  : Lemma (ensures FSet.mem key (domain (subtract m s)) ==> FSet.mem key (domain m) /\ (elements (subtract m s)) key == (elements m) key)
          [SMTPat ((elements (subtract m s)) key)]

val map_equal_fact (#a: eqtype) (#b: Type u#b) (m1 m2: t a b) 
  : Lemma (ensures equal m1 m2 <==>   (forall key. FSet.mem key (domain m1) = FSet.mem key (domain m2))
                   /\ (forall key. FSet.mem key (domain m1) ==> (elements m1) key == (elements m2) key))
          [SMTPat (equal m1 m2)]

val map_extensionality_fact (#a: eqtype) (#b: Type u#b) (m1 m2: t a b) 
  : Lemma (ensures equal m1 m2 ==> m1 == m2)
          [SMTPat (equal m1 m2)]
