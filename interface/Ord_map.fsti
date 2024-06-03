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

 @summary FStar.Map provides a polymorphic, partial map from keys to
   values, where keys support decidable equality.

 `m:Map.t key value` is a partial map from `key` to `value`

  A distinctive feature of the library is in its model of partiality.

  A map can be seen as a pair of:
    1. a total map `key -> Tot value`
    2. a set of keys that record the domain of the map

*)
module Ord_map

//module S = Set_extended
open FStar.FunctionalExtensionality
module FSet = Finite_set //FStar.FiniteSet.Base

type setfun_t (a: eqtype)
              (b: Type u#b)
              (s: FSet.t a) =
   f: (a ^-> option b){forall (key: a). FSet.mem key s == Some? (f key)}
   
(* Map.t key value: The main type provided by this module *)
val t (key:eqtype) ([@@@strictly_positive] value:Type u#a)
  : Type u#a

(* domain m : The set of keys on which this partial map is defined *)
val domain: #key:eqtype -> #value:Type -> t key value -> Tot (FSet.t key)

val elements (#a: eqtype) (#b: Type u#b) (m: t a b)
  : setfun_t a b (domain m)
  
let contains (#a: eqtype) (#b: Type u#b) (m: t a b) (key: a) =
  FSet.mem key (domain m)
  
let sel (#a: eqtype) (#b: Type u#b) (key: a) (m: t a b{contains m key}) : b =
  Some?.v ((elements m) key)

val cardinality: #key:eqtype -> #value:Type -> t key value -> GTot nat
  
val upd (#a: eqtype) (#b: Type u#b) (m: t a b) (k: a) (v: b) : t a b
  
val emptymap (#a: eqtype) (#b: Type u#b) : t a b

val subtract (#a: eqtype) (#b: Type u#b) (m: t a b) (s: FSet.t a) : t a b

let remove (#a: eqtype) (#b: Type u#b) (key: a) (m: t a b) : t a b =
  subtract m (FSet.singleton key)

(*let upd (#a: eqtype) (#b: Type u#b) (m: t a b) (k: a) (v: b) =
  let r = remove k m in
  insert r k v*)

val map_val: #key:eqtype -> #val1:Type u#b -> #val2:Type u#c -> f:(val1 -> val2) -> t key val1 -> Tot (t key val2)

val iter_upd: #key:eqtype -> #val1:Type u#b -> #val2:Type u#c -> f:(key -> val1 -> val2) -> t key val1 -> Tot (t key val2)

val const_on: #key:eqtype -> #val1:Type u#b -> k:(FSet.t key) -> val1 -> Tot (t key val1)

val values (#a: eqtype) (#b: Type u#b) (m: t a b)
  : GTot (b -> prop)

val items (#a: eqtype) (#b: Type u#b) (m: t a b)
  : GTot ((a * b) -> prop)

val equal (#a: eqtype) (#b: Type u#b) (m1: t a b) (m2: t a b)
  : prop

let mem (#a: eqtype) (#b: Type u#b) (key: a) (m: t a b) =
  FSet.mem key (domain m)

val choose (#a: eqtype) (#b: Type u#b) (m: t a b{exists key. mem key m})
  : GTot (key: a{mem key m})

val cardinality_zero_iff_empty_fact' (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures cardinality m = 0 <==> m == emptymap)
          [SMTPat (cardinality m)]

(*let cardinality_zero_iff_empty_fact =
  forall (k: eqtype) (v:Type u#b) (m: t k v).{:pattern cardinality m}
    cardinality m = 0 <==> m == emptymap*)

val empty_or_domain_occupied_fact' (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures m == emptymap \/ (exists k. mem k m))
          [SMTPat (domain m)]
          
(*let empty_or_domain_occupied_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b).{:pattern domain m}
    m == emptymap \/ (exists k.{:pattern mem k m} mem k m)*)

val empty_or_values_occupied_fact' (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures m == emptymap \/ (exists v. (values m) v))
          [SMTPat (values m v)]
  
(*let empty_or_values_occupied_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b).{:pattern values m}
    m == emptymap \/ (exists v. {:pattern values m v } (values m) v)*)

val empty_or_items_occupied_fact' (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures m == emptymap \/ (exists item. (items m) item))
          [SMTPat (exists item. items m item)]
   
(*let empty_or_items_occupied_fact =
  forall (a: eqtype) (b:Type u#b) (m: t a b).{:pattern items m}
    m == emptymap \/ (exists item. {:pattern items m item } (items m) item)*)

val map_cardinality_matches_domain_fact' (#k: eqtype) (#v: Type u#b) (m: t k v)
  : Lemma (ensures FSet.cardinality (domain m) = cardinality m)
          [SMTPat (FSet.cardinality (domain m))]

(*let map_cardinality_matches_domain_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b).{:pattern FSet.cardinality (domain m)}
    FSet.cardinality (domain m) = cardinality m*)

val values_contains_fact' (#a: eqtype) (#b: Type u#b) (m: t a b) (v:b) 
  : Lemma (ensures (values m) v <==>
       (exists (u: a).FSet.mem u (domain m) /\ (elements m) u == Some v))
       [SMTPat ((values m) v)]
  
(*let values_contains_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b) (v: b).{:pattern (values m) v}
    (values m) v <==>
       (exists (u: a).{:pattern FSet.mem u (domain m) \/ ((elements m) u)}
          FSet.mem u (domain m) /\ (elements m) u == Some v)*)

val items_contains_fact' (#a: eqtype) (#b: Type u#b) (m: t a b) (item: a * b)
  : Lemma (ensures (items m) item <==>
        FSet.mem (fst item) (domain m)
      /\ (elements m) (fst item) == Some (snd item))
        [SMTPat ((items m) item)]

(*let items_contains_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b) (item: a * b).{:pattern (items m) item}
    (items m) item <==>
        FSet.mem (fst item) (domain m)
      /\ (elements m) (fst item) == Some (snd item)*)

val empty_domain_empty_fact' (#a: eqtype) (#b: Type u#b) (u:a)
  : Lemma (ensures not (FSet.mem u (domain (emptymap #a #b))))
          [SMTPat (FSet.mem u (domain (emptymap #a #b)))]

(*let empty_domain_empty_fact =
  forall (a: eqtype) (b: Type u#b) (u: a).{:pattern FSet.mem u (domain (emptymap #a #b))}
    not (FSet.mem u (domain (emptymap #a #b)))*)

val upd_elements_fact' (#a: eqtype) (#b: Type u#b) (m: t a b) (key:a) (key':a) (value:b)
  : Lemma (ensures (key' = key ==>   FSet.mem key' (domain (upd m key value))
                     /\ (elements (upd m key value)) key' == Some value)
    /\ (key' <> key ==>   FSet.mem key' (domain (upd m key value)) = FSet.mem key' (domain m)
                     /\ (elements (upd m key value)) key' == (elements m) key'))
                     [SMTPat (upd m key value)]

val const_on_elements_fact' (#a: eqtype) (#b: Type u#b) (s: FSet.t a) (value:b)
  : Lemma (ensures (forall k. FSet.mem k s <==> (FSet.mem k (domain (const_on s value)))) /\
                   (forall k. FSet.mem k s ==> (elements (const_on s value)) k == Some value))
          [SMTPat (const_on s value)]
  
  (*(key' = key ==>   FSet.mem key' (domain (upd m key value))
                     /\ (elements (upd m key value)) key' == Some value)
    /\ (key' <> key ==>   FSet.mem key' (domain (upd m key value)) = FSet.mem key' (domain m)
                     /\ (elements (upd m key value)) key' == (elements m) key'))
                     [SMTPat (upd m key value)]*)

val cons_on_member_cardinality_fact' (#a: eqtype) (#b: Type u#b) (s: FSet.t a) (value:b)
  : Lemma (ensures (forall k. FSet.mem k (domain (const_on s value)) ==> cardinality (const_on s value) = FSet.cardinality s))
    [SMTPat (cardinality (const_on s value))]

(*let upd_elements_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b) (key: a) (key': a) (value: b).
    {:pattern FSet.mem key' (domain (upd m key value)) \/ ((elements (upd m key value)) key')}
      (key' = key ==>   FSet.mem key' (domain (upd m key value))
                     /\ (elements (upd m key value)) key' == Some value)
    /\ (key' <> key ==>   FSet.mem key' (domain (upd m key value)) = FSet.mem key' (domain m)
                     /\ (elements (upd m key value)) key' == (elements m) key')*)

val upd_member_cardinality_fact' (#a: eqtype) (#b: Type u#b) (m: t a b) (key:a) (value:b)
  : Lemma (ensures FSet.mem key (domain m) ==> cardinality (upd m key value) = cardinality m)
    [SMTPat (cardinality (upd m key value))]

(*let upd_member_cardinality_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b) (key: a) (value: b).{:pattern cardinality (upd m key value)}
    FSet.mem key (domain m) ==> cardinality (upd m key value) = cardinality m*)

val upd_nonmember_cardinality_fact' (#a: eqtype) (#b: Type u#b) (m: t a b) (key: a) (value: b)
  : Lemma (not (FSet.mem key (domain m)) ==> cardinality (upd m key value) = cardinality m + 1)
    [SMTPat (cardinality (upd m key value))]
  
(*let upd_nonmember_cardinality_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b) (key: a) (value: b).{:pattern cardinality (upd m key value)}
    not (FSet.mem key (domain m)) ==> cardinality (upd m key value) = cardinality m + 1*)

val iter_upd_domain_fact' (#a: eqtype) (#b: Type u#b) (#c: Type u#c) (f:a -> b -> c) (m: t a b) 
  : Lemma (ensures domain (iter_upd f m) == domain m)
          [SMTPat (domain (iter_upd f m))]

val iter_upd_element_fact' (#a: eqtype) (#b: Type u#b) (#c: Type u#c) (f:a -> b -> c) (m: t a b) (key:a)
  : Lemma (ensures FSet.mem key (domain (iter_upd f m)) ==> FSet.mem key (domain m) /\ 
                   (if Some? ((elements m) key) then 
                     (let Some v = (elements m) key in
                       (elements (iter_upd f m)) key == Some (f key v)) //(f key v))
                    else true))
    [SMTPat ((elements (iter_upd f m)) key)]

val subtract_domain_fact' (#a: eqtype) (#b: Type u#b) (m: t a b) (s:FSet.t a)
  : Lemma (ensures domain (subtract m s) == FSet.difference (domain m) s)
          [SMTPat (domain (subtract m s))]

(*let subtract_domain_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b) (s: FSet.set a).{:pattern domain (subtract m s)}
    domain (subtract m s) == FSet.difference (domain m) s*)

val subtract_element_fact' (#a: eqtype) (#b: Type u#b) (m: t a b) (s:FSet.t a) (key:a) 
  : Lemma (ensures FSet.mem key (domain (subtract m s)) ==> FSet.mem key (domain m) /\ (elements (subtract m s)) key == (elements m) key)
    [SMTPat ((elements (subtract m s)) key)]

(*let subtract_element_fact =
  forall (a: eqtype) (b: Type u#b) (m: t a b) (s: FSet.set a) (key: a).{:pattern (elements (subtract m s)) key}
    FSet.mem key (domain (subtract m s)) ==> FSet.mem key (domain m) /\ (elements (subtract m s)) key == (elements m) key*)

val map_equal_fact' (#a: eqtype) (#b: Type u#b) (m1 m2: t a b) 
  : Lemma (ensures equal m1 m2 <==>   (forall key. FSet.mem key (domain m1) = FSet.mem key (domain m2))
                   /\ (forall key. FSet.mem key (domain m1) ==> (elements m1) key == (elements m2) key))
    [SMTPat (equal m1 m2)]

(*let map_equal_fact =
  forall (a: eqtype) (b: Type u#b) (m1: t a b) (m2: t a b).{:pattern equal m1 m2}
    equal m1 m2 <==>   (forall key. FSet.mem key (domain m1) = FSet.mem key (domain m2))
                   /\ (forall key. FSet.mem key (domain m1) ==> (elements m1) key == (elements m2) key)*)

val map_extensionality_fact' (#a: eqtype) (#b: Type u#b) (m1 m2: t a b) 
  : Lemma (ensures equal m1 m2 ==> m1 == m2)
    [SMTPat (equal m1 m2)]

(*let map_extensionality_fact =
  forall (a: eqtype) (b: Type u#b) (m1: t a b) (m2: t a b).{:pattern equal m1 m2}
    equal m1 m2 ==> m1 == m2*)

(*val lemma_equal_intro: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                       Lemma (requires (forall k. contains m1 k /\ contains m2 k /\ 
                                             sel k m1 == sel k m2))
                             (ensures (equal m1 m2))
                             [SMTPat (equal m1 m2)]

val lemma_equal_elim: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                      Lemma (ensures (equal m1 m2 <==> m1 == m2))
                            [SMTPat (equal m1 m2)]

val lemma_equal_intro': #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                       Lemma (requires (equal m1 m2))
                             (ensures (forall k. contains m1 k /\ contains m2 k /\ 
                                             sel k m1 == sel k m2))
                             [SMTPat (equal m1 m2)]*)

(*let equal_refl (#key:eqtype) (#value:Type) (m1:t key value) (m2:t key value) :
    Lemma (requires m1 == m2)
          (ensures (forall k. (contains m1 k = contains m2 k) /\ sel k m1 == sel k m2))
          [SMTPat (m1 == m2)] = ()*)
          
(*let all_finite_map_facts =
    cardinality_zero_iff_empty_fact u#b
  /\ empty_or_domain_occupied_fact u#b
  /\ empty_or_values_occupied_fact u#b
  /\ empty_or_items_occupied_fact u#b
  /\ map_cardinality_matches_domain_fact u#b
  /\ values_contains_fact u#b
  /\ items_contains_fact u#b
  /\ empty_domain_empty_fact u#b
  /\ upd_elements_fact u#b
  /\ upd_member_cardinality_fact u#b
  /\ upd_nonmember_cardinality_fact u#b
  /\ subtract_domain_fact u#b
  /\ subtract_element_fact u#b
  /\ map_equal_fact u#b
  /\ map_extensionality_fact u#b
  
val all_finite_map_facts_lemma (_:unit)
  : Lemma (all_finite_map_facts u#b)*)

