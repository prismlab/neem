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

module Dependent_map
module S = FStar.Set //Set_extended

/// This module provides an abstract type of maps whose co-domain
/// depends on the value of each key. i.e., it is an encapsulation
/// of [x:key -> value x], where [key] supports decidable equality.
///
/// The main constructors of the type are:
///   * [create]: To create the whole map from a function
///   * [upd]: To update a map at a point
///   * [restrict]: To restrict the domain of a map
///   * [concat]: To concatenate maps by taking the union of their key spaces
///   * [rename]: To rename the keys of a map
///   * [map]: To map a function over the values of a map
///
/// The main eliminators are:
///   * [sel]: To query the map for its value at a point
///
/// The interface is specified in a style that describes the action of
/// each eliminator over each of the constructors
///
/// The map also supports an extensional equality principle.

(** Abstract type of dependent maps, with universe polymorphic values
    and keys in universe 0 with decidable equality *)
val t (key: eqtype) ([@@@strictly_positive] value: (key -> Type u#v)) : Type u#v

(* domain m : The set of keys on which this partial map is defined *)
val domain(#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) : Tot (S.set key)

(* contains m k: Decides if key `k` is in the map `m` *)
val contains (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k:key) : Tot bool

(** Querying the map for its value at a given key *)
val sel (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) : Tot (value k)

(** Updating a map at a point *)
val upd (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k)
    : Tot (t key value)

(* del m k : A map identical to `m` except the key `k`*)
val del (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) : Tot (t key value)

val iter_upd (#key:eqtype) (#value1 #value2: (key -> Tot Type)) (f : (k:key) -> value1 k -> value2 k) (m : t key value1) : t key value2

(** Creating a new map from a function *)
val create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k)))
    : Tot (t key value)

(** Restricts the domain of the map to those keys satisfying [p] *)
val restrict (#key: eqtype) (#value: (key -> Tot Type)) (s:S.set key) (m: t key value) : Tot (t key value)

(** The action of [sel] on [restrict] : the contents of the map isn't changed *)
val sel_restrict
      (#key: eqtype)
      (#value: (key -> Tot Type))
      (s:S.set key)
      (m: t key value)
      (k: key)
    : Lemma (ensures (sel (restrict s m) k == sel m k))

let const_on (#key:eqtype) (#value: (key -> Tot Type)) (dom:S.set key) (f: (k:key) -> value k) : t key value
  = restrict dom (create f)
  
(** Relating [create] to [sel] *)
val sel_create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k))) (k: key)
    : Lemma (ensures (sel #key #value (create f) k == f k)) [SMTPat (sel #key #value (create f) k)]
    
(** The action of selecting a key [k] a map with an updated value [v]
    at [k]

    This is one of the classic McCarthy select/update axioms in the
    setting of a dependent map.
    *)
val sel_upd_same (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k)
    : Lemma (ensures (sel (upd m k v) k == v)) [SMTPat (sel (upd m k v) k)]

(** The action of selecting a key [k] a map with an updated value [v]
    at a different key [k']

    This is one of the classic McCarthy select/update axioms in the
    setting of a dependent map.
    *)
val sel_upd_other
      (#key: eqtype)
      (#value: (key -> Tot Type))
      (m: t key value)
      (k: key)
      (v: value k)
      (k': key)
    : Lemma (requires (k' <> k))
      (ensures (sel (upd m k v) k' == sel m k'))
      [SMTPat (sel (upd m k v) k')]

val sel_IterUpd (#key:eqtype) (#value1 #value2: (key -> Tot Type)) (f : (k:key) -> value1 k -> value2 k) (m : t key value1) (k:key)
  : Lemma (ensures (sel (iter_upd f m) k == f k (sel m k)))
          [SMTPat (sel (iter_upd f m) k)]

val dom_create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k))) (k: key)
  : Lemma (requires True) 
          (ensures (contains (create f) k))
          [SMTPat (contains (create f) k)]
                         
val dom_upd_same (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k1 k2: key) (v: value k1)
  : Lemma (requires True) 
          (ensures (contains (upd m k1 v) k2 == (k1=k2 || contains m k2)))
          [SMTPat (contains (upd m k1 v) k2)]

val dom_upd_other (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k1 k2: key) (v: value k2)
  : Lemma (requires True) 
          (ensures (k2=!=k1 ==> contains (upd m k2 v) k1 == contains m k1))
          [SMTPat (contains (upd m k2 v) k1)]

val dom_IterUpd (#key:eqtype) (#value1 #value2: (key -> Tot Type)) (f : (k:key) -> value1 k -> value2 k) (m : t key value1) (k:key)
  : Lemma (ensures (contains (iter_upd f m) k == contains m k))
          [SMTPat (contains (iter_upd f m) k)]

val dom_contains (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key)
  : Lemma (requires True) 
          (ensures (contains m k = S.mem k (domain m)))
          [SMTPatOr[[SMTPat (contains m k)]; [SMTPat (S.mem k (domain m))]]]

val lemma_UpdDomain (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k)
  : Lemma (requires True)
          (ensures (S.equal (domain (upd m k v)) (S.union (domain m) (S.singleton k))))
          [SMTPat (domain (upd m k v))]

val dom_restrict (#key: eqtype)
      (#value: (key -> Tot Type))
      (s:S.set key)
      (m: t key value)
      (k: key)
      : Lemma (ensures (contains (restrict s m) k == (S.mem k s && contains m k)))
              [SMTPat (contains (restrict s m) k)]

val dom_const_on (#key: eqtype) (#value: (key -> Tot Type)) (k:key) (dom:S.set key) (f: (k:key) -> value k)
  : Lemma (requires True) 
          (ensures (contains (const_on dom f) k = S.mem k dom))
          [SMTPat (contains (const_on dom f) k)]
          
(** Extensional propositional equality on maps *)
val equal (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value) : prop

(** Introducing extensional equality by lifting equality on the map, pointwise *)
val equal_intro (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value)
    : Lemma (requires (forall k. sel m1 k == sel m2 k /\ contains m1 k = contains m2 k))
      (ensures (equal m1 m2))
      [SMTPat (equal m1 m2)]

val equal_elim (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value)
  : Lemma (ensures (equal m1 m2 <==> m1 == m2))
          [SMTPat (m1 == m2)]
                            
(** [equal] is reflexive *)
val equal_refl (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value)
    : Lemma (ensures (equal m m)) [SMTPat (equal m m)]

val equal_intro' (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value)
  : Lemma (requires (equal m1 m2))
          (ensures (forall k. sel m1 k == sel m2 k /\ contains m1 k = contains m2 k))
          [SMTPat (equal m1 m2)]
                                            
(** [equal] can be eliminated into standard propositional equality
    (==), also proving that it is an equivalence relation *)
//val equal_elim (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value)
  //  : Lemma (requires (equal m1 m2)) (ensures (m1 == m2)) [SMTPat (equal m1 m2)]

(**** Mapping a function over a dependent map *)

(** [map f m] applies f to each value in [m]'s co-domain *)
val map
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
    : Tot (t key value2)

(** The action of [sel] on [map] *)
val sel_map
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
      (k: key)
    : Lemma (ensures (sel (map f m) k == f k (sel m k)))
      [SMTPat (sel #key #value2 (map #key #value1 #value2 f m) k)]

(** [map] explained in terms of its action on [upd] *)
val map_upd
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
      (k: key)
      (v: value1 k)
    : Lemma (ensures (map f (upd m k v) == upd (map f m) k (f k v)))
      [
        //AR: wanted to write an SMTPatOr, but gives some error
        SMTPat (map #key #value1 #value2 f (upd #key #value1 m k v))
      ]

val dom_map (#key:eqtype) (#value1 #value2: (key -> Tot Type)) (f : (k:key) -> value1 k -> value2 k) (m : t key value1) (k:key)
  : Lemma (ensures (contains (map f m) k == contains m k))
          [SMTPat (contains (map f m) k)]
