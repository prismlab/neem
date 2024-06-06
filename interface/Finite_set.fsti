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
finite sets as they're modeled in Dafny.

@summary Type and functions for modeling finite sets
*)

module Finite_set
module FLT = FStar.List.Tot
open FStar.FunctionalExtensionality

//8248157467

val t (a:eqtype) : Type0

let rec list_nonrepeating (#a: eqtype) (xs: list a) : bool =
  match xs with
  | [] -> true
  | hd :: tl -> not (FLT.mem hd tl) && list_nonrepeating tl

val mem (#a:eqtype) (x:a) (s:t a) : bool
val empty (#a:eqtype) : t a
val singleton (#a:eqtype) (x:a) : t a
val equal (#a:eqtype) (s1:t a) (s2:t a) : Type0
val union (#a:eqtype) (s1 s2:t a) : t a
val intersection (#a:eqtype) (s1 s2:t a) : t a
//val complement : #a:eqtype -> (s:t a) -> t a
val difference (#a:eqtype) (s1 s2:t a) : t a
val filter (#a:eqtype) (s:t a) (p:a -> bool) : t a
val remove (#a:eqtype) (s:t a) (x:a) : t a
val cardinality (#a:eqtype) (s:t a) : GTot nat
val choose (#a:eqtype) (s:t a{exists x. mem x s}) : GTot (x:a{mem x s})
  
val mem_empty (#a:eqtype) (x:a)
  : Lemma (not (mem x empty))
          [SMTPat (mem x empty)]

val equal_intro (#a:eqtype) (s1 s2:t a)
  : Lemma (requires (forall (x:a). mem x s1 == mem x s2))
          (ensures equal s1 s2)
          [SMTPat (equal s1 s2)]

val equal_intro' (#a:eqtype) (s1 s2:t a)
  : Lemma (ensures equal s1 s2 <==> s1 == s2)
          [SMTPat (s1 == s2)]
          
val equal_elim (#a:eqtype) (s1 s2:t a)
  : Lemma (requires equal s1 s2)
          (ensures s1 == s2)
          [SMTPat (equal s1 s2)]

let equal_refl (#a:eqtype) (s1 s2:t a)
  : Lemma (requires s1 == s2)
          (ensures (forall (x:a). mem x s1 == mem x s2) /\ equal s1 s2)
          [SMTPat (s1 == s2)] = ()
          
let equal_refl1 (#a:eqtype) (s:t a)
  : Lemma (equal s s) = ()

let subset (#a:eqtype) (s1:t a) (s2:t a) =
  (forall x. mem x s1 ==> mem x s2)

val mem_subset (#a:eqtype) (s1:t a) (s2:t a)
  : Lemma (requires (forall x. mem x s1 ==> mem x s2))
          (ensures (subset s1 s2))
          [SMTPat (subset s1 s2)]

val subset_mem (#a:eqtype) (s1:t a) (s2:t a)
  : Lemma (requires (subset s1 s2))
          (ensures (forall x. mem x s1 ==> mem x s2))
          [SMTPat (subset s1 s2)]
   
val mem_union (#a:eqtype) (s1 s2:t a) (x:a)
  : Lemma (mem x (union s1 s2) <==> (mem x s1 || mem x s2))
          [SMTPat (mem x (union s1 s2))]

val mem_singleton (#a:eqtype) (x y:a)
  : Lemma (mem y (singleton x) = (x=y))
          [SMTPat (mem y (singleton x))]
   
let add (#a:eqtype) (x:a) (s:t a) : t a =
  union s (singleton x)

val mem_intersection (#a:eqtype) (s1 s2:t a) (x:a)
  : Lemma (mem x (intersection s1 s2) <==> (mem x s1 /\ mem x s2))
          [SMTPat (mem x (intersection s1 s2))]

(*val mem_complement (#a:eqtype) (s:t a) (x:a) 
  : Lemma (mem x (complement s) = not (mem x s))
          [SMTPat (mem x (complement s))]*)
   
val mem_difference (#a:eqtype) (s1 s2:t a) (x:a)
  : Lemma (mem x (difference s1 s2) <==> (mem x s1 /\ ~ (mem x s2)))
          [SMTPat (mem x (difference s1 s2))]
   
val mem_filter (#a:eqtype) (s:t a) (p:a -> bool) (x:a)
  : Lemma (mem x (filter s p) <==> (mem x s /\ p x))
          [SMTPat (mem x (filter s p))]

val mem_remove_x (#a:eqtype) (s:t a) (x:a)
  : Lemma (not (mem x (remove s x)))
          [SMTPat (mem x (remove s x))]

val mem_remove_y (#a:eqtype) (s:t a) (x:a) (y:a)
  : Lemma (requires x =!= y)
          (ensures mem y (remove s x) == mem y s)
          [SMTPat (mem y (remove s x))]
          
val length_zero_fact (#a:eqtype) (s:t a)
  : Lemma (ensures (cardinality s = 0 <==> s == empty) /\ (cardinality s <> 0 <==> (exists x. mem x s)))
          [SMTPat (cardinality s)]

val singleton_cardinality_fact (#a:eqtype) (r:a)
  : Lemma (ensures cardinality (singleton r) = 1)
          [SMTPat (cardinality (singleton r))]

val intersection_cardinality_fact (#a:eqtype) (s1 s2:t a)
  : Lemma (ensures cardinality (union s1 s2) + cardinality (intersection s1 s2) = cardinality s1 + cardinality s2)
          [SMTPat (cardinality (intersection s1 s2))]
    
val difference_cardinality_fact (#a:eqtype) (s1 s2:t a)
  : Lemma (ensures cardinality (difference s1 s2) + cardinality (difference s2 s1) + cardinality (intersection s1 s2) = cardinality (union s1 s2)
    /\ cardinality (difference s1 s2) = cardinality s1 - cardinality (intersection s1 s2))
          [SMTPat (cardinality (difference s1 s2))]

val union_cardinality_fact (#a:eqtype) (s1 s2:t a)
  : Lemma (ensures cardinality (difference s1 s2) + cardinality (difference s2 s1) + cardinality (intersection s1 s2) = cardinality (union s1 s2)
    /\ cardinality (difference s1 s2) = cardinality s1 - cardinality (intersection s1 s2))
          [SMTPat (cardinality (union s1 s2))]
    
