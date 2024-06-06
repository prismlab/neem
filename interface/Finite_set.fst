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

let has_elements (#a: eqtype) (f: a ^-> bool) (xs: list a): prop =
  forall x. f x == x `FLT.mem` xs

let t (a:eqtype) = f:(a ^-> bool){exists xs. f `has_elements` xs}

let rec remove_repeats (#a: eqtype) (xs: list a)
: (ys: list a{list_nonrepeating ys /\ (forall y. FLT.mem y ys <==> FLT.mem y xs)}) =
  match xs with
  | [] -> []
  | hd :: tl -> let tl' = remove_repeats tl in if FLT.mem hd tl then tl' else hd :: tl'

let mem #a x s = s x

let set_as_list (#a: eqtype) (s: t a): GTot (xs: list a{list_nonrepeating xs /\ (forall x. FLT.mem x xs = mem x s)}) =
  remove_repeats (FStar.IndefiniteDescription.indefinite_description_ghost (list a) (fun xs -> forall x. FLT.mem x xs = mem x s))
  
let intro_set (#a: eqtype) (f: a ^-> bool) (xs: Ghost.erased (list a))
: Pure (t a)
    (requires f `has_elements` xs)
    (ensures fun _ -> True)
= Classical.exists_intro (fun xs -> f `has_elements` xs) xs;
  f 
  
let empty #a = intro_set (on_dom a (fun _ -> false)) []

let insert (#a: eqtype) (x: a) (s: t a): t a =
  intro_set (on_dom _ (fun x' -> x = x' || s x')) (x :: set_as_list s)

let singleton #a x = insert x empty
let equal #a s1 s2 = feq s1 s2

let rec union_lists (#a: eqtype) (xs: list a) (ys: list a) : (zs: list a{forall z. FLT.mem z zs <==> FLT.mem z xs \/ FLT.mem z ys}) =
  match xs with
  | [] -> ys
  | hd :: tl -> hd :: union_lists tl ys
  
let union #a s1 s2 = intro_set (on_dom a (fun x -> s1 x || s2 x)) (union_lists (set_as_list s1) (set_as_list s2))

let rec intersect_lists (#a: eqtype) (xs: list a) (ys: list a)
: (zs: list a{forall z. FLT.mem z zs <==> FLT.mem z xs /\ FLT.mem z ys}) =
  match xs with
  | [] -> []
  | hd :: tl -> let zs' = intersect_lists tl ys in if FLT.mem hd ys then hd :: zs' else zs'

let intersection #a s1 s2 = intro_set (on_dom a (fun x -> s1 x && s2 x)) (intersect_lists (set_as_list s1) (set_as_list s2))

//let complement #a s = F.on_dom a (fun x -> not (s x))

let rec difference_lists (#a: eqtype) (xs: list a) (ys: list a)
: (zs: list a{forall z. FLT.mem z zs <==> FLT.mem z xs /\ ~(FLT.mem z ys)}) =
  match xs with
  | [] -> []
  | hd :: tl -> let zs' = difference_lists tl ys in if FLT.mem hd ys then zs' else hd :: zs'
  
let difference #a s1 s2 = intro_set (on_dom a (fun x -> s1 x && not (s2 x))) (difference_lists (set_as_list s1) (set_as_list s2))

let rec filter_lists (#a: eqtype) (xs: list a) (p: a -> bool)
: (zs: list a{forall z. FLT.mem z zs <==> FLT.mem z xs /\ p z}) =
  match xs with
  | [] -> []
  | hd :: tl -> let zs' = filter_lists tl p in if p hd then hd::zs' else zs'
  
let filter #a s1 p = intro_set (on_dom a (fun x -> s1 x && p x)) (filter_lists (set_as_list s1) p)

let rec remove_lists (#a: eqtype) (xs: list a) (x: a)
: (zs: list a{forall z. FLT.mem z zs <==> FLT.mem z xs /\ z <> x}) =
  match xs with
  | [] -> []
  | hd :: tl -> let zs' = remove_lists tl x in if hd = x then zs' else hd::zs'
  
let remove #a s1 y = intro_set (on_dom a (fun x -> s1 x && x <> y)) (remove_lists (set_as_list s1) y)

[@"opaque_to_smt"]
let cardinality (#a: eqtype) (s: t a) : GTot nat =
  FLT.length (set_as_list s)

let choose (#a: eqtype) (s: t a{exists x. mem x s}) : GTot (x: a{mem x s}) =
  Cons?.hd (set_as_list s)
  
let mem_empty #a x = ()
let equal_intro #a s1 s2 = ()
let equal_intro' #a s1 s2 = ()
let equal_elim #a s1 s2 = () 
let insert_mem # a x s = ()
let mem_subset #a s1 s2 = ()
let subset_mem #a s1 s2 = ()
let mem_union #a s1 s2 x = ()
let mem_singleton #a x y = ()
let mem_intersection #a s1 s2 x = ()
let mem_complement #a s x = ()
let mem_difference #a s1 s2 x = ()
let mem_filter #a s p x = ()
let mem_remove_x #a s x = ()
let mem_remove_y #a s x y = ()
