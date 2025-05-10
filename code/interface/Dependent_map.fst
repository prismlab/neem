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
open Set_extended
module S = Set_extended
open FStar.FunctionalExtensionality

module F = FStar.FunctionalExtensionality
noeq
type t (key: eqtype) (value: (key -> Type)) =
  { mappings:F.restricted_t key value;
    domain:S.t key
  }

let domain (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) : Tot (S.t key) =
  m.domain

let contains (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) : Tot bool =
  S.mem k m.domain

let sel (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) : Tot (value k) =
  m.mappings k

let upd (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k)
    : Tot (t key value) =
  { mappings = F.on_domain key (fun k' -> if k' = k then v else m.mappings k');
    domain = S.union m.domain (S.singleton k)
  }

let del(#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) : t key value =
  { mappings = F.on_domain key (fun x -> m.mappings x);
    domain = S.remove (domain m) k
  }

let iter_upd (#key:eqtype) (#value1 #value2: (key -> Tot Type)) (f : (k:key) -> value1 k -> value2 k) (m : t key value1) : t key value2 =
  { mappings = F.on_domain key (fun x -> f x (m.mappings x));
    domain =   m.domain
  }

let create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k))) : Tot (t key value) =
  { mappings = F.on_domain key f;
    domain = complement empty
  }

let restrict (#key: eqtype) (#value: (key -> Tot Type)) (s:S.t key) (m: t key value) =
  { mappings = m.mappings;
    domain =   S.intersection s m.domain
  }

let sel_restrict
      (#key: eqtype)
      (#value: (key -> Tot Type))
      (s:S.t key)
      (m: t key value)
      (k: key) = ()

let sel_create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k))) (k: key)
    : Lemma (requires True)
      (ensures (sel #key #value (create f) k == f k))
      [SMTPat (sel #key #value (create f) k)] = ()

let sel_upd_same (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k) = ()

let sel_upd_other
      (#key: eqtype)
      (#value: (key -> Tot Type))
      (m: t key value)
      (k: key)
      (v: value k)
      (k': key) = ()

let sel_IterUpd (#key:eqtype) (#value1 #value2: (key -> Tot Type)) (f : (k:key) -> value1 k -> value2 k) (m : t key value1) (k:key) = ()

let dom_create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k))) (k: key) = ()

let dom_upd_same (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k1 k2: key) (v: value k1) = ()

let dom_upd_other (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k1 k2: key) (v: value k2) = ()

let dom_IterUpd (#key:eqtype) (#value1 #value2: (key -> Tot Type)) (f : (k:key) -> value1 k -> value2 k) (m : t key value1) (k:key) = ()

let dom_contains (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) = ()

let lemma_UpdDomain (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k) = ()

let dom_restrict (#key: eqtype)
      (#value: (key -> Tot Type))
      (s:S.t key)
      (m: t key value)
      (k: key)
      : Lemma (ensures (contains (restrict s m) k == (S.mem k s && contains m k))) = ()

let dom_const_on (#key: eqtype) (#value: (key -> Tot Type)) (k:key) (dom:S.t key) (f: (k:key) -> value k) = ()

let equal (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value) =
  F.feq m1.mappings m2.mappings /\
  S.equal m1.domain m2.domain

let equal_intro (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value) = ()
let equal_elim (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value) = ()
let equal_refl (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) = ()
let equal_intro' (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value) = ()

let map
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
    : Tot (t key value2) =
    { mappings = F.on_domain key (fun k -> f k (sel m k));
      domain = m.domain }

let sel_map
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
      (k: key)
     = ()

let map_upd
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
      (k: key)
      (v: value1 k)
     = equal_elim #key #value2 (map f (upd m k v)) (upd (map f m) k (f k v))

let dom_map (#key:eqtype) (#value1 #value2: (key -> Tot Type)) (f : (k:key) -> value1 k -> value2 k) (m : t key value1) (k:key) = ()
