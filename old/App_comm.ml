open Prims
type concrete_st = (Prims.nat * Prims.nat) FStar_Set.set
let init_st : 'uuuuu . unit -> 'uuuuu FStar_Set.set =
  fun uu___ -> FStar_Set.empty ()
type ('a, 'b) eq = unit



type app_op_t =
  | Add of Prims.nat 
  | Rem of Prims.nat 
let (uu___is_Add : app_op_t -> Prims.bool) =
  fun projectee -> match projectee with | Add _0 -> true | uu___ -> false
let (__proj__Add__item___0 : app_op_t -> Prims.nat) =
  fun projectee -> match projectee with | Add _0 -> _0
let (uu___is_Rem : app_op_t -> Prims.bool) =
  fun projectee -> match projectee with | Rem _0 -> true | uu___ -> false
let (__proj__Rem__item___0 : app_op_t -> Prims.nat) =
  fun projectee -> match projectee with | Rem _0 -> _0
type ('l, 'a, 'b) concrete_merge_pre1 = unit
let remove_if :
  'a . 'a FStar_Set.set -> ('a -> Prims.bool) -> 'a FStar_Set.set =
  fun s -> fun f -> failwith "Not yet implemented:remove_if"
let filter_s :
  'a . 'a FStar_Set.set -> ('a -> Prims.bool) -> 'a FStar_Set.set =
  fun s -> fun f -> failwith "Not yet implemented:filter_s"
let exists_s : 'a . 'a FStar_Set.set -> ('a -> Prims.bool) -> Prims.bool =
  fun s -> fun f -> failwith "Not yet implemented:exists_s"
let (mem_ele : Prims.nat -> concrete_st -> Prims.bool) =
  fun ele ->
    fun s -> exists_s s (fun e -> (FStar_Pervasives_Native.snd e) = ele)
let (concrete_merge1 :
  concrete_st -> concrete_st -> concrete_st -> concrete_st) =
  fun l ->
    fun a ->
      fun b ->
        let i_la = FStar_Set.intersect l a in
        let i_lab = FStar_Set.intersect i_la b in
        let da = remove_if a (fun e -> FStar_Set.mem e l) in
        let db = remove_if b (fun e -> FStar_Set.mem e l) in
        let da1 =
          filter_s da
            (fun e ->
               Prims.op_Negation
                 (exists_s db
                    (fun e1 ->
                       ((FStar_Pervasives_Native.snd e) =
                          (FStar_Pervasives_Native.snd e1))
                         &&
                         ((FStar_Pervasives_Native.fst e1) >
                            (FStar_Pervasives_Native.fst e))))) in
        let db1 =
          filter_s db
            (fun e ->
               Prims.op_Negation
                 (exists_s da
                    (fun e1 ->
                       ((FStar_Pervasives_Native.snd e) =
                          (FStar_Pervasives_Native.snd e1))
                         &&
                         ((FStar_Pervasives_Native.fst e1) >=
                            (FStar_Pervasives_Native.fst e))))) in
        let da_not_in_db =
          remove_if da (fun e -> mem_ele (FStar_Pervasives_Native.snd e) db) in
        let db_not_in_da =
          remove_if db (fun e -> mem_ele (FStar_Pervasives_Native.snd e) da) in
        let u1 = FStar_Set.union i_lab (FStar_Set.union da1 db1) in
        let u2 = FStar_Set.union da_not_in_db db_not_in_da in
        FStar_Set.union u1 u2