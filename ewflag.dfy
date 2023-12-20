datatype pair = Cf(int, bool)
type concrete_st = map<nat, pair>
datatype app_op_t = Enable | Disable
datatype tup = Tup(nat, app_op_t)
datatype op_t = Opt(nat, tup)

function GetCtr (cf:pair) : int
{
    match cf { 
        case Cf(c,_) => c }
}

function GetFlag (cf:pair) : bool
{
    match cf {
        case Cf(_,f) => f }
}

function GetTs(t: op_t): nat
{
    match t {
        case Opt(ts, _) => ts }
}

function GetRid(t: op_t): nat
{
    match t {
        case Opt(_, Tup(rid, _)) => rid }
}

function GetOp(t: op_t): app_op_t
{
    match t {
        case Opt(_, Tup(_, op)) => op }
}

datatype rc_res = 
  | Fst_then_snd
  | Snd_then_fst
  | Either

function GetInitState(): concrete_st { map[] }

function distinct_ops(o1: op_t, o2: op_t): bool
{ 
    GetTs(o1) != GetTs(o2) 
}

function DisableAll(m:concrete_st) : concrete_st
{
  var res:= map k | k in m.Keys :: Cf(GetCtr(m[k]), false);
  res
}

function do(s: concrete_st, o: op_t): concrete_st
{ 
    match (GetOp(o)) {
        case Enable => if (GetRid(o)) in s then s[GetRid(o) := Cf(GetCtr(s[GetRid(o)]) + 1, true)] else s[GetRid(o) := Cf(1, true)]
        case Disable => DisableAll(s)
    }
}

method symmetric(a: concrete_st, b: concrete_st)
    requires a == b
    ensures b == a
{
    assert b == a;
}

function rc(o1:op_t, o2:op_t) : rc_res 
{ 
    if GetOp(o1) == Enable && GetOp(o2) == Disable then Snd_then_fst
    else if GetOp(o1) == Disable && GetOp(o2) == Enable then Fst_then_snd
    else Either
}

function merge_flag(l:pair, a:pair, b:pair): bool
{
    var lc := GetCtr(l);
    var ac := GetCtr(a);
    var bc := GetCtr(b);
    var af := GetFlag(a);
    var bf := GetFlag(b);
    if af && bf then true
    else if !af && !bf then false
    else if af then ac > lc
    else bc > lc
}

function merge_cf(l: pair, a: pair, b: pair): pair
{
    Cf(GetCtr(a) + GetCtr(b) - GetCtr(l), merge_flag(l,a,b))
}

function merge(l: concrete_st, a: concrete_st, b: concrete_st): concrete_st
{
    var keys := l.Keys + a.Keys + b.Keys;
    var m := map k | k in keys :: (var lk := if k in l then l[k] else Cf(0, false);
                                   var ak := if k in a then a[k] else Cf(0, false);
                                   var bk := if k in b then b[k] else Cf(0, false);
                          merge_cf(lk, ak, bk));
    m
}

method no_rc_chain (o1:op_t, o2:op_t, o3:op_t)
    requires distinct_ops(o1,o2) && distinct_ops(o2,o3)
    ensures !(rc(o1,o2) == Fst_then_snd && rc(o2,o3) == Fst_then_snd)
{
    assert !(rc(o1,o2) == Fst_then_snd && rc(o2,o3) == Fst_then_snd);
}

method relaxed_comm (s:concrete_st, o1:op_t, o2:op_t, o3:op_t)
    requires distinct_ops(o1,o2) && distinct_ops(o2,o3) && rc(o1,o2) == Fst_then_snd && rc(o2,o3) != Either
    ensures do(do(do(s,o1),o2),o3) == do(do(do(s,o2),o1),o3)
{
    assert do(do(do(s,o1),o2),o3) == do(do(do(s,o2),o1),o3);
}

method merge_comm(l: concrete_st, a: concrete_st, b: concrete_st)
    ensures merge(l,a,b) == merge(l,b,a)
{
    assert merge(l,a,b) == merge(l,b,a);
}

function merge_pre(l:concrete_st, a: concrete_st, b: concrete_st): bool
{
    forall id :: (id in l.Keys ==> (id in a.Keys && id in b.Keys &&
                                GetCtr(a[id]) >= GetCtr(l[id]) && GetCtr(b[id]) >= GetCtr(l[id])))
}

method {:verify true} rc_ind_left(l:concrete_st, a: concrete_st, b: concrete_st, o1:op_t, o1':op_t, o2:op_t) 
    requires merge(l,do(a,o1),do(b,o2)) == do(merge(l,do(a,o1),b),o2) 
            && (rc(o1,o2) == Fst_then_snd)
            /*&& merge_pre(l,do(do(a,o1'),o1),do(b,o2)) && merge_pre(l,do(do(a,o1'),o1),b) 
            && merge_pre(l,do(a,o1),do(b,o2)) && merge_pre(l,do(a,o1),b)
            && l == GetInitState() && a == l 
            && b == map[1328 := Cf(-7036,false), 5904 := Cf(1192,false), 4894 := Cf(1288,false), 1289 := Cf(6391,false)]
            && o1 == Opt(1,Tup(1695,Disable)) && o2 == Opt(2,Tup(1328,Enable)) && o1' == Opt(3,Tup(1289,Enable))*/
    ensures merge(l,do(do(a,o1'),o1),do(b,o2)) == do((merge(l,do(do(a,o1'),o1),b)),o2)
{
    assert merge(l,do(do(a,o1'),o1),do(b,o2)) == do((merge(l,do(do(a,o1'),o1),b)),o2);
}

method {:test} print1() {
    print merge(GetInitState(),
               do(GetInitState(),Opt(1,Tup(1695,Disable))),
               do(map[1328 := Cf(-7036,false), 5904 := Cf(1192,false), 4894 := Cf(1288,false), 1289 := Cf(6391,false)],Opt(2,Tup(1328,Enable)))), "\n";
}

method {:test} print2() {
    print do((merge(GetInitState(),
                    do(GetInitState(),Opt(1,Tup(1695,Disable))),
                    map[1328 := Cf(-7036,false), 5904 := Cf(1192,false), 4894 := Cf(1288,false), 1289 := Cf(6391,false)])),Opt(2,Tup(1328,Enable))), "\n";
}

method {:test} print3() {
    print merge(GetInitState(), 
                do(do(GetInitState(), Opt(3,Tup(1289,Enable))), Opt(1,Tup(1695,Disable))), 
                do(map[1328 := Cf(-7036,false), 5904 := Cf(1192,false), 4894 := Cf(1288,false), 1289 := Cf(6391,false)], Opt(2,Tup(1328,Enable)))), "\n";
} 

method {:test} print4() {
    print do(merge(GetInitState(),
                   do((do(GetInitState(),Opt(3,Tup(1289,Enable)))),Opt(1,Tup(1695,Disable))),
                   map[1328 := Cf(-7036,false), 5904 := Cf(1192,false), 4894 := Cf(1288,false), 1289 := Cf(6391,false)]),Opt(2,Tup(1328,Enable))), "\n";
}
