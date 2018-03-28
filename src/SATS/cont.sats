(*
from https://www.irif.fr/~jch/cpc.pdf
see also https://github.com/kerneis/cpc

continuation: k : a -> void, for some type a

continuation as a linear adt:
*)

absvtype cont(a:vt@ype) = ptr

vtypedef kfun(a:vt@ype, b:vt@ype) = (a, cont(b)) -> void

// need some base case here no?
fun{a:t@ype}
dummy (INV(a) -> void): cont(a)

// calling a continuation
fun{a:vt@ype}
resume(k : cont(a), x : INV(a)): void // = k(x)
// prepend a funapp to the body of continuation
fun{a,b:vt@ype}
push(m: kfun(INV(b), a), k: cont(INV(a))): cont(b) // = lam (n:b) => m (n, k)

(* schematically:
push(f, x1,..,xn,k) = f(x1,..,xn) . k
resume((f,x1,...,xn) . k,y1,...,ym) = f(x1,..,xn,y1,...,ym,k)
*)
