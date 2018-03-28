#include
"share/atspre_staload.hats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

staload "./../SATS/cont.sats"

local

staload UN = "prelude/SATS/unsafe.sats"

vtypedef kont(a:vt@ype) = a -<lincloptr1> void
assume cont(a:vt@ype) = kont(a)

in // in of [local]

implement{a}
dummy (f) = lam (x) =<lincloptr1> f (x)

implement{a}
resume (k, x) = {
    val () = k(x)
    val () = cloptr_free ($UN.castvwtp0{cloptr0}(k))
}

implement{a,b}
push (m, k) = lam (n) =<lincloptr1> m (n, k)

end // end of [local]
