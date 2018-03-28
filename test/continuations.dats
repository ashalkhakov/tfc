#include
"share/atspre_staload.hats"

staload "./../src/SATS/cont.sats"
staload _ = "./../src/DATS/cont.dats"

// example: two functions in CPS
fun f(x: int, k: cont(int)): void = resume(k, x + 1)
fun g(x: int, k: cont(int)): void = resume(k, x * 2)

// composition in CPS
fun f_then_g(x: int, k: cont(int)): void =
     resume(push(f, push(g, k)), x)

//
fun
fact2
(n : int, res: int): int =
if n > 0 then fact2(n-1, n*res) else res
//
fun
k_fact2
(n: int, res: int, k: cont(int)): void  =
if n > 0 then k_fact2(n-1, n*res, k) else resume(k,res)
//
fun
my_kfact (n:int, k: cont(int)): void = (println!("called with n=", n); k_fact2 (n, 1, k))

fun fact_after_fg (x:int, k:cont(int)): void =
    resume (
        push (f_then_g, push (my_kfact, k)),
        x
    )

implement
main0 () = {
  val () = fact_after_fg ((g0ofg1)1, dummy (lam (x: int): void => {
    val () = assertloc(eq_g0int_int(x, g0ofg1(24)))
  }))
}
