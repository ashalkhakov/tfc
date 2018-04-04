#include
"share/atspre_staload.hats"

staload "./../src/SATS/cont.sats"
staload "./../src/SATS/sched.sats"
staload _ = "./../src/DATS/cont.dats"
staload _ = "./../src/DATS/sched.dats"

staload _ = "prelude/DATS/reference.dats"

fun thread0(p: int, k: cont(int)): void = let
  datavtype mystate = started of int | running of int

  fun aux (state: mystate, k: cont(int)): void =
    case+ state of
    | ~started n => {
        val () = println!("n= ", n)
        val n= n+1
        // this suspends the thread!
        val () = yield (running n, aux, k)
      }
   | ~running n => {
       val n = n * 2
       val () = println!("changing n to ", n)
       val () = resume (k, n)
     }
in
  yield (started p, aux, k)
end

dynload "./../src/DATS/sched.dats"

implement
main0 () = let
  // parallel execution
  val () = thread0 (0, dummy<int> (lam (r: int): void => let
    val () = assertloc (r = g0ofg1(2))
  in
    
  end))
  val () = thread0 (1, dummy<int> (lam (r: int): void => let
    val () = assertloc (r = g0ofg1(4))    
  in
    
  end))
  val () = mainloop ()
in
end