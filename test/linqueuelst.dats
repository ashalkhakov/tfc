#include
"share/atspre_staload.hats"

staload "./../src/SATS/linqueuelst_vt.sats"
staload _ = "./../src/DATS/linqueuelst_vt.dats"

overload queue_create with linqueuelst_nil
overload enqueue with linqueuelst_enqueue
overload dequeue with linqueuelst_dequeue
overload queue_free with linqueuelst_free

fun test_eq1 (): void = {
  var xs = queue_create()
  val () = enqueue(xs, 1)
  val () = enqueue(xs, 2)
  val () = assertloc ((1:int) = dequeue(xs))
  val () = enqueue(xs, 3)
  val () = assertloc ((2:int) = dequeue(xs))
  val () = assertloc ((3:int) = dequeue(xs))
  val () = queue_free (xs)
}

implement
main0 () = {
  val () = test_eq1 ()
}
