#include
"share/atspre_staload.hats"

staload "./../src/SATS/heaparray.sats"
staload _ = "./../src/DATS/heaparray.dats"

implement main0 () = let
  typedef T = int

  implement
  mycompare<T>(x,y) = (x >= y)

  var h: heap (T, 0, 0, null)

  val () = heap_init (h, (i2sz)10)
  val () = heap_push (h, 5)
  val () = heap_push (h, 4)
  val () = heap_push (h, 3)
  val () = heap_push (h, 100)
  val () = heap_push (h, 6)
  val () = heap_push (h, 10)

  val () = assertloc (100 = heap_front (h))
  val () = heap_pop (h)
  val () = assertloc (10 = heap_front (h))
  val () = heap_pop (h)
  val () = assertloc (6 = heap_front (h))
  val () = heap_pop (h)
  val () = assertloc (5 = heap_front (h))
  val () = heap_pop (h)
  val () = assertloc (4 = heap_front (h))
  val () = heap_pop (h)
  val () = assertloc (3 = heap_front (h))
  val () = heap_pop (h)
  
  val () = heap_resize (h, (i2sz)100)

  val () = heap_term (h)
  
  var p_arr = @[int](5,4,3,100,6,10)
  val () = heapify (p_arr, (i2sz)6)
  val () = assertloc (100 = p_arr.[0])
  val () = assertloc (6 = p_arr.[1])
  val () = assertloc (10 = p_arr.[2])
  val () = assertloc (4 = p_arr.[3])
  val () = assertloc (5 = p_arr.[4])
  val () = assertloc (3 = p_arr.[5])
in

end