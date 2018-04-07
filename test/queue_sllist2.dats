(* ****** ****** *)
//
#include
"share/atspre_staload.hats"
//
(* ****** ****** *)

staload "./../src/SATS/queue_sllist2.sats"
staload _ = "./../src/DATS/queue_sllist2.dats"

staload _ = "libats/DATS/gnode.dats"
staload _ = "libats/DATS/sllist.dats"

(* ****** ****** *)

implement
main0 () =
{
//
typedef T = int
//
val Q = queue_make_nil {T} ()
//
val () = queue_insert_atend (Q, 0)
val () = queue_insert_atend (Q, 1)
val () = assertloc (0 = queue_takeout_atbeg (Q))
val () = assertloc (1 = queue_takeout_atbeg (Q))
//
val () = queue_insert_atend (Q, 2)
val () = queue_insert_atend (Q, 3)
val () = queue_insert_atend (Q, 4)
val () = assertloc (2 = queue_takeout_atbeg (Q))
val () = assertloc (3 = queue_takeout_atbeg (Q))
val () = assertloc (4 = queue_takeout_atbeg (Q))
//
val () = queue_free_nil (Q)
//
} // end of [main0]

(* ****** ****** *)

(* end of [queue-sllist2.dats] *)
