(* ****** ****** *)
//
// HX-2013-05:
// Effective ATS: Amortized Queue Implementation
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

staload "./../SATS/queue_sllist2.sats"

(* ****** ****** *)

local

staload "libats/SATS/sllist.sats"

dataviewtype
queue (a:viewt@ype+, n:int) =
  {f,r:nat | f+r==n} QUEUE of (sllist (a, f), sllist (a, r))
// end of [queue]

assume queue_vtype (a, n) = queue (a, n)

in (* in of [local] *)

implement{}
queue_make_nil () = QUEUE (sllist_nil (), sllist_nil ())

implement{}
queue_free_nil (que) = let
//
val+~QUEUE (f, r) = que
//
prval () = lemma_sllist_param (f)
prval () = lemma_sllist_param (r)
//
prval () = sllist_free_nil (f)
prval () = sllist_free_nil (r)
//
in
  // nothing
end // end of [queue_free_nil]

implement{}
queue_is_empty (que) = let
  val+QUEUE (f, r) = que
in
  if sllist_is_nil (f) then sllist_is_nil (r) else false
end // end of [queue_is_empty]

implement{}
queue_isnot_empty (que) = let
  val+QUEUE (f, r) = que
in
  if sllist_is_cons (f) then true else sllist_is_cons (r)
end // end of [queue_isnot_empty]

implement{a}
queue_insert_atend
  (que, x) = let
//
val+@QUEUE (f, r) = que
val () = r := sllist_cons (x, r)
prval () = fold@ (que)
//
in
  // nothing
end // end of [queue_insert_atend]

implement{a}
queue_takeout_atbeg
  (que) = let
//
val+@QUEUE (f, r) = que
//
prval () = lemma_sllist_param (f)
prval () = lemma_sllist_param (r)
//
val iscons = sllist_is_cons (f)
//
in
//
if iscons then let
  val x = sllist_uncons (f)
  prval () = fold@ (que)
in
  x
end else let
  prval () = sllist_free_nil (f)
  val () = f := sllist_reverse (r)
  val () = r := sllist_nil {a} ()
  val x = sllist_uncons (f)
  prval () = fold@ (que)
in
  x
end // end of [if]
//
end // end of [queue_takeout_atbeg]

end // end of [local]

