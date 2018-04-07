(* ****** ****** *)
//
// HX-2013-05:
// Effective ATS: Amortized Queue Implementation
//
(* ****** ****** *)
//
// How to test:
// ./queue-sllist2
// How to compile:
// patscc -DATS_MEMALLOC_LIBC -o queue-sllist2 queue-sllist2.dats
//
(* ****** ****** *)

absvtype
queue_vtype (a:viewt@ype+, n:int) = ptr

(* ****** ****** *)

vtypedef
queue (a:vt0p, n:int) = queue_vtype (a, n)

(* ****** ****** *)

praxi
lemma_queue_param
  {a:vt0p}{n:int} (x: !queue (INV(a), n)): [n >= 0] void
// end of [lemma_queue_param]

(* ****** ****** *)

fun{} queue_make_nil {a:vt0p} (): queue (a, 0)
fun{} queue_free_nil {a:vt0p} (que: queue (a, 0)): void

(* ****** ****** *)
//
fun{} queue_is_empty
  {a:vt0p}{n:int} (que: !queue (INV(a), n)): bool (n==0)
fun{} queue_isnot_empty
  {a:vt0p}{n:int} (que: !queue (INV(a), n)): bool (n > 0)
//
(* ****** ****** *)

fun{a:vt0p}
queue_insert_atend{n:int}
  (que: !queue (INV(a), n) >> queue (a, n+1), x: a): void
// end of [queue_insert_atend]

fun{a:vt0p}
queue_takeout_atbeg
  {n:pos} (que: !queue (INV(a), n) >> queue (a, n-1)): (a)
