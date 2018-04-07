#include
"share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

staload "./../SATS/sched.sats"
staload "./../SATS/cont.sats"

staload _ = "./../DATS/cont.dats"

staload _ = "prelude/DATS/reference.dats"
staload _ = "prelude/DATS/pointer.dats"

staload "./../SATS/queue_sllist2.sats"
staload _ = "./queue_sllist2.dats"
staload _ = "libats/DATS/gnode.dats"
staload _ = "libats/DATS/sllist.dats"

(* ****** ****** *)

absvtype thread_t = ptr

local

vtypedef sthread_t = () -<lincloptr1> void
assume thread_t = sthread_t

in // in of [local]

fun{v:vtype;r:vt@ype}
thread_make (
  env: v, tfn: (v, cont(r)) -> void, k: cont(r)
): thread_t = lam (): void =<lincloptr1> tfn (env, k)

fun
thread_run (thr: thread_t) = let
  val () = thr ()
  val () = cloptr_free ($UN.castvwtp0{cloptr0}(thr))
in
end

end // end of [local]

(* ****** ****** *)

extern
fun
myenqueue (t: thread_t): void

local

vtypedef sched = [n:int] queue (thread_t, n)

var the_threads : sched = queue_make_nil{thread_t}()
val threads : ref(sched) = ref_make_viewptr {sched} (
  view@ the_threads | addr@ the_threads
)

implement
myenqueue (t) = let
  val (vbox pf | p) = (ref_get_viewptr {sched} (threads))
  val () = $effmask_ref (queue_insert_atend (!p, t))
in
end

in // in of [local]

implement{v,r}
yield (env, tfn, k) = let
  val thr = thread_make<v,r> (env, tfn, k)
  val () = myenqueue (thr)
in
end

(* ****** ****** *)

implement
mainloop () = {
  fun
  loop {n:int} (
    q: !queue (thread_t, n) >> queue (thread_t, 0)
  ): void = let
    prval () = lemma_queue_param (q)
  in
    if queue_is_empty q then ()
    else let
       var thr = queue_takeout_atbeg (q)
       val () = thread_run (thr)
       val () = loop (q)
    in
    end
  end // end of [loop]

  val (vbox pf | p) = $effmask_ref (ref_get_viewptr {sched} (threads))
  val () = $effmask_ref (loop (!p))

} (* end of [mainloop] *)

end // end of [local]

(* ****** ****** *)
