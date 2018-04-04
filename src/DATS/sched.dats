#include
"share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

staload "./../SATS/sched.sats"
staload "./../SATS/cont.sats"

staload _ = "./../DATS/cont.dats"

staload _ = "prelude/DATS/reference.dats"
staload _ = "prelude/DATS/pointer.dats"

(* ****** ****** *)

absvtype queue (vt@ype+) = ptr
extern
fun
queue_nil {a:vtype} (): queue (a)
extern
fun
enqueue {a:vtype} (&queue(INV(a)) >> queue(a), a): void
extern
fun
dequeue {a:vtype} (&queue(a) >> queue(a), &INV(a)? >> opt (a, b)): #[b:bool] bool b

local

assume queue (a:vt@ype) = List_vt (a)

in

implement
queue_nil{a} () = list_vt_nil{a} ()
implement
enqueue {a} (q, x) = let
  prval () = lemma_list_vt_param (q)
in
  q := list_vt_cons (x, q)
end
implement
dequeue {a} (q, x) =
  case+ q of
  | list_vt_nil () => let prval () = opt_none{a}(x) in false end
  | ~list_vt_cons (x1, q1) => let
    val () = q := q1
    val () = x := x1
    prval () = opt_some{a}(x)
  in
    true
  end

end

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

vtypedef sched = queue (thread_t)

var the_threads : sched = queue_nil{thread_t}()
val threads : ref(sched) = ref_make_viewptr {sched} (
  view@ the_threads | addr@ the_threads
)

implement
myenqueue (t) = let
  val (vbox pf | p) = (ref_get_viewptr {sched} (threads))
  val () = $effmask_ref (enqueue{thread_t} (!p, t))
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
  loop (
    q: &queue (thread_t)
  ): void = let
    var thr: thread_t
  in
    if :(thr: thread_t?, q: queue (thread_t)) => dequeue (q, thr) then let
       prval () = opt_unsome {thread_t} (thr)
       val () = thread_run (thr)
       val () = loop (q)
    in

    end else let
      prval () = opt_unnone {thread_t} (thr)
    in
    end
  end // end of [loop]

  val (vbox pf | p) = $effmask_ref (ref_get_viewptr {sched} (threads))
  val () = $effmask_ref (loop (!p))

} (* end of [mainloop] *)

end // end of [local]

(* ****** ****** *)
