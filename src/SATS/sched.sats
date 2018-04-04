staload "./cont.sats"

typedef threadfun (v:vtype, b:vt@ype) = (v, cont(b)) -> void

fun{v:vtype;r:vt@ype}
yield
(init: INV(v), tfn: threadfun (v, INV(r)), k: cont (INV(r))): void
(*
fun{b:vt@ype;v:vtype}
sleep (v: INV(v), tfn: thread_t (v, b), msec: int): void
*)

(*
abstype cv = ptr // condition variable

cv_get (): cv
cv_retain (!cv): cv // refcounting!
cv_release (cv): void

cv_count (!cv): int // returns count of threads waiting on it

fun
cv_wait (cvar): void // used by a thread to wait for the condition variable

// used by a thread to wake up one thread waiting for a cv
fun
cv_signal (cvar): void

// used by a thread to wake up all threads waiting for a cv
cv_signal_all (cvar): void

- a thread will have at most one condvar to wait on
- all threads waiting on the same condvar are put into a single queue

*)

fun
mainloop (): void
