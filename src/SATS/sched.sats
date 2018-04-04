staload "./cont.sats"

typedef threadfun (v:vtype, b:vt@ype) = (v, cont(b)) -> void

fun{v:vtype;r:vt@ype}
yield
(init: INV(v), tfn: threadfun (v, INV(r)), k: cont (INV(r))): void
(*
fun{b:vt@ype;v:vtype}
sleep (v: INV(v), tfn: thread_t (v, b), msec: int): void
*)

fun
mainloop (): void
