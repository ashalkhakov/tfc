
(*
// general CPS compose operation
// is it even necessary?
fun{a,b,c:vt@ype}
compose (f: kfun(a, b), g: kfun(b, c)): kfun(a, c) =
    lam (x : a, k : cont(c)) => // not envless! also needs linearity!
        resume (push (f, push (g, k)), x)
*)

// NEXT: some simple scheduler! round-robin, list of threads (per real thread)

scheduler =
List_vt (cont(int))

operations: dequeue, enqueue, check if empty

what do we do?

- while queue not empty:
  - dequeue continuation k
  - execute it, it should return either
    - a continuation k1
      - put k1 to end of queue (round-robin!)
    - or finish completely
      - discard the thread (nothing else to do with this thread!)

// NEXT: spawn & yield functions
extern
fun
spawn : (k: () -> void) -> void // spawn a new thread with the sheduler
extern
fun{a:t@ype}
yield : (k: cont(int)): void // yield a continuation to the scheduler, but return back!
extern
fun
mainloop : () -> void // returns when all work is done
// NEXT: simple concurrency programs

(*
how to implement?
use a linear singly linked list? :) yeah.
probably also will have to switch to some other representation of closures.
e.g. closures with explicit environments

"At the centre of the implementation is the CPC scheduler. The
scheduler manipulates three data structures: a queue of runnable
continuations, which are resumed in a round-robin fashion; a pri-
ority queue of continuations waiting on a timeout, and an array of
queues of continuations waiting on I/O, one per active file descrip-
tor."

how can we do this?
a scheduler might just be an event loop.

a CPS-converted function:
function(x1,...,xn,k) = let ... in k(...) end

never returns except by invoking its continuation:

function(x1,...,xn,k) = let ... in resume(k, ...) end

*)
