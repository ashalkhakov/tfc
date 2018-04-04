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
