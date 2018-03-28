(* queue abstract type: this one is based on singly-linked lists
 * (adapted from ATS1 code by Hongwei Xi)
*)

absvtype linqueuelst_vt (n:int(*size*)) = ptr

stadef queue = linqueuelst_vt

fun{}
linqueuelst_is_nil
  {n:nat} (xs: !queue (n)):<> bool (n==0)

fun{}
linqueuelst_is_cons
  {n:nat} (xs: !queue (n)):<> bool (n > 0)


fun{}
linqueuelst_nil ():<> queue (0)

fun{}
linqueuelst_enqueue {n:nat} // O(1)
  (xs: &queue (n) >> queue (n+1), x: int): void

fun{}
linqueuelst_dequeue {n:pos} // O(1)
  (xs: &queue (n) >> queue (n-1)): int
  
  
fun{}
linqueuelst_free {n:int} (xs: queue (n)): void
