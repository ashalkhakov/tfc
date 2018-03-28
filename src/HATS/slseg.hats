// NOTE: we assume that a client has:
// 1. defined a typedef: slseg_node : addr -> t@ype
// 2. defined a viewdef for the mfree view: slseg_node_mfree_v : addr -> view
// 3. implemented the templates slseg_node_get_next and slseg_node_set_next

typedef slseg_node = slseg_node (null)?
viewdef slseg_node_v (l1: addr, l2: addr) = slseg_node (l1) @ l2

overload set_next with slseg_node_set_next
overload get_next with slseg_node_get_next

(* ***** ****** *)
(* dataview for singly-linked list segment
 * (adapted from ATS1 code by Hongwei Xi)
*)

absview slseg_v (addr(*self*), addr(*last node's [next]*), int(*segment length*))

extern
prfun
slseg_v_uncons : {l1,l2:addr} {n:pos}
    slseg_v (l1, l2, n) -<> [l3:addr] (slseg_node_mfree_v (l1), slseg_node_v (l3, l1), slseg_v (l3, l2, n-1))
extern
prfun
slseg_v_unnil : {l1,l2:addr} slseg_v (l1, l2, 0) -<> void

extern
prfun
slseg_v_lemma_size {l1,l2:addr}{n:int} (!slseg_v (l1, l2, n)): [n>=0] void

extern
prfun slseg_v_extend
{l1,l2,l3:addr} {n:nat} (
  pf_sl: slseg_v (l1, l2, n)
, pf_gc: slseg_node_mfree_v (l2)
, pf_at: slseg_node_v (l3, l2)
) :<prf> slseg_v (l1, l3, n+1)

extern
prfun slseg_v_append
{l1,l2,l3:addr} {n1,n2:nat} (
  pf1_sl: slseg_v (l1, l2, n1), pf2_sl: slseg_v (l2, l3, n2)
) :<prf> slseg_v (l1, l3, n1+n2) // end of [slseg_v_append]

(* ****** ****** *)
(* functions for constructing slseg values *)

// nil/empty list segment
extern
castfn
slseg_nil {l1,l2:addr} (
  slseg_node_mfree_v (l1), slseg_node_v (l2, l1) | p1: ptr l1, p2: ptr l2
) : (slseg_v (l1, l2, 1) | void)

// slseg cons -- insert before the first elt
extern
fun{}
slseg_cons {p_nxt0,p_slf,p_fst,p_lst:addr}{n:int} (
  slseg_node_mfree_v (p_slf), slseg_node_v (p_nxt0, p_slf)
, slseg_v (p_fst, p_lst, n)
| ptr p_slf, ptr p_fst
): (slseg_v (p_slf, p_lst, n+1) | void)

// slseg extend -- insert after the last elt
extern
castfn
slseg_snoc {p_nxt0,p_fst,p_lst:addr}{n:int} (
  slseg_node_mfree_v (p_lst), slseg_node_v (p_nxt0, p_lst)
, slseg_v (p_fst, p_lst, n)
| ptr p_lst
): (slseg_v (p_fst, p_nxt0, n+1) | void)

extern
fun{}
slseg_free {l1,l2:addr} {n:int} (
  slseg_v (l1, l2, n) | ptr l1, int n
): void


(* ****** ****** *)
(* slseg functions: implementations *)

dataview slseg_view
  (addr(*self*), addr(*last node's [next]*), int(*segment length*)) =
  | {n:nat} {l1,l2,l3:addr}
    slseg_v_cons (l1, l3, n+1) of (
      slseg_node_mfree_v (l1), slseg_node_v (l2, l1), slseg_view (l2, l3, n)
    ) // end of [slseg_v_cons]
  | {l:addr} slseg_v_nil (l, l, 0)
// end of [slseg_view]

assume slseg_v = slseg_view

implement
slseg_nil (pf_gc, pf_at | p1, p2) = let
  prval pf_res = slseg_v_cons (pf_gc, pf_at, slseg_v_nil ())
in
  (pf_res | ((*void*)))
end

implement
slseg_cons<> {p_nxt0,p_slf,p_fst,p_lst} (pf_gc, pf_at, pf_seg | p_slf, p_seg) = let
  val () = set_next (pf_at | p_slf, p_seg)
  prval () = slseg_v_lemma_size (pf_seg)
  prval pf_seg = slseg_v_cons (pf_gc, pf_at, pf_seg)
in
  (pf_seg | ((*void*)))
end

implement
slseg_snoc {p_nxt0,p_fst,p_lst} (pf_gc, pf_at, pf_seg | p_lst) = let
  prval () = slseg_v_lemma_size (pf_seg)
  prval pf_seg = slseg_v_extend (pf_seg, pf_gc, pf_at)
in
  (pf_seg | ((*void*)))
end

implement
slseg_free<> {l1,l2} {n} (pf_seg | p_seg, n) = let
  var i: int = n
  prval () = slseg_v_lemma_size (pf_seg)
  var p = p_seg
  prvar pf0 = pf_seg
  //
  val () =
  while* {i:nat; l1,l2:addr | i <= n} .<i>. (
    i: int (i)
  , p: ptr (l1)
  , pf0: slseg_v (l1, l2, i)
  ) : [l3,l4:addr] (
    pf0: slseg_v (l3, l4, 0)
  ) => (
    i > 0
  ) {
    //
    prval slseg_v_cons (pf_gc, pf_at, pf1_seg) = pf0
    prval () = pf0 := pf1_seg
    //
    val p1 = get_next (pf_at | p)
    val () = slseg_node_free (pf_gc, pf_at | p)
    val () = p := p1
    //
    val () = i := i - 1
    //
  } // end of [val]
  //
  prval slseg_v_nil () = pf0
  //
in
end // end of [slseg_free]
