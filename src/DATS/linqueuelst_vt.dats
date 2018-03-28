#include
"share/atspre_staload.hats"

staload "./../SATS/linqueuelst_vt.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

// first, instantiate the slseg
typedef slseg_node (l:addr) = @{data= int, next= ptr l} // the node type
viewdef slseg_node_mfree_v (l:addr) = mfree_gc_v (l)

#include "./../HATS/slseg_node.hats" // signatures for the node type operations

// implementations of operations
implement
slseg_node_set_next<> {l1,l2,l3} (pf_at | p, p2) = !p.next := p2
implement
slseg_node_get_next<> {l1,l2} (pf_at | p) = !p.next
implement
slseg_node_free<> {l1,l2} (pf_gc, pf_at | p) = ptr_free (pf_gc, pf_at | p)

// list routines
#include "./../HATS/slseg.hats"

(* ****** ****** *)

local

datavtype queuelst_vt (int) =
  | {n:nat} {l1,l2,l3:addr}
    queuelst_vt_some (n+1) of (
      slseg_v (l1, l2, n), mfree_gc_v (l2), slseg_node_v (null, l2) | int n, ptr l1, ptr l2
    ) // end of [queuelst_vt_some]
  | queuelst_vt_none (0) of ()

assume linqueuelst_vt (n: int) = queuelst_vt (n)

in

implement{}
linqueuelst_nil () = queuelst_vt_none ()

implement{}
linqueuelst_is_nil (xs) = (
case+ xs of
| queuelst_vt_some (_, _, _| _, _, _) => false
| queuelst_vt_none () => true
) (* end of [linqueuelst_is_nil] *)

implement{}
linqueuelst_is_cons (xs) = (
case+ xs of
  | queuelst_vt_some (_, _, _ | _, _, _) => true
  | queuelst_vt_none () => false
) (* end of [linqueuelst_is_cons] *)

implement{}
linqueuelst_enqueue (xs, x) = let
  val (pf_at_new, pf_gc_new | p_new) = ptr_alloc<slseg_node> ()
  val () = p_new->data := x
  val () = p_new->next := the_null_ptr
in
  case+ xs of
  | @queuelst_vt_some
      (pf_seg, pf_gc, pf_at | n, p1, p2) => let
      prval [l2:addr] EQADDR () = ptr_get_index (p2)
      val () = set_next (pf_at | p2, p_new)
      prval pf_seg_new = slseg_v_extend (pf_seg, pf_gc, pf_at)
      prval () = begin
        pf_seg := pf_seg_new; pf_gc := pf_gc_new; pf_at := pf_at_new
      end // end of [prval]
    in
      n := n + 1;
      p2 := p_new;
      fold@ xs;
    end // end of [queuelst_vt_some]
  | ~queuelst_vt_none () => begin
      xs := queuelst_vt_some (slseg_v_nil (), pf_gc_new, pf_at_new | 0, p_new, p_new)
    end // end of [queuelst_vt_none]
end // end of [linqueuelst_enqueue]

implement{}
linqueuelst_dequeue (xs) = let
  val+ @queuelst_vt_some (pf_seg, pf_gc, pf_at | n, p1, p2) = xs
in
  if n > 0 then let
    prval (pf_gc, pf_at, pf1_seg) = slseg_v_uncons (pf_seg)
    val x = p1->data
    val p1_ = p1
    val () = p1 := get_next (pf_at | p1)
    val () = slseg_node_free (pf_gc, pf_at | p1_)
  in
    pf_seg := pf1_seg;
    n := n - 1;
    fold@ xs;
    x
  end else let
    prval () = slseg_v_unnil (pf_seg)
    val x = p2->data
    val () = slseg_node_free (pf_gc, pf_at | p2)
  in
    free@ {0} (xs);
    xs := queuelst_vt_none ();
    x
  end // end of [if]
end // end of [linqueuelst_deqeue]

implement{}
linqueuelst_free (xs) = case+ xs of
  | ~queuelst_vt_some (pf_seg, pf_gc, pf_at | n, p1, p2) => let
      val () = slseg_node_free (pf_gc, pf_at | p2)
    in     
      slseg_free (pf_seg | p1, n)
    end // end of [queuelst_vt_some]
  | ~queuelst_vt_none () => ()
// end of [linqueuelst_free]

end
