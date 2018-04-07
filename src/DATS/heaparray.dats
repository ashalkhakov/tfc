#include
"share/atspre_staload.hats"

staload "./../SATS/heaparray.sats"

#define ATS_DYNLOADFLAG 0

implement{T}
mycompare2 {l1,l2} (pf1, pf2 | p1, p2) = mycompare<T>(!p1, !p2)

local

dataprop myprop (int,int) = {m,n:int | m >= n} MYPROP (m, n)

assume heap (T:t@ype, m:int, n:int, l:addr) = (
  array_v (T, l, n),
  array_v (T?, l+n*sizeof(T), m-n),
  mfree_gc_v (l),
  myprop (m, n)
| HEAPNODE (T, m, n, l)
)

in

implement{T}
heap_init (h, sz) = {
  val (pf_arr, pf_gc | p_arr) = array_ptr_alloc<T> (sz)
  prval () = h.0 := array_v_nil {T} ()
  prval () = h.1 := pf_arr
  prval () = h.2 := pf_gc
  prval () = h.3 := MYPROP ()
  val () = h.4.size := sz
  val () = h.4.count := (i2sz)0
  val () = h.4.data := p_arr
}

implement{T}
heap_term (h) = {
  prval pf1_arr = h.0
  prval pf2_arr = h.1
  prval pf_gc = h.2
  prval MYPROP () = h.3
  
  prval pf1_arr = __trustme (pf1_arr) where { extern prfun __trustme {n:int;l:addr} (array_v (T,l,n)): array_v (T?,l,n) }
  
  prval pf_arr = array_v_unsplit (pf1_arr, pf2_arr)
  val p_arr = h.4.data
  val () = array_ptr_free (pf_arr, pf_gc | p_arr)

  prval () = h.3 := unit_p ()
  val () = h.4.size := (i2sz)0
  val () = h.4.count := (i2sz)0
  val () = h.4.data := the_null_ptr
}

implement{T}
heap_push {m,n,l} (h, v) = {
    // Find out where to put the element and put it
    fun
    aux {l:addr} {i,n1:nat | i <= n1} (
     pf1_arr: array_v (T, l, i)
    , pf_at: T? @ l+i*sizeof(T)
    , pf2_arr: array_v (T, l+(i+1)*sizeof(T), n1-i)
    | base: ptr l, index: size_t i, n1: size_t n1
    ): [i1:nat | i1 <= i] (
     array_v (T, l, i1), T? @ l+i1*sizeof(T), array_v (T, l+(i1+1)*sizeof(T), n1-(i1))
    | size_t i1
    ) =
     if index = 0 then let
     in
       (pf1_arr, pf_at, pf2_arr | index)
     end else let
       val parent = pred (index) // parent0 >=0
       // [q,r:int | 0 <= r; r < j] (DIVMOD (parent0, 2, q, r)
       // we need to show that q is still less than parent, how?
       val (pf_divmod | parent) = g1uint_div2 (parent, (i2sz)2)
       prval () = __trustme (pf_divmod) where {
         extern
         prfun
         __trustme {x,y:int | x >= 0; y > 0} {q,r:int} (pf: DIVMOD (x, y, q, r)): [q < x] void
       }
       prval [parent:int] EQINT () = eqint_make_guint (parent)
       prval () = lemma_g1uint_param (parent)
       val (pf1_at, fpf | p_parent) = array_ptr_takeout<T> (pf1_arr | base, parent)
       var v = v
       val res = mycompare2<T> (pf1_at, view@v | p_parent, addr@v)
       prval pf1_arr = fpf (pf1_at)
     in
       if res then let
       in
           (pf1_arr, pf_at, pf2_arr | index)
       end else let
         // need to split pf1_arr by parent into pf11_arr, pf1_at, pf12_arr
         // and then, to assign:
         prval (pf11_arr, pf12_arr) = array_v_split_at (pf1_arr | parent)
         prval (pf1_at, pf12_arr) = array_v_uncons (pf12_arr)
         val p_index = ptr1_add_guint<T> (base, index)
         val p_parent = ptr1_add_guint<T> (base, parent)
         // so data[index] is now initialized
         var v_parent = ptr_get<T> (pf1_at | p_parent)
         val () = ptr_set<T> (pf_at | p_index, v_parent)
         // but data[parent] is now un-initialized...
         prval pf2_arr = array_v_unsplit (pf12_arr, array_v_cons (pf_at, pf2_arr))
       in
         aux (pf11_arr, pf1_at, pf2_arr | base, parent, n1)
       end
     end

    val count = h.4.count
    val base = h.4.data

    prval pf1_arr = h.0
    prval pf3_arr = h.1
    prval MYPROP () = h.3

    prval (pf_at, pf3_arr) = array_v_uncons (pf3_arr)
    prval pf2_arr = array_v_nil ()
    //
    prval () = __trustme () where { extern prfun __trustme (): [n>=0] void }
    //
    val (pf1_arr, pf_at, pf2_arr | index) = aux (pf1_arr, pf_at, pf2_arr | base, count, count)
    val p_index = ptr1_add_guint<T> (base, index)
    val () = ptr_set<T> (pf_at | p_index, v)
    prval pf2_arr = array_v_cons (pf_at, pf2_arr)
    //
    val () = h.4.count := succ(count)
    prval () = h.0 := array_v_unsplit (pf1_arr, pf2_arr)
    prval () = h.1 := pf3_arr
    prval () = h.3 := MYPROP ()
}

implement{T}
heap_pop {m,n,l} (h) = {
  // Remove the biggest element
  val count = h.4.count
  val count = pred(count)
  val base = h.4.data

  prval pf1_arr = h.0
  prval pf2_arr = h.1
  prval MYPROP () = h.3

  val () = h.4.count := count
  val p_temp = ptr1_add_guint<T> (base, count)
  prval (pf1_arr, pf_temp) = array_v_unextend {T} (pf1_arr)

  // Reorder the elements
  fun
  aux {n,i:nat | i < n} {l,l1:addr} (
    pf_arr: !array_v (T, l, n)
  , pf_tmp: !T @ l1
  | data: ptr l, index: size_t i, count: size_t n,
    p_tmp: ptr l1
  ): [i1: nat | i1 < n] size_t i1 = let
    // Find the child to swap with
    val swap = (index + index) + 1
  in
    if swap >= count then index // If there are no children, the heap is reordered
    else let
      val other = swap + 1
      val swap =
        (if other < count then (
           if mycompare<T> (!data.[other], !data.[swap]) then other
           else swap
        ) else swap) : sizeLt(n)
      //
      prval [swap:int] EQINT () = eqint_make_guint (swap)
      prval () = lemma_g1uint_param (swap)
      val (pf1_at, fpf | p_swap) = array_ptr_takeout<T> (pf_arr | data, swap)
      val res = mycompare2<T> (pf_tmp, pf1_at | p_tmp, p_swap)
      prval () = pf_arr := fpf (pf1_at)
    in
      if res then index // If the bigger child is less than or equal to its parent, the heap is reordered
      else let
        val () = !data.[index] := !data.[swap]
      in
        aux (pf_arr, pf_tmp | data, swap, count, p_tmp)
      end
    end
  end
  // AS: guess I fixed a bug here!
  val () =
    if isgtz(count) then let
      val index = aux (pf1_arr, pf_temp | base, (i2sz)0, count, p_temp)
      val () = array_set_at_guint<T> (!base, index, ptr_get<T> (pf_temp | p_temp))
    in
    end

  prval () = h.0 := pf1_arr
    
  prval pf2_arr = array_v_cons (pf_temp, pf2_arr)
  prval () = h.1 := pf2_arr
  prval () = h.3 := MYPROP ()
}

implement{T}
heap_front {m,n,l} (h) = res where {
  val count = h.4.count
  val base = h.4.data

  prval pf1_arr = h.0
  prval (pf_at, pf1_arr) = array_v_uncons (pf1_arr)
  prval pf2_arr = h.1
  prval MYPROP () = h.3

  val p_index = base
  val res = ptr_get<T> (pf_at | p_index)
  prval pf1_arr = array_v_cons (pf_at, pf1_arr)
  //
  prval () = h.0 := pf1_arr
  prval () = h.1 := pf2_arr
  prval () = h.3 := MYPROP ()
} (* end of [heap_front] *)

implement
heap_isnot_full {a} {m,n,l} (h) = res where {
  val count = h.4.count
  val size = h.4.size
  prval MYPROP () = h.3
  val res = count < size
} (* end of [heap_isnot_full] *)

implement{T}
heap_resize {m,m1,n,l} (h, size) = {
  val p11_arr = h.4.data

  prval pf11_arr = h.0
  prval pf12_arr = h.1
  prval pf_gc = h.2
  prval MYPROP () = h.3

  prval () = lemma_array_v_param (pf11_arr)
  prval () = lemma_g1uint_param (h.4.size)
  prval () = lemma_g1uint_param (h.4.count)

  val (pf2_arr, pf2_gc | p2_arr) = array_ptr_alloc<T> (size)

  prval (pf21_arr, pf22_arr) = array_v_split_at (pf2_arr | h.4.count)
  val () = array_copy<T> {n} (!p2_arr, !p11_arr, h.4.count)

  prval () = topize (!p11_arr)
  prval pf1_arr = array_v_unsplit (pf11_arr, pf12_arr)
  val () = array_ptr_free (pf1_arr, pf_gc | p11_arr)

  val () = h.4.size := size
  val () = h.4.data := p2_arr
  prval () = h.0 := pf21_arr
  prval () = h.1 := pf22_arr
  prval () = h.2 := pf2_gc
  prval () = h.3 := MYPROP ()
} (* end of [heap_resize] *)

end // end of [local]

(* ****** ****** *)

extern
fun
{a:vt0p}
array_ptr_takeout2
  {l:addr}{n:int}{i,j:nat | i <> j; i < n; j < n}
(
  array_v (INV(a), l, n)
| ptr l, size_t i, size_t j
, &ptr? >> ptr (l+i*sizeof(a)), &ptr? >> ptr (l+j*sizeof(a))
) : (
  a @ (l+i*sizeof(a))
, a @ (l+j*sizeof(a))
, (a @ (l+i*sizeof(a)), a @ (l+j*sizeof(a))) -<lin,prf> array_v (a, l, n)
| void
) (* end of [array_ptr_takeout2] *)

extern    
prfun
array_v_takeout2
  {a:vt0p}
  {l:addr}
  {n:int}{i,j:nat | i <> j; i < n; j < n}
(
  pfarr: array_v (INV(a), l, n)
) :<prf> @(
  a @ l+i*sizeof(a),
  a @ l+j*sizeof(a),
  (a @ l+i*sizeof(a), a @ l+j*sizeof(a)) -<lin,prf> array_v (a, l, n)
) // end of [array_v_split2]

implement{a}
array_ptr_takeout2 {l}{n}{i,j} (pf_arr | p_arr, i, j, p_i, p_j) = let
  val () = p_i := ptr1_add_guint<a> (p_arr, i)
  val () = p_j := ptr1_add_guint<a> (p_arr, j)
    
  prval () = lemma_array_v_param (pf_arr)
  prval () = lemma_g1uint_param (i)
  prval () = lemma_g1uint_param (j)

  prval (pf_i, pf_j, fpf) = array_v_takeout2 {a}{l}{n}{i,j} (pf_arr)
in
  (pf_i, pf_j, fpf | ())
end // end of [array_ptr_takeout2]

(* ****** ****** *)

implement{T}
heapify {n} (data, count) = let
  prval () = lemma_g1uint_param (count)
in
if iseqz(count) then ()
else {
  fun
  aux (data: &(@[T][n]) >> _, i: sizeLt(n)): void = let
    var j = i
  in
    for* {j:nat | j < n} (j: size_t j) : (i: size_t j) =>  ( ; ; )
    {
      var l = j + j + (i2sz)1
      var r = j + j + (i2sz)2
      var c: sizeLt(n) = j

      val () =
        if (l < count) then {
          var p_l: ptr
          var p_c: ptr
          val p_arr = addr@ data
          prval pf_arr = view@ data
          val (pf_l, pf_c, fpf | ()) = array_ptr_takeout2<T> (pf_arr | p_arr, l, c, p_l, p_c)
          val () = (if mycompare2 (pf_l, pf_c | p_l, p_c) then c := l)
          prval () = view@ data := fpf (pf_l, pf_c)
        } (* end of [val] *)
      val () =
        if (r < count) then {
          var p_r: ptr
          var p_c: ptr
          val p_arr = addr@ data
          prval pf_arr = view@ data
          val (pf_r, pf_c, fpf | ()) = array_ptr_takeout2<T> (pf_arr | p_arr, r, c, p_r, p_c)

          val () = (if mycompare2 (pf_r, pf_c | p_r, p_c) then c := r)
          prval () = view@ data := fpf (pf_r, pf_c)
        } (* end of [val] *)

      val () =
        if c = j then $break
      // end of [val]

      var p_j: ptr
      var p_c: ptr
      val p_arr = addr@ data
      prval pf_arr = view@ data
      val (pf_j, pf_c, fpf | ()) = array_ptr_takeout2<T> (pf_arr | p_arr, j, c, p_j, p_c)

      // exchange
      val temp = ptr_get<T> (pf_j | p_j)
      val () = ptr_set<T> (pf_j | p_j, ptr_get<T> (pf_c | p_c))
      val () = ptr_set<T> (pf_c | p_c, temp)

      prval () = view@ data := fpf (pf_j, pf_c)

      val () = j := c
    }
  end (* end of [aux] *)
    
  prval () = lemma_g1uint_param (count)
    
  val (pf_divmod | count_2) = g1int_ndiv2 ((sz2i)count, 2)
  prval () = __trustme (pf_divmod) where {
    extern
    prfun
    __trustme {x,y:int | x >= 0; y > 0} {q,r:int} (pf: DIVMOD (x, y, q, r)): [q >= 0; q < x] void
  }
  var i: int

  val () =
    for* {i:nat | i < n} (i: int (i)) : (i: int (i)) => (i := count_2; i >= 0; i := pred(i))
    {
      val () = aux (data, (i2sz)i)
    }
}
end // end of [heapify]

(* ****** ****** *)
