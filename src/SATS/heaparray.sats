
fun{T:vt@ype}
mycompare (&T, &T): bool

fun{T:vt@ype}
mycompare2 {l1,l2:addr} (!T @ l1, !T @ l2 | ptr l1, ptr l2): bool

(* ****** ****** *)

typedef HEAPNODE (a:t@ype, m:int, n:int, l:addr) = @{
    size= size_t m,
    count= size_t n,
    data= ptr l
}

(* ****** ****** *)

absvt@ype heap (a:t@ype+,m:int,n:int,l:addr) = HEAPNODE (a, m, n, l)
vtypedef heap (a:t@ype, m:int,n:int) = [l:addr] heap (a, m, n, l)

fun{a:t@ype}
heap_init {m:pos} (&heap (INV(a), 0, 0, null)? >> heap (a, m, 0, l), size_t m): #[l:addr] void
fun{a:t@ype}
heap_term {m,n:int;l:addr} (&heap (INV(a), m, n, l) >> heap (a, 0, 0, null)?): void
fun{a:t@ype}
heap_push {m,n:int;l:addr | n < m} (
  &heap (INV(a), m,n, l) >> heap (a, m, n+1, l), a
): void
fun{a:t@ype}
heap_pop {m,n:int;l:addr | n > 0} (&heap (INV(a),m,n,l) >> heap (a, m,n-1,l)): void
fun{a:t@ype}
heap_front {m,n:int;l:addr | n > 0} (&heap (INV(a), m, n, l) >> _): a

fun
heap_isnot_full {a:t@ype} {m,n:int;l:addr} (
  &heap (a, m, n, l) >> _
): bool (n < m)

fun{a:t@ype}
heap_resize {m,m1,n:int;l:addr | n <= m1} (
  &heap (INV(a), m, n, l) >> heap (a, m1, n, l1), size_t m1
): #[l1:addr] void

fun{T:vt@ype}
heapify {n:int} (&(@[INV(T)][n]) >> @[T][n], size_t n): void
