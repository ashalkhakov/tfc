extern
fun{} throws_assert$fn (): void = {
}

extern
fun{} throws_assert (): bool

implement{}
throws_assert () =
  try (f (); true)
  except ~AssertExn () => false
