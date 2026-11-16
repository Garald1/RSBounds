# Build record for `RSBounds/HelfgottSmall`, 2026-11-10

Lean 4.35.0, Mathlib as pinned in `lake-manifest.json`, a 2-core machine with 5.8 GB available.

* `build-20261110.log`: the `Built …` lines of the build of all chunk modules and
  `RSBounds.HelfgottSmall.AllChunks`, in two runs. The two `error` lines are the first run's
  attempts at chunks 0 and 1, killed for lack of memory while another job ran beside them. Chunk 1
  was then rebuilt alone, and chunk 0 was split into ten parts (`Chunk/C0000S*.lean`), which all
  built; the second run finished with `Build completed successfully (1291 jobs)`.
* `axioms.lean`, `axioms-20261110.log`: `#print axioms` for the three unconditional theorems and
  the two gluing lemmas of `RSBounds.HelfgottSmall.Final`: only `propext`, `Classical.choice` and
  `Quot.sound`.

`RSBounds.HelfgottPsiBoundsBook` and the Comparator challenge `comparator-helfgott-psi-book.json`
were not built here: they import `HelfgottPsiBoundsFinal`, hence PsiCert.
