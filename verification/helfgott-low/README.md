# Build record for `RSBounds/HelfgottLow`, 2026-11-17

Lean 4.35.0, Mathlib as pinned in `lake-manifest.json`, a 2-core machine with 7 GB.

* `build-20261117.log`: the `Built …` lines of the last build of all 200 chunk modules and
  `RSBounds.HelfgottLow.AllChunks` (`Build completed successfully (211 jobs)`); each chunk took
  7–8 s. `RSBounds.HelfgottLow.Final`, `HelfgottLowChallenge` and `HelfgottLowSolution` were then
  built on top of it.
* `axioms.lean`, `axioms-20261117.log`: `#print axioms` for the six theorems of
  `RSBounds.HelfgottLow.Final` in `comparator-helfgott-low.json` (only `propext`,
  `Classical.choice` and `Quot.sound`), and their statements.

`RSBounds.HelfgottLowBook` was not built here: it imports `HelfgottPsiBoundsBook`, hence PsiCert.
Its two theorems were checked here against copies of the signatures of
`HelfgottPsiBoundsBook.sum_vonMangoldt_le_a14` and `sum_vonMangoldt_mul_lt_a17`. The Comparator
run of `comparator-helfgott-low.json` has not been made yet.
