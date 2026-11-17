# Build record for `RSBounds/HelfgottB6`, 2026-11-17

Lean 4.35.0, Mathlib and calr3/ternary-goldbach as pinned in `lake-manifest.json`, a 2-core machine
with 7 GB.

* `build-20261117.log`: the `Built …` lines of a clean build of the nine modules
  (`Grid`, `Expand`, `Sound`, `GridA`, `GridBpos`, `GridBneg`, `Main`, `HelfgottB6Challenge`,
  `HelfgottB6Solution`), 4 min 26 s in all.
* `axioms.lean`, `axioms-20261117.log`: `#print axioms` for the expansion, the three combined grids
  and the two theorems (only `propext`, `Classical.choice` and `Quot.sound`), and the statements.
* `decl-hashes.lean.in`, `precheck-20261117.log`: the constants outside Mathlib and core that the
  statement in `comparator-helfgott-b6.json` reaches, with hashes of their types and values, in the
  challenge's environment and in the solution's. They agree. This is a local sanity check, not a
  Comparator run.

The Comparator run of `comparator-helfgott-b6.json` has not been made yet.
