# Build record for `RSBounds/HelfgottAppA`, 2026-11-17

Lean 4.35.0, Mathlib and calr3/ternary-goldbach as pinned in `lake-manifest.json`, a 2-core machine.
`RSBounds.HelfgottAppA.EBound` (with `EtaPlusSup` and `NonPrime`), `HelfgottAppAChallenge` and
`HelfgottAppASolution` built with no errors and no warnings from these files.

* `axioms.lean`, `axioms-20261117.log`: `#print axioms` for the sup-norm, (14.51) and (14.28)
  theorems (only `propext`, `Classical.choice` and `Quot.sound`), and their statements.

On Harald's laptop, `run-helfgott-appa.sh` then ran `lake comparator --config
comparator-helfgott-appa.json`, which reported "Your solution is okay!" (Lean kernel) on 2026-11-17,
real time 2 min 2 s. The logs are `comparator-helfgott-appa.log` and `axioms-appa.log` at the root.
