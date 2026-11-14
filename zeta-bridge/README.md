# Finite RH at height 1894438.5122 from `smmercuri/zeta`

`ZetaBridge.lean` proves

```lean
theorem TernaryGoldbach.RSBounds.ZetaRH.finiteRH_rs75 : Goals.FiniteRH 1894438.5122
```

with no hypothesis, and more generally `Goals.FiniteRH A` for every `A < 1895609`. It derives them
from `Zeta.riemannHypothesisUpTo_1895609` by S. Mercuri and B. Mehta
([`smmercuri/zeta`](https://github.com/smmercuri/zeta), tag `v1-1.8956e6`), a kernel-checked
verification that every nontrivial zero of `riemannZeta` with `|Im s| < 1895609` lies on the
critical line. Its main theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

`Goals.FiniteRH 1894438.5122` is the only premise of the RSBounds results that assume finite RH:

- Ramaré's bound (2.21), `Moebius003.ramareMoebius_of_finiteRH`;
- the RS75 zero-free region and ψ bound (`Goals.ZeroFreeRegion1975`, `Goals.PsiTable1975`);
- Schoenfeld (1976), Theorem 7* and Theorem 11 (`Schoenfeld1976Final`);
- (2.14) and (2.17) with the book's constants (`HelfgottPsiBoundsFinal`).

The premise is the same constant, defined in `RSBounds/Targets.lean`, which imports only Mathlib.
So these results hold unconditionally, by combining two Lean theorems about one proposition.

## Why the two halves are not combined in one Lean file

A file importing both `Zeta.Main` and, say, `RSBounds.Moebius003.Complete` would receive several
hundred public declarations twice. A source scan finds about 345 shared names. RSBounds vendors
some `PrimeNumberTheoremAnd` files under `vendor/rh100/Zeta23/FromPNTPlus/`, for instance
`namespace CS` in `Sobolev.lean`. `zeta` imports the same declarations from its own fork of
`PrimeNumberTheoremAnd`. Lean refuses such an import.

There are two ways to fix this, and both force many modules to be rebuilt:

- move the vendored copies into a namespace of their own;
- take the first zeros from `zeta` instead of `vendor/rh100`.

## Status

- **Checked here:** the proof, against a verbatim copy of `zeta`'s definition of
  `RiemannHypothesisUpTo`, with `RSBounds.Targets`. This project's dependencies resolve, and
  `lake-manifest.json` pins them. Lean v4.35.0, Mathlib `56a005855` and every shared package are at
  the same revisions as in RSBounds.
- **Not checked here:** the build against `zeta`'s own files, which needs more disk than this
  machine has.

## Building

```bash
cd zeta-bridge
lake exe cache get   # Mathlib's prebuilt files
lake build           # fails if the axioms differ from the standard three (#guard_msgs)
```

`lake build` downloads `zeta`'s prebuilt release for Linux x86-64. The download is 1.7 GB, and it
unpacks to **about 34.4 GB**, almost all of it compiled-code files under `ir/`. So leave at least
40 GB free. It also compiles the 39 `PrimeNumberTheoremAnd` modules that `Zeta.Main` imports.

## What to trust

- **The prebuilt release.** Lake does not re-check downloaded `.olean` files: Mercuri's build
  checked them, as Mathlib's cache is checked by Mathlib's CI. An independent check means
  rebuilding `zeta` at branch `1.8956e6` from source with its `scripts/build.sh`. Its README
  reports 1 h 40 min for height 10⁶ on a 24-core, 256 GB server.
- **Comparator.** According to Mercuri, a Comparator run is not yet feasible at this height,
  because of a hashing problem in Lean. It was fixed on 12 November 2026, so a Lean release that
  includes the fix will be needed.
