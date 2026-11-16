# Finite RH at height 1894438.5122 from `smmercuri/zeta`

The project has three files.

- **`ZetaBridge.lean`** proves

  ```lean
  theorem TernaryGoldbach.RSBounds.ZetaRH.finiteRH_rs75 : ZetaRH.FiniteRH 1894438.5122
  ```

  with no hypothesis, and more generally `ZetaRH.FiniteRH A` for every `A < 1895609`. It derives
  them from `Zeta.riemannHypothesisUpTo_1895609` by S. Mercuri and B. Mehta
  ([`smmercuri/zeta`](https://github.com/smmercuri/zeta), tag `v1-1.8956e6`). That is a
  kernel-checked verification that every nontrivial zero of `riemannZeta` with `|Im s| < 1895609`
  lies on the critical line, and its main theorem depends only on `propext`, `Classical.choice`
  and `Quot.sound`.
- **`ZetaBridge/Statement.lean`** defines `ZetaRH.FiniteRH`, a verbatim copy of RSBounds'
  `Goals.FiniteRH`.
- **`ZetaBridge/Check.lean`** proves `ZetaRH.FiniteRH = Goals.FiniteRH` by `rfl`. So Lean confirms
  that the bridge proves exactly RSBounds' premise.

`Goals.FiniteRH 1894438.5122` is the only premise of the RSBounds results that assume finite RH:

- Ramaré's bound (2.21), `Moebius003.ramareMoebius_of_finiteRH`;
- the RS75 zero-free region and ψ bound (`Goals.ZeroFreeRegion1975`, `Goals.PsiTable1975`);
- Schoenfeld (1976), Theorem 7* and Theorem 11 (`Schoenfeld1976Final`);
- (2.14) and (2.17) with the book's constants (`HelfgottPsiBoundsBook`).

So these results hold unconditionally, by combining two Lean theorems about one proposition.

## Why the bridge is a `module`, and why the copy

`zeta`'s prebuilt release ships the private part of its large certificate files (`.olean.private`)
compressed. A file that is not a `module` loads the private part of everything it imports, so it
fails on these files with "invalid header". A `module` reads only the public part.

A `module` cannot import a file that is not one, and `RSBounds.Targets` is not a `module`. Hence the
copy of `FiniteRH` in a small `module`, and the check against the original in a separate file that
does not import `zeta`.

## Why the halves are not combined in one Lean file

Two obstacles stand in the way.

- **Modules.** A file combining both halves would have to be a `module`, for the reason above. But
  RSBounds' files are not modules, so it could not import them.
- **Duplicate names.** RSBounds vendors some `PrimeNumberTheoremAnd` files under
  `vendor/rh100/Zeta23/FromPNTPlus/`, for instance `namespace CS` in `Sobolev.lean`. `zeta` brings
  in the same declarations from its own fork of `PrimeNumberTheoremAnd`. A source scan finds about
  345 shared names, and Lean refuses to load the same name twice.

## Status

**Built on 2026-11-16,** on Harald Helfgott's laptop against `zeta`'s prebuilt release (Lean
v4.35.0). All three files built. The `#guard_msgs` check in `ZetaBridge.lean` confirms that
`finiteRH_rs75` depends only on `propext`, `Classical.choice` and `Quot.sound`. This project's
dependencies are pinned in `lake-manifest.json`. Lean v4.35.0, Mathlib `56a005855` and every shared
package are at the same revisions as in RSBounds.

An earlier attempt, before `ZetaBridge.lean` was a `module`, failed with the "invalid header" error
described above.

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
