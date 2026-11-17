import Lake
open Lake DSL

package RSBounds

require TernaryGoldbach from git
  "https://github.com/calr3/ternary-goldbach.git" @
  "192ca57362fa3ee737cd83205cb9ea99526c4553"

@[default_target] lean_lib RSBounds where
  globs := #[.one `RSBounds]

-- Kernel-checked proofs of (M) and (m) of `mobius003.tex` (the MoebiusCert session's project,
-- unchanged). Used by `RSBounds.Moebius003.Complete`.
lean_lib MoebiusCert

-- Comparator challenges for the Möbius results (`comparator-ramare-moebius.json`,
-- `comparator-moebius003.json`, `comparator-moebius-cert.json`, `comparator-moebius-small.json`).
lean_lib RamareMoebiusChallenge where
  srcDir := "comparator"

lean_lib Moebius003Challenge where
  srcDir := "comparator"

lean_lib MoebiusCertChallenge where
  srcDir := "comparator"

lean_lib MoebiusSmallChallenge where
  srcDir := "comparator"

lean_lib MoebiusSmallSolution where
  srcDir := "comparator"

lean_lib RSTotientChallenge where
  srcDir := "comparator"

lean_lib RSTotientSolution where
  srcDir := "comparator"

lean_lib RSZeroCountChallenge where
  srcDir := "comparator"

lean_lib RSZeroCountSolution where
  srcDir := "comparator"

lean_lib RSZeroFreeChallenge where
  srcDir := "comparator"

lean_lib RSZeroFreeSolution where
  srcDir := "comparator"

-- Exact, checked 99-module dependency closure of RHHeight100.Main100.
-- The pinned upstream sources and adaptations are recorded under vendor/rh100.
lean_lib Zeta23 where
  srcDir := "vendor/rh100"
  globs := #[.submodules `Zeta23]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

lean_lib ZetaLean where
  srcDir := "vendor/rh100"
  globs := #[.submodules `ZetaLean]

lean_lib RHHeight where
  srcDir := "vendor/rh100"
  globs := #[.submodules `RHHeight]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

lean_lib RHHeight100 where
  srcDir := "vendor/rh100"
  globs := #[.submodules `RHHeight100]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

lean_lib HardyFirstZero where
  srcDir := "vendor/rh100"
  globs := #[.submodules `HardyFirstZero]

lean_lib HardyTenZeros where
  srcDir := "vendor/rh100"
  globs := #[.submodules `HardyTenZeros]

-- Comparator challenges for upstream's statements (calr3/ternary-goldbach at `192ca57`):
-- `comparator-upstream-ramare.json`, `comparator-ternary-goldbach.json`.
lean_lib UpstreamRamareChallenge where
  srcDir := "comparator"

lean_lib TernaryGoldbachChallenge where
  srcDir := "comparator"

-- [H] (2.14) and (2.17) on the book's ranges (`comparator-helfgott-psi-book.json`).
lean_lib HelfgottPsiBookChallenge where
  srcDir := "comparator"

lean_lib HelfgottPsiBookSolution where
  srcDir := "comparator"

-- [H] (2.16), (2.18) and (2.19) up to 2·10⁶, and their extension to the book's ranges given the
-- large-`y` inputs as hypotheses (`comparator-helfgott-low.json`).
lean_lib HelfgottLowChallenge where
  srcDir := "comparator"

lean_lib HelfgottLowSolution where
  srcDir := "comparator"

-- [H, Lemma B.1.2, (B.6)] with `31.521` (`comparator-helfgott-b6.json`).
lean_lib HelfgottB6Challenge where
  srcDir := "comparator"

lean_lib HelfgottB6Solution where
  srcDir := "comparator"

-- [H] (14.3), (14.24), (14.51) and (14.28) with Helfgott's constants (`comparator-helfgott-appa.json`).
lean_lib HelfgottAppAChallenge where
  srcDir := "comparator"

lean_lib HelfgottAppASolution where
  srcDir := "comparator"
