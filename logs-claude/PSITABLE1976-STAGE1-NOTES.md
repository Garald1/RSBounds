# PsiTable1976, stage 1 (stage A of `docs/PsiTable1976Plan.md`), 2026-11-08

## Result

```lean
theorem TernaryGoldbach.RSBounds.PsiTable1976.of_certified :
    Head1000.Certified → Goals.PsiTable1976

theorem TernaryGoldbach.RSBounds.PsiTable1976.psi_error_lt (h : Head1000.Certified)
    (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x) :
    |Chebyshev.psi x - x| < 0.00020171 * x
```

and, with the three statements as separate hypotheses in their exact form
(these two are the ones compared by Comparator, below),

```lean
theorem TernaryGoldbach.RSBounds.PsiTable1976.of_zeros0to1000
    (located : ∀ s ∈ Zeros0to1000.zerosBetween 0 1000, s.re = 1 / 2 ∧
      analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros0to1000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20)
    (unique : ∀ m ∈ Zeros0to1000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20)
    (count : (Zeros0to1000.zerosBetween 0 1000).ncard = 649) :
    Goals.PsiTable1976
```

and `psi_error_of_zeros0to1000` (the same hypotheses, then `hRH`, `hx`, and
the ψ bound). Stage B is then
`of_zeros0to1000 Zeros0to1000.located Zeros0to1000.unique Zeros0to1000.count`.

`Goals.PsiTable1976` is unchanged (`RSBounds/Targets.lean`). The theorem is
**conditional** on `Head1000.Certified`, which nothing in this project
asserts:

```lean
def Certified : Prop :=
  (∀ s ∈ Zeros0to1000.zerosBetween 0 1000, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros0to1000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    (∀ m ∈ Zeros0to1000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    (Zeros0to1000.zerosBetween 0 1000).ncard = 649
```

These are the statements of `located`, `unique` and `count` in
`challenge/Zeros0to1000.lean` (`Garald1/zeta-zero-locations`), copied
verbatim (in that file they sit inside `namespace Zeros0to1000`).

## Checks on the vendored statement

* `RSBounds/Zeros0to1000Statement.lean` agrees with the file Harald sent
  (sha256 `161dd725362204ad1fc7144493f54c6c81dc86ea47b7feb261d97037b01dc2fa`) from
  `namespace Zeros0to1000` to the end, except that the three theorems are
  removed (`diff`, no other difference). The local clone of
  `zeta-zero-locations` at `df497b2` has the same statement body; its file
  (sha256 `68f27c14…`) differs from the sent one only in the header comment
  and the module-system header.
* The import is `Mathlib.NumberTheory.LSeries.RiemannZeta` instead of
  `Mathlib`. `#print Zeros0to1000.zerosBetween` with `pp.all` gives identical
  output under this import and under the challenge's `import Mathlib`. The
  `ordinates` lists are `ℕ` literals.

## What changed relative to the 1975 proof

Only the explicit zero head: height 1000 with 649 zeros instead of 100 with
29. δ = 0.0000211, the eight cancellation bands, the 0.931 factor and the
unconditional high-zero term are those of `RosserSchoenfeld1975.lean`.

* Head bound: from `unique`, each listed m has a zero with
  γ > (m − 10001)/10²⁴. The kernel checks
  Σ (⌊10³³/(m − 10001)⌋ + 1) = 2028657292 ≤ 2028658000 over the 649 integers,
  so Σ_{0<γ≤1000} 1/‖ρ‖ ≤ 2.028658 (`Head1000.weighted_head_le`).
* Count: N(1000) = 649 (`Head1000.positiveZeroCount_thousand`, via the
  table and `Rosser1941.positiveZeroCount_eq`).
* Budget: the generated certificate gives
  scalarBudget1000 ≤ 0.00020152574343131 < 0.00020171, margin 1.8426·10⁻⁷
  (`verification/quartic-head1000-scalar-generated.json`;
  `QuarticHead1000BudgetNumerics.scalarBudget1000_lt`, kernel-checked).
  The 1975 budget at head 100 was 0.000202088906.

## Files (all new; no existing file was changed)

* `RSBounds/Zeros0to1000Statement.lean`
* `RSBounds/Head1000Data.lean`
* `RSBounds/Head1000Table.lean`
* `RSBounds/QuarticHead1000BudgetNumerics.lean` (generated)
* `RSBounds/QuarticHead1000Budget.lean`
* `RSBounds/PsiTable1976.lean`
* `scripts/generate_quartic_head1000_budget_certificate.py`
* `verification/quartic-head1000-scalar-generated.json`
* `comparator/RSPsi1976ConditionalChallenge.lean`,
  `comparator/RSPsi1976ConditionalSolution.lean`,
  `comparator-psi1976-conditional.json`,
  `verification/run_psi1976_conditional_comparator.py`,
  `verification/psi1976-comparator/` (both run records)
* `logs-claude/PsiTable1976Audit.lean`, `logs-claude/psitable1976-axiom-audit.log`
* `logs-claude/build-psitable1976-stage1.log` (the successful build); the
  earlier `build-head1000-*.log` files record the failed attempts below.

The new modules are not in `RSBounds.lean`, so plain `lake build` does not
build them (adding them would change an existing file). Build with
`lake build RSBounds.PsiTable1976`.

## Build and audit

* `lake build RSBounds.PsiTable1976`: exit 0 (Head1000Data 3.6 s,
  Head1000Table 32 s, QuarticHead1000Budget 25 s, PsiTable1976 24 s;
  QuarticHead1000BudgetNumerics 54 s in an earlier run).
* `#print axioms`: `of_certified`, `psi_error_lt`, `of_zeros0to1000`,
  `psi_error_of_zeros0to1000` and every intermediate
  theorem audited depend on at most `propext`, `Classical.choice`,
  `Quot.sound`.

## Problems met

* This workspace has a 5.8 GiB memory limit, and importing all of Mathlib
  (which `ZetaZeroTable` does transitively) takes about 5 GB. A first version
  with `decide +kernel` over `Fin 649` was killed for lack of memory. The
  list facts are now in `Head1000Data.lean`, with the light import and
  Nat-only list checkers (`rangeCheck`, `gapCheck`) with soundness theorems;
  that module takes 3.6 s.
* The first Comparator run failed; see below.

## Comparator

Configuration `comparator-psi1976-conditional.json`; challenge
`comparator/RSPsi1976ConditionalChallenge.lean` (imports Mathlib only: the
`Zeros0to1000` statement data, `Goals.FiniteRH`, `Goals.PsiTable1975`,
`Goals.PsiTable1976`, and the two theorems with `sorry`); solution
`comparator/RSPsi1976ConditionalSolution.lean` (`import RSBounds.PsiTable1976`);
runner `verification/run_psi1976_conditional_comparator.py`, a copy of
`run_height_comparator.py` with only this configuration. Compared theorems:
`PsiTable1976.psi_error_of_zeros0to1000` and `PsiTable1976.of_zeros0to1000`;
permitted axioms: the standard three; no definition holes.

* Run `20261108T131556.933288Z` (theorems `psi_error_lt`, `of_certified`
  under `def Certified`): **failed**, "Const does not match between
  challenge and target 'TernaryGoldbach.RSBounds.Goals.PsiTable1976'". The
  two terms differed only in an auxiliary proof constant for the literal
  `23 : ℝ`: `Targets.lean` elaborates `PsiTable1976` with
  `PsiTable1975._proof_1` (shared within that file), the challenge with
  `PsiTable1976._proof_1`. Lean shares these constants within a file, so a
  one-file challenge cannot reproduce `def Certified` either (its literals
  2, 10, 1000 would reuse `FiniteRH`'s). Theorem types carry the proofs
  inline. Fix: the two explicit-hypothesis theorems above, and
  `PsiTable1975` defined before `PsiTable1976` in the challenge. Before the
  second run, `pp.all` output of both theorem types and of `PsiTable1976`,
  `FiniteRH`, `zerosBetween`, `ordinates` was identical under the challenge
  and the solution imports.
* Run `20261108T133504.533753Z`: **passed**, bwrap sandbox on. Comparator
  log: "Lean default kernel accepts the solution", "Your solution is okay!".
  Comparator stage 2559 s; whole run 46 min. Record:
  `verification/psi1976-comparator/comparator-psi1976-conditional/20261108T133504.533753Z/run.json`.
  This is a local record, not an IEANTN receipt.

## Stage B (not done)

Apply `of_zeros0to1000` to the proofs of `Zeros0to1000.located`, `unique`,
`count` once they exist under a compatible Mathlib pin; then
`Goals.PsiTable1976` holds under `FiniteRH 1894438.5122` alone.
