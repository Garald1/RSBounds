# Plan: the 1976 b = 23 row (`Goals.PsiTable1976`)

Status, 2026-11-08: stage A below is done. `PsiTable1976.of_certified :
Head1000.Certified → Goals.PsiTable1976` is proved (new files only; standard
three axioms), and so is `PsiTable1976.of_zeros0to1000`, which takes the three
statements `located`, `unique`, `count` of `Zeros0to1000` as hypotheses in
their exact form. A native Comparator run of the latter (and of the ψ bound
in the same form) against a Mathlib-only challenge passed, sandboxed. The
result is conditional on those three statements until stage B. Details:
`logs-claude/PSITABLE1976-STAGE1-NOTES.md`.

The target, in `RSBounds/Targets.lean`:

```lean
def PsiTable1976 : Prop :=
  FiniteRH 1894438.5122 → ∀ x : ℝ, Real.exp 23 ≤ x →
    |Chebyshev.psi x - x| < 0.00020171 * x
```

The proved 1975 row is `RosserSchoenfeld1975.psi_error_b23` with
0.00020211; its scalar budget, certified in
`QuarticFirst29BudgetNumerics.lean`, is at most 0.000202088906. The 1976 row
needs a budget below 0.00020171, i.e. about 3.8·10⁻⁷ less.

## How the zeros enter, in Schoenfeld (1976) and here

Schoenfeld, "Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II",
Math. Comp. 30 (1976), 337–360, continues the numbering of Rosser–Schoenfeld
(1975). The pages read for this plan are 337–340 and 351–353.

* (8.5), p. 351: G(D) = Σ_{0<γ≤D} (γ² + ¼)^{−1/2} − (1/4π){(log(D/2π) − 1)² + 1}
  + (1/D){0.137 log D + 0.443(log log D + 1/log D) + 2.6 − N(D)}: the explicit
  sum over the zeros up to D, minus its smooth main term, plus a Rosser-type
  boundary term at D.
* Lemma 9*, (8.7), p. 352: Lemma 9 with D free (2 ≤ D ≤ A); the zeros enter
  Ω₁* only through 4πG(D).
* p. 352: "The early zeros ρ_n = ½ + iγ_n of ζ(s) have been calculated for
  1 ≤ n ≤ 12,556 to an accuracy better than 2·10⁻⁷ by R. Sherman Lehman"
  (Lehman 1966); the table of D, N(D), S(D), 4πG(D), C(D) was extracted from
  calculations by Lehman and de Vogelaere. Rosser–Schoenfeld (1975) had used
  "D = 158.84998 which yields N(D) = 57, 4πG(D) ≤ 0.038207".
* p. 353: the Section 5 table was recalculated with the first D
  (7436.76651, N = 7192) for b ≤ 18.7, the second (8929.80867, N = 8896) for
  19.0 ≤ b ≤ 19.5, and the third (12030.00896, N = 12555) for b ≥ 20,
  "although this did not produce any decrease in ε for b ≥ 40". So the b = 23
  row uses the first 12555 zeros.
* p. 353 also says the table was recomputed "using the various devices
  mentioned": besides Lemma 9*, the choice T₂ = T₀ (p. 351: the earlier T₂ "is
  about 50% too large") and the incomplete-gamma bounds (8.8)–(8.10). From the
  paper alone, the drop from 0.00020211 to 0.00020171 cannot be attributed to
  the zeros only.

4πG(D) recomputed from the zero ordinates of `Garald1/zeta-zero-locations`
(`data/zeros_T10000.txt`, commit `df497b2`; script
`scripts/plan_schoenfeld_G.py`) reproduces Schoenfeld's table where the data
reach, and shows that most of the gain comes from the first zeros:

| D | N(D) | S(D) | 4πG(D) | Schoenfeld p. 352 |
|---|---|---|---|---|
| 100 | 29 | 0.59215562 | 0.176787 | |
| 158.84998 | 57 | 0.81139243 | 0.038206 | 4πG ≤ 0.038207 |
| 500 | 269 | 1.50594470 | −0.129885 | |
| 1000 | 649 | 2.02856589 | −0.171643 | |
| 2000 | 1517 | 2.62571658 | −0.193384 | |
| 7436.76651 | 7192 | 3.96742350 | −0.210077 | S ≤ 3.9674 2351, 4πG ≤ −0.210075 |
| 8929.80867 | 8896 | 4.17616892 | −0.211150 | S ≤ 4.1761 6893, 4πG ≤ −0.211150 |
| 10000 | 10142 | 4.30794435 | −0.211727 | |
| 12030.00896 | 12555 | | | S ≤ 4.5275 6275, 4πG ≤ −0.212544 |

From D = 158.85 to D = 12030, 4πG drops by 0.2508; D = 1000 already gets
0.2099 of that (84%), D = 2000 0.2316 (92%).

## Finding: the project's machinery needs 649 zeros, not 12555

In the project's b = 23 budget (`scripts/generate_quartic_budget_certificate.py`)
the zero head enters only through the line weight,

    a · (S + I(100, Y) + (F(100) + R(100) − 29)/100) + …,

with S = 0.592316 ≥ Σ over the 29 zeros up to height 100, and Rosser's
|N(T) − F(T)| ≤ R(T) above 100. The boundary term (F(100) + R(100) − 29)/100
≈ 0.029 is what a longer head saves; this is the same mechanism as
Schoenfeld's G(D). Replacing 100 by T₀, with S(T₀) and the exact count N(T₀),
and changing nothing else (δ = 2.11·10⁻⁵, the eight cancellation bands, the
0.931 factor, the high-zero term):

| head T₀ | zeros N(T₀) | budget | vs 0.00020171 |
|---|---|---|---|
| 100 | 29 | 0.000202087437 | above |
| 200 | 79 | 0.000201784824 | above |
| 500 | 269 | 0.000201593045 | below |
| 1000 | 649 | 0.000201525723 | below, margin 1.84·10⁻⁷ |
| 2000 | 1517 | 0.000201490670 | below |
| 10000 | 10142 | 0.000201461098 | below |

(`scripts/plan_b23_longer_head.py`; with the generator's S = 0.592316 at
T₀ = 100 it reproduces the certified 0.000202088906 exactly. A grid search
finds δ = 2.165·10⁻⁵ slightly better; `PolynomialZeroCancellation.coefficient_le`
allows δ ≤ 0.000022, but other δ-dependent steps were not checked, so the
plan keeps δ = 2.11·10⁻⁵.)

## The dependency: `Zeros0to1000`

The head through 1000 is exactly the first range of `Garald1/zeta-zero-locations`,
whose trusted statement `challenge/Zeros0to1000.lean` (as received
2026-11-08, sha256 `161dd725…b01dc2fa`) is:

* `ordinates : List ℕ`: the 649 integers m_k nearest to 10²⁴·γ_k;
* `located : ∀ s ∈ zerosBetween 0 1000, s.re = 1/2 ∧ analyticOrderAt
  riemannZeta s = 1 ∧ ∃ m ∈ ordinates, |s.im − m/10²⁴| ≤ 1/10²⁰`;
* `unique : ∀ m ∈ ordinates, ∃! s, riemannZeta s = 0 ∧ |s.im − m/10²⁴| ≤
  1/10²⁰`;
* `count : (zerosBetween 0 1000).ncard = 649`.

Checks made here:

* the 649 ordinates are strictly increasing and are the nearest integers to
  10²⁴γ for the Arb data used in the scans (largest rounding error 4.996·10⁻²⁵);
* with the head taken from the statement itself, γ ≥ (m − 10⁴)/10²⁴, the
  exact rational bound is Σ 1/γ ≤ 2.028657 (Σ 1/‖ρ‖ ≤ 2.028566), and the budget
  is 0.000201525743, margin 1.84·10⁻⁷;
* with only the module header removed (`module`, `public import`,
  `@[expose] public section` → `import Mathlib`), the statement elaborates
  against this project's Lean 4.35.0 / Mathlib `56a005855ea1`, with only the
  three `sorry` warnings.

These three theorems supply every field of this project's
`ZetaZeroTable.CertifiedTable 649 1000`: brackets m/10²⁴ ± 10⁻²⁰, a zero in
each (from `unique`), real part ½ and simplicity (from `located`, since each
bracket lies in (0, 1000]), completeness (`located`) and the count.

## Proposed route

A. **State the dependency here.** Vendor the statement (non-module copy,
   definitions unchanged) and define `Zeros0to1000.Certified : Prop` as
   `located ∧ unique ∧ count`. Prove, in new files and changing no existing
   one:
   1. `Certified → CertifiedTable 649 1000`;
   2. the head bound S(1000) ≤ 2.028658 (or the 1/‖ρ‖ form), by the method of
      `ZetaZeroTableHead.lean` / `ZetaZeroHeadBound.lean`;
   3. the budget at head 1000: files parallel to
      `QuarticFirst29BudgetBridges.lean` and `QuarticFirst29BudgetNumerics.lean`,
      generator adapted from `scripts/generate_quartic_budget_certificate.py`,
      assertion `budget < 0.00020171`;
   4. assembly as in `RosserSchoenfeld1975.psi_error_b23`:
      `Zeros0to1000.Certified → Goals.PsiTable1976`.

B. **Discharge the hypothesis** once the proof of `Zeros0to1000` exists under a
   compatible pin: vendor it (rebuilt against Mathlib `56a00585`, as
   `vendor/rh100` was), or move both projects to one Mathlib. Then
   `Goals.PsiTable1976` holds under `FiniteRH 1894438.5122` alone.

Stage A is independent of when or how the zero proof is finished, and makes
the dependency an explicit, Comparator-checkable statement. Until stage B,
the theorem is conditional on `Head1000.Certified`.

## Stage A as built (2026-11-08)

The proposition is named `Head1000.Certified` (in `RSBounds/Head1000Table.lean`),
not `Zeros0to1000.Certified`, so that nothing is added to the vendored
namespace. Files, all new:

| File | Content |
|---|---|
| `RSBounds/Zeros0to1000Statement.lean` | vendored definitions (`zerosBetween`, `ord0`–`ord2`, `ordinates`), theorems omitted |
| `RSBounds/Head1000Data.lean` | kernel-checked facts about the 649 integers: length, range, gaps, Σ (⌊10³³/(m − 10001)⌋ + 1) ≤ 2028658000 |
| `RSBounds/Head1000Table.lean` | `Certified`; `table : CertifiedTable 649 1000`; `positiveZeroCount_thousand`; `weighted_head_le` (Σ 1/‖ρ‖ ≤ 2.028658) |
| `RSBounds/QuarticHead1000BudgetNumerics.lean` | generated certificate: `scalarBudget1000_lt : scalarBudget1000 < 0.00020171` |
| `RSBounds/QuarticHead1000Budget.lean` | low-zero bound with D = 1000 (copy of `QuarticLowZeroBounds`), `relativeBudget1000_lt` |
| `RSBounds/PsiTable1976.lean` | zero-sum bound and psi assembly (copies of the 1975 ones), `psi_error_lt`, `of_certified`, and the explicit-hypothesis forms `psi_error_of_zeros0to1000`, `of_zeros0to1000` |
| `comparator/RSPsi1976Conditional{Challenge,Solution}.lean`, `comparator-psi1976-conditional.json` | Comparator for the two explicit-hypothesis theorems (passed 2026-11-08, sandboxed) |

Item 2 of the route uses the bracket bound γ > (m − 10001)/10²⁴ with a
rounded-up integer numerator per zero, which gives 2.028658 directly (the
plan's 2.028657 used exact rationals). The certified budget is
0.00020152574343131 (margin 1.8426·10⁻⁷).
