# Lowering the finite-RH height from 1894439 to 1894438.5122

Date: 2026-11-07. Toolchain: Lean 4.35.0, Mathlib `56a00585`, TernaryGoldbach
`ce82a5b2`. Baseline: `rsbounds-project-sources.tar.gz` as received.

1894438.5122 = 9472192561/5000 is Rosser–Schoenfeld's A = 1894438.51224…
rounded down. Every changed public theorem now assumes `FiniteRH 1894438.5122`
(and, where it has one, a height condition at 1894438.5122) instead of
`FiniteRH 1894439`. Since `FiniteRH 1894439 → FiniteRH 1894438.5122`
(`Goals.FiniteRH.mono`), each new theorem implies the old one.

## Rule used to classify occurrences

* **Premise** (`hRH : FiniteRH 1894439`, `ht : 1894439 ≤ t`): lowered. This
  strengthens the theorem.
* **Split height** (`|γ| ≤ A` on the line, `A < |γ|` treated otherwise):
  lowered on both sides. The zeros in (1894438.5122, 1894439], among them
  zero 3 502 501 at 1894438.637, move to the "otherwise" side. Every
  numerical bound evaluated at A was recomputed at the new A (table below).
* **Conclusion about the number 1894439** (`cutoff_height : 1894439 ≤ 17 e^X`):
  left unchanged, so no statement is weakened; call sites use
  `1894438.5122 ≤ 1894439`.
* **Natural-number index** (`eventually_ge_atTop (1894439 : ℕ)`, used only to
  make contour heights eventually exceed A): left unchanged; it still does so.

## Margins at the new height (all recomputed with exact rationals or mpmath)

| Quantity | Bound | at 1894439 | at 1894438.5122 |
|---|---|---|---|
| `heightRatio` = v / log(A/17) (certified upper end) | < 0.029172 | 0.0291719245 | 0.0291719252 (margin 7.48e-8) |
| `15·22.584/A²` (frequency tail) | < 1e-10 | 9.439106e-11 | 9.439111e-11 |
| `cubicAllowance A` rational majorant (RosserCubicTail) | < 3e-13 | 2.994922e-13 | 2.994923e-13 (margin 5.08e-16) |
| `square_tail_A_lt` majorant (MertensTailScalars) | < 1.2e-6 | 1.176763e-6 | 1.176763e-6 |
| `C·A⁻²·3e-13` (ModeratePsi.high_fifth_le) | ≤ 2e-12 | 1.42105e-12 | 1.42105e-12 |
| `2·1.00001/A` (ThetaLarge prefactor; file removed 2026-11-08) | ≤ 2e-6 | 1.05573e-6 | 1.05573e-6 |
| `Z3g BPz2 A` via (37+2.6A)/1.2039 (ThetaLarge; removed) | ≤ 5e6 | 4.09135e6 | 4.09135e6 (decreases with A) |
| quartic `scalarBudget` (b = 23) | < 0.00020211 | 0.000202088903 | 0.000202088906 (margin 2.109e-8) |

No margin failed.

## Build and audit results

* `lake build` (default target): success, 9331 jobs. `lake build` of the 24
  touched modules that can compile (list in `build-confirm.log`): success.
  First full build: `build-1.log`; confirmation: `build-confirm.log`.
* 2026-11-08, after the `SchoenfeldZeroSymmetry` fix and the removals:
  `build-confirm-2026-11-08.log` (default target, the touched modules and
  `SchoenfeldZeroSymmetry`: success); `axiom-audit.log` rerun (29 theorems,
  standard axioms only); `rs-closure-sha256.txt` still checks.
* `comparator/RS62GlobalChallenge`, `RSPsiChallenge`, `RS62GlobalSolution`,
  `RSPsiSolution` compiled with `lake env lean` (`comparator-challenges.log`);
  `RSZeroFreeChallenge`/`RSZeroFreeSolution` are Lake libraries and built.
  The only `sorry`s are the deliberate challenge stubs.
* `HeightAudit.lean` / `axiom-audit.log`: 29 public theorems, each depending
  only on `propext`, `Classical.choice`, `Quot.sound`; the `#check` lines show
  the new statements.
* `rs-closure-sha256.txt`: sha256 of the 211 project files in the import
  closures of the default target, the three RS solutions and the three
  challenges, plus lakefile, toolchain, manifests, generators and generated
  JSON. Check with `sha256sum -c logs-claude/rs-closure-sha256.txt`.

## Not compiled: the theta chain (pre-existing, independent of the change)

**2026-11-08:** the whole chain was removed at Harald's decision:
`ThetaLarge.lean` with its audit file `verification/ThetaLargeAudit.lean`,
then `PsiFiniteRH.lean` and `PsiFiniteRHZeroFree.lean`. None of them ever
compiled in this project, and nothing else imported them (`RHUpToHeight`,
defined in `PsiFiniteRH`, had no other users). `Theta.lean`, the unconditional
R = 20 region, stays: it compiles, but nothing imports it now. The text below
records why the chain did not compile.

`PsiFiniteRH.lean` does not compile against the pinned TernaryGoldbach
`ce82a5b2`: the upstream lemmas it uses (`zerosRectD_zetaF_strip`,
`line_sum_leH`, …) are declared after `variable [Fact TernaryGoldbach.RHUpTo]`,
so they require that instance, which is RH up to 3·10¹⁰ (Platt). The file is
unchanged and imports only upstream, so this failure is independent of the
height change. `PsiFiniteRHZeroFree` and `ThetaLarge` import it and are
therefore not built. No public RS62/RS75 theorem and no other module imports
`ThetaLarge`.

Diagnostic (scratch copies only, never shipped): adding the instance as a
section variable, the edited `PsiFiniteRHZeroFree` elaborates; `ThetaLarge`
still has 7 errors (two `linarith` failures, four heartbeat timeouts, one
`rw` failure), at exactly the same locations as the unedited baseline under
the same diagnostic. So the height edits there are untested by compilation but
introduce no new error; repairing the chain is a separate task.

## Schoenfeld files

On 2026-11-07 no `RSBounds/Schoenfeld*.lean` file was modified. On
2026-11-08, at Harald's request, one was: `SchoenfeldZeroSymmetry` (see the
end of this section). Two of them,
`SchoenfeldCoefficientPairing` and `SchoenfeldZeroSymmetry`, used to be in the
RS62 closure through `WeakPsiTail`; they call `xi_zero_re_lt`,
`RS75ZeroPowerDecay.log_height_pos` and `FiniteRH 1894439` with old-height
arguments and so cannot compile against the lowered theorems. `WeakPsiTail`
now restates the one lemma it took from them (`low_re_eq_half`, three lines)
at the lowered height and no longer imports them, so RS62 does not depend on
them.

Building all 31 `Schoenfeld*` modules (`schoenfeld-impact-build.log`,
classified in `schoenfeld-impact-summary.txt`): 9 build; `SchoenfeldZeroSymmetry`
fails at its three old-height calls (lines 74, 89, 92); the other 21 are
downstream of it and so not built, two of them also downstream of
`QuadraticZeroKernel`, which fails independently of this change: it has no
finite-RH hypothesis and imports nothing that changed. Its receipts are not
passes (`schoenfeld-quadratic-kernel-attempt1-run.json` exited 1 with an empty
log; `schoenfeld-quadratic-kernel-run.json` recorded no runs and never
finished), and the Schoenfeld status file calls it work in progress. Adapting
`SchoenfeldZeroSymmetry` is the first step for the Schoenfeld chat;
`Goals.FiniteRH.mono` converts a `FiniteRH 1894439` premise for the lowered
theorems.

**2026-11-08:** `SchoenfeldZeroSymmetry` fixed (Harald: "just fix this one
file"; the other Schoenfeld files stay with the Schoenfeld chat). The only
change: the premises of `rpow_boundary_eq` (`1894439 ≤ γ`) and
`zero_pair_power_le` (`1894439 ≤ |ρ.im|`) are lowered to 1894438.5122, which
strengthens both lemmas; the file has no numerics at the height. It builds
(`build-schoenfeld-zero-symmetry.log`). Its downstream Schoenfeld modules were
not rebuilt; their own height occurrences remain for the Schoenfeld chat.

## Comparator

The psi, RS62 and zero-free challenge statements changed (height only), so
their old receipts no longer certify the current statements. Unaffected:
`comparator.json` (totient), `comparator-zero-count.json`.

New runs, 2026-11-08, with `verification/run_height_comparator.py` (one
runner for the three configurations, adapted from
`run_zero_free_comparator.py`): pin checks; wrapper build (Lake for the
`RSZeroFree*` libraries; for psi and RS62 the pinned `lean` into a fresh
directory, never over `.lake/build`); a fresh transitive axiom audit of the
solution theorems; `leanexport` of both wrappers; `lake comparator` with both
from-export flags, **bwrap sandbox on** (installed for these runs); hash checks
of sources, objects, tools and exports before and after. Unlike
`run_zero_free_comparator.py` it records the tool binaries' hashes instead of
comparing them with `../../evidence/toolchain-binaries.json`, which is not in
this project. Records: `verification/height-comparator/<config>/<run id>/`.
Not IEANTN receipts.

| Configuration | Theorems | Verdict | Comparison stage |
|---|---|---|---|
| `comparator-zero-free.json` | `zero_free_high`, `zero_free` | passed: "Lean default kernel accepts the solution", "Your solution is okay!" | 2238 s |
| `comparator-psi.json` | `psi_error_b23` | passed (same two lines) | 2117 s |
| `comparator-rs62-global.json` | `mertens_lower_of_finiteRH`, `totient_bound_of_finiteRH` | passed (same two lines) | 3215 s |

Each fresh solution audit lists only `propext`, `Classical.choice`,
`Quot.sound`.

## Per-file notes

Lean, items 1–2 (RS75):

* `Targets.lean`: IEANTN patch (the four `Goals` statements now assume
  `FiniteRH 1894438.5122`, `PsiTable1976` and `ThetaLogBound` included; both
  are unproved specifications with no users) plus `Goals.FiniteRH.mono`, a
  one-line proof. Safe: each new `Goals` proposition has a weaker premise,
  so it implies the old one.
* `RS75ZeroFreeNumerics.lean`: regenerated. Only `heightRatio`'s definition
  and the log node `n24` changed, to log(9472192561/85000) = log(A/17); the
  kernel re-checks every bound, and `heightRatio_upper` still holds.
* `RS75ZeroFreeScalars.lean`: the height premise `1894439 ≤ t` lowered in
  five lemmas; the only numerics at the endpoint are `heightRatio` and
  15·22.584/A² < 1e-10, both rechecked. The residual coefficients c0–c4 do
  not depend on A.
* `RS75ZeroFree1975.lean`: `xi_zero_re_lt(_pos)`, `zero_free_high` now start
  at 1894438.5122 (stronger), `zero_free` assumes `FiniteRH 1894438.5122`
  (stronger). This closes the strip 1894438.5122 < |t| < 1894439.
* `RS75FiniteHandoff.lean`: finite RH handoff on 21 ≤ |t| ≤ 1894438.5122,
  high part from 1894438.5122; the split is exhaustive as before.
* `QuarticFirst29BudgetNumerics.lean`: regenerated with the IEANTN generator
  patch; byte-identical to IEANTN's patched file. `scalarBudget < 0.00020211`
  re-checked by the kernel (upper end 0.000202088906).
* `QuarticFirst29BudgetBridges.lean`, `QuarticLowZeroBounds.lean`,
  `RosserSchoenfeld1975.lean`: IEANTN patches, unchanged. In
  `RosserSchoenfeld1975` the natural-number index `1894439` that makes
  contour heights exceed A stays, with `(A : ℝ) < 1894439`.

Lean, item 3:

* `RS62MertensFromFiniteRH.lean`, `RS62TotientFromFiniteRH.lean`: premise
  passed through.
* `ModeratePsi.lean`: split height. Low part: the window budget depends only
  on the lower cut-offs (2000, …), not on A. High part: C·A⁻²·3e-13 ≤ 2e-12
  rechecked. The ℕ index stays at 1894439.
* `WeakPsiTail.lean`: split height. Low part 2·A·Σm/γ² gets smaller with A;
  high part is the cubic tail. Restates `low_re_eq_half`; drops the
  `SchoenfeldCoefficientPairing` import (see above). The ℕ index stays.
* `RosserCubicTail.lean`: the unconditional cube tail now starts at A;
  `cubicAllowance_A_lt` rechecked (margin 5.08e-16 against 3e-13).
* `RS75ZeroPowerDecay.lean`, `RS75DecayingHighZeros.lean`,
  `RS75AdaptiveHighBudget.lean`: high-zero threshold lowered; uses the
  unconditional region from A (item 1) and the cube tail at A; no other
  numerics at A.
* `MertensTailScalars.lean`: the square-tail scalar evaluated at the new A
  (1.176763e-6 < 1.2e-6).
* `MertensPotentialBound.lean`, `MertensPotentialDecay.lean`: premise and
  split lowered; `squareAllowance_A_lt` uses the new scalar; the generic
  lemmas in `A` are unchanged.
* `MertensLargeBudget.lean`: premise lowered; the cutoff condition
  `1894438.5122 ≤ cutoffHeight x` follows from the unchanged
  `MertensDecayScalars.cutoff_height` (1894439 ≤ 17 e^X), which is not
  weakened.
* `Theta.lean`: the unconditional R = 20 region now from 1894438.5122; the
  numerics at the endpoint are log A ≥ 14 and A ≥ 10⁶. Builds.
* `PsiFiniteRH.lean`, `PsiFiniteRHZeroFree.lean`, `ThetaLarge.lean`,
  `verification/ThetaLargeAudit.lean`: removed on 2026-11-08 (never compiled;
  no other importers), see "theta chain".
* `SchoenfeldZeroSymmetry.lean` (2026-11-08): two premises lowered, see
  "Schoenfeld files".
* `comparator/RS62GlobalChallenge.lean`, `RSPsiChallenge.lean`,
  `RSZeroFreeChallenge.lean`: statements at the new height; compile.

Scripts and data:

* `scripts/generate_rs75_zero_free_scalars.py`: A = 9472192561/5000 in the
  log node and in the Lean `heightRatio` text. Before the change it
  reproduced the shipped files byte for byte.
* `scripts/generate_quartic_budget_certificate.py`: IEANTN generator patch.
* `verification/rs75-zero-free-scalars-generated.json`,
  `verification/quartic-first29-scalar-generated.json`: regenerated records.

Text:

* `README.md`, `comparator/README.md`, `verification/README.md`, 17 files in
  `docs/` (no `docs/Schoenfeld*`): the height in statements updated, plus a
  short banner saying that receipts, hashes and Comparator records cited
  there were made for the old statements. Historical receipt text is not
  rewritten. `docs/MertensDecayScalars.md` is unchanged (its lemma is).
