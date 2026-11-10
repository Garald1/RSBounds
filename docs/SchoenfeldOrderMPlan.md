# Order-m far-only envelope: plan (2026-11-07)

Goal: table-quality bounds `|ψ(x) − x| ≤ ε(b) x` for `x ≥ e^b`, `400 ≤ b < 1737`, for the
table route to (5.6b*) (`Schoenfeld1976Plan.md`). Section 8 of the paper recalculates its table
from RS75's Theorems 4 and 5; numerically, a far-only envelope (all zeros above `A = 1894439`
treated with the zero-free region, none in a near region) with order-`m` smoothing reproduces
the 1976 rows within 0.7% at b = 800, 1000, 1150, 1350 for m = 6, 5, 4, 3
(`scripts/schoenfeld_table_planning.py`). (5.6b*) needs `ε(b)·b' + (θ correction) ≤ 0.0077629`
on each interval `[e^b, e^b')`, which fails for `m ∈ {2, 4}` on about `400 ≤ b ≤ 920`; there
m = 5 or 6 is needed.

## The envelope

For order `m`, smoothing width `δ` and `x = e^b`:

    |ψ(x) − x| ≤ x·(m/2)·δ                                  (smoothing loss)
               + (R_m(δ)/δ^m)·√x·Σ_{γ≤A} 1/|γ|^{m+1}         (critical line, finite RH)
               + x·(R_m(δ)/δ^m)·F_m(log x / R)                (zeros above A, zero-free region)
               + left contour + log 2π,

with `R_m(δ) = ((1+δ)^{m+1} + 1)^m` and
`F_m(a) = (1/(2π) + q(A))·farPrimitive a d m (log(A/17))/17^m + 2R(A)·Phi a m A`.

## What exists

| Piece | m = 2 | m = 4 | general m |
|---|---|---|---|
| Mellin kernel `1/(s(s+1)…(s+m))` | `QuadraticMellin` | quartic chain (`Polynomial*`) | — |
| contour shift, left remainder | `QuadraticContourLimit`, `QuadraticZetaFormula` | `PolynomialExplicitFormula`, `PolynomialLeftRemainder` | — (to check: whether the m = 2 contour hypotheses, inverse-square decay of the numerator, cover higher m) |
| m-fold differences / smoothing of ψ | `QuadraticPsi`, `QuadraticAveragedFormula` | `PolynomialSmoothing`, `PolynomialPsi` | — |
| zero kernel bound `R_m(δ)/δ^m` | `QuadraticZeroKernel`, `SchoenfeldQuadraticKernel` | `PolynomialZeroKernel` (`R4`) | — |
| zero pairing (reflection, conjugation) | `SchoenfeldQuadraticPsi` | `PolynomialZeroPairing` | — |
| zeros above A with the zero-free region | `SchoenfeldQuadraticPsi.norm_upper_sum_le` | **done:** `SchoenfeldQuarticFar.norm_upper_sum_le4`, `norm_lower_sum_le4` | — |
| far weighted sums `Σ_{γ>A} Phi a m` | `far_sum_le` | — | **done:** `SchoenfeldWeightedZerosM.far_sum_le_m` |
| far-only assembly | **done:** `SchoenfeldQuadraticFar.psi_error_le_farEnvelope` | **done:** `SchoenfeldQuarticFar.psi_error_le_farEnvelope4` | — |
| left remainder, general `δ` | `SchoenfeldQuadraticLeft` (`150000/(δ²√x)`) | **done:** `PolynomialRemainderGeneral` (`700/(δ⁴√x)`, `δ ≤ 0.01`) | — |
| critical-line sum `Σ 1/|γ|^{m+1}` | from `SchoenfeldReciprocalSquare` (`0.0463/14.13`) | **done:** `SchoenfeldQuarticFar.rectangle_reciprocal_fifth_sum_lt` (`0.0463/14.13³`) | `≤ 0.0463/14.13^{m−1}` follows the same way |

## Order of work

1. Done: `far_sum_le_m` (any `m ≥ 1`, condition `a < m log(A/17)²`).
   Done for m = 2: rows `[1300,1400]`, `[1400,1550]`, `[1550,1737]` in `log x`
   (`Schoenfeld1976Rows2`), giving (5.6b*) for `x ≥ e^1300`. With the same crude bounds the
   order-2 envelope reaches about `log x = 1240`.

2. Done: the quartic far-only envelope (`SchoenfeldQuarticFar.psi_error_le_farEnvelope4`, with the
   general-step left remainder of `PolynomialRemainderGeneral`) and six order-4 rows
   (`Schoenfeld1976Rows4`), giving (5.6b*) for `x ≥ e^947`. With these constants the order-4 rows
   stop working near `log x = 921`. Keeping the critical-line term, five more order-4 rows give
   (5.6b*) on `[e^100, e^313]` (`psiThetaLog_100_313`); order 4 fails on about `[313, 921]`,
   where `ε(b)·b` peaks near `b = 560`, and below about `b = 90`, where the critical-line zeros
   need the treatment of the b = 23 row. Notes from before the work: a quartic far-only envelope from
   the existing m = 4 chain plus the zero-free region gives the rows near b = 920–1350 and tests
   the assembly. Inputs found: the generic lemma
   `SchoenfeldCoefficientPairing.norm_sum_le_critical_and_weighted_high` takes any coefficient
   with `‖K ρ‖ ≤ C(|γ|) x^β`, and `PolynomialZeroPairing.norm_zeroCoefficient_upper_le_high` /
   `lower_le_high` give exactly `(R4 δ/δ⁴) x^β/|γ|⁵` for every `δ`; the quartic explicit formula
   (`PolynomialPsiFromZeroSums.upper/lower_error_of_eventually_bounded_zero_sums`) is general in
   `h = δx`. Missing: a quartic left-remainder bound for general `δ`; the existing one,
   `PolynomialRemainderBound.norm_upper_leftRemainder_lt`, is for `δ = 0.0000211`, `x ≥ e^23`.

3. The general-m kernel: Mellin transform of `(1 − u)_+^m/m!`, the m-fold difference identity
   for ψ, `R_m(δ)` bound for a single zero, pairing. Prove by induction on `m` where the m = 2 and
   m = 4 files use explicit expansions.
4. The general-m left-contour bound (the m = 2 bound is `150000/(δ²√x)`).
5. Rows: for each interval, a fixed `(m, δ)` and the monotone decrease of the far term in `x`;
   numerical checks as in `SchoenfeldTheorem11Far.far_le_piece`.

The rows b = 22 and b = 35 (below 400) would follow the method of the proved b = 23 row; they
are not part of this plan.
