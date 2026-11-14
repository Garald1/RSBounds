# Explicit Rosser–Schoenfeld estimates: partial formalization

> **Height change, 2026-11-07.** Every statement in this project at a fixed
> finite-RH height, outside the `Schoenfeld*.lean` files, now assumes `FiniteRH 1894438.5122`,
> Rosser–Schoenfeld's A = 1894438.51224… rounded down (the first 3 502 500
> zeros), instead of `FiniteRH 1894439`; `Goals.FiniteRH.mono` shows that each
> new theorem implies the old one. The build log, axiom audit and source hashes
> for the new statements are in `logs-claude/`. The Comparator receipts and
> source hashes cited below were made for the earlier `FiniteRH 1894439`
> statements; new psi, RS62 and zero-free Comparator runs for the new
> statements passed on 2026-11-08 (sandboxed; `verification/height-comparator/`).
> Since 2026-11-08 the `Schoenfeld*.lean` files assume `FiniteRH 1894438.5122`
> as well. See `logs-claude/HEIGHT-CHANGE-NOTES.md`.

The **full-range RS62 weighted Mertens and totient inequalities are now
proved**, assuming only `FiniteRH 1894438.5122`. The weighted bound holds for
every real `x > 1`, with the exact constant `E`; the totient bound holds for
every integer `n >= 3`, with no upper restriction on `n`. See the
[exact statements, proof route and receipts](docs/RS62Global.md).
Both final source checks and their transitive axiom audits passed using only
`propext`, `Classical.choice`, and `Quot.sound`. The independent joint
Comparator workflow is running locally; no completed native verdict is
claimed yet. These are standalone Lean 4.35 results, not official IEANTN
verification receipts.

This standalone Lean 4.35 project now proves the requested **RS75 b = 23 psi
entry**:

$$
\mathrm{FiniteRH}(1894438.5122)\;\Longrightarrow\;
|\psi(x)-x|<0.00020211\,x\qquad(x\ge e^{23}).
$$

The public theorem is
[`RosserSchoenfeld1975.psi_error_b23`](RSBounds/RosserSchoenfeld1975.lean).
Finite RH means that every zero in the open critical strip with absolute
ordinate at most 1894438.5122 lies on the critical line. This is the sole
mathematical premise apart from the displayed range of x. The proof uses
four integrations, the historical delta 0.0000211, the certified first 29
zeros, and eight cancellation subintervals. See the
[statement and proof guide](docs/PsiTable1975.md).

The complete theorem has freshly compiled and its transitive axiom audit
uses only `propext`, `Classical.choice`, and `Quot.sound`. Its independent
Comparator has passed statement and definition matching, the allowed-axiom
check, and full replay with Lean's default kernel. The successful replay took
3143.89 seconds; see [the completed receipt](verification/psi-resume-run.json)
and [final log](verification/psi-comparator-resume.log). The original fresh
build/export record is `verification/psi-run.json`. Process sandboxing was
disabled for the workspace's recorded bwrap limitation; this is not a
sandboxed attestation.

The project also proves **Rosser (1941), Theorem 19,
unconditionally for every real `T >= 2`, including zero ordinates**:

$$
|N(T)-F(T)| < 0.137\log T + 0.443\log\log T + 1.588.
$$

Here `N(T)` counts actual zeros of Mathlib's Riemann zeta function with
`0 < Im(rho) <= T`, with analytic multiplicity, and
`F(T) = T/(2*pi)*log(T/(2*pi)) - T/(2*pi) + 7/8`.
The public theorem is
[`Rosser1941.zero_count_bounds`](RSBounds/Rosser1941.lean).
There is no RH or numerical-count premise.

The stronger finite-range estimate **`abs(N(T)-F(T)) < 1` for
`0 <= T <= 100`** is separately proved, with `F(0)=7/8`.
A reusable [certified table](docs/CertifiedZeroTable.md) provides all 29 zeros
through 100, their rational brackets, simplicity, completeness, and inexpensive
bounds on counts at rational thresholds. The [exact table data](data/zeta-zeros-to-100.json)
is also readable without Lean. See [the public theorem guide](docs/ZeroCountTheorems.md)
for precise statements, imports, citations, and verification records.

Both count theorems passed Comparator's statement and definition matching,
allowed-axiom checks, and full replay with Lean's default kernel. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The native
Comparator command took 2747.55 seconds; see the
[completed receipt](verification/zero-count-run.json).
Process sandboxing was disabled because `bwrap` could not mount its required
filesystem in this workspace; this is not a sandboxed attestation.

The separate **RS75 quantitative zero-free region is now proved**:
assuming `FiniteRH 1894438.5122`, zeta is nonzero whenever `abs(Im(s)) >= 21` and
`Re(s) >= 1 - 1/(9.645908801 * log(abs(Im(s))/17))`.
The high-height theorem for `abs(Im(s)) >= 1894438.5122` is unconditional;
finite RH is used only for the bounded-height handoff. The closed boundary
is excluded. The [proof and dependency guide](docs/RS75ZeroFreeAudit.md)
records the exact statement and all component checks. The final theorem
freshly compiles and its public transitive audit uses only the standard three
axioms. Its separate native Comparator run has now passed with the process
sandbox enabled (statement and definition matching, the allowed-axiom check,
and full replay with Lean's default kernel; 2822 seconds). See
[the run record](verification/zero-free-comparator/20261107T053344.584695Z/run.json),
produced by `verification/run_zero_free_comparator.py`. This is a local
Lean 4.35 result, not an official IEANTN receipt.


**Schoenfeld II: every display of Theorem 7\* and Theorem 11 is proved** under
`FiniteRH 1894438.5122` (2026-11-08):

* (5.6b\*) for `x >= exp(22)`, with no other premise
  (`Schoenfeld1976PsiThetaLog.proved`);
* (5.5a\*), (5.5b\*), (5.6a\*), (5.6\*) and Theorem 11 (7.2), (7.3), (7.4), given also
  `Goals.Schoenfeld1976.PsiCert`, `|psi(x)-x| <= (4/5) sqrt(x)` for
  `1500 <= x <= 10^10` (`Schoenfeld1976Theorem7Proved`, `Schoenfeld1976Theorem11Proved`).

Each depends only on `propext`, `Classical.choice`, `Quot.sound`
(`logs-claude/SchoenfeldAudit.lean`, `logs-claude/schoenfeld-axiom-audit-1894438.5122.log`).
PsiCert itself is the kernel-checked campaign in `RSBounds/PsiFinite/`
(`PsiFinite.psi_abs_sub_le_four_fifths_sqrt`); `Schoenfeld1976Final` discharges the
hypothesis with it. The finite ranges are described in
[docs/SchoenfeldFiniteRanges.md](docs/SchoenfeldFiniteRanges.md); statements and dependency
map in [docs/Schoenfeld1976Plan.md](docs/Schoenfeld1976Plan.md).
The stronger 1976 b = 23 coefficient 0.00020171,
the strict count error through height 280, and a certified first-1000 zero
table also remain unproved here. The finite square-root psi bound on `[1500,10^10]` (PsiCert) is now in
`RSBounds/PsiFinite/`; the earlier
[feasibility and reuse investigation](docs/FinitePsiCertification.md) is superseded.

The completed b = 23 proof assembles the actual finite complex zero sums,
including analytic multiplicities, with the averaged explicit formula.
The high-zero estimate uses conjugation and critical-line reflection; the
quantitative zero-free-region target is a separate problem.

| Result | Freshly checked status |
| --- | --- |
| RS62 totient coefficient 2.50637 for at most twenty distinct prime factors | Proved |
| Its corollary for 3 ≤ q ≤ 10^27 | Proved |
| Finite prime-product certificate through 557 and the earlier all-n reduction | Proved as an implication; the completed global proof uses the larger finite handoff below |
| Existing calr finite Mertens-product certificate for every prime from 5 through 100000 | Fresh kernel replay passed; the analytic tail is now supplied under finite RH, closing the all-n totient theorem |
| Exact finite-anchor Abel identities for weighted prime and von Mangoldt sums | Proved |
| Centered Mertens tail identity and variation-to-tail bound | Generic identities and implications proved; the completed RS62 proof uses the separately checked signed J identity and quantitative bounds |
| Signed degree-two explicit formula and passage to infinity | Proved unconditionally for actual multiplicity zero sums; the exact Euler-normalized signed-tail identity is checked |
| First-Mertens Abel identities and Euler normalization | Proved unconditionally; convergence is supplied by the actual zero potential. See [normalized identity](docs/MertensDLimit.md) |
| Global reciprocal-square zero allowance | Proved unconditionally for arbitrary finite actual-zero sets with analytic multiplicities: sum m/gamma^2 < 0.0463; inclusive positive-ordinate cutoffs have bound 0.02315 |
| Reciprocal-square tail above A = 1894438.5122 | Proved: each positive-ordinate finite tail is below 0.0000012, using the unconditional Rosser count estimate |
| Schoenfeld II Theorem 11 Laplace integrals and weight calculus | Exact near/far integral bounds, logarithmic substitution, Phi monotonicity, and the density allowance are checked |
| Schoenfeld II Theorem 11 quadratic smoothing, zero envelope and left contour | Proved under finite RH: `SchoenfeldQuadraticLeft.psi_error_le_envelope` bounds abs(psi(x)-x) by the explicit envelope plus 150000/(delta^2 sqrt x) + log(2 pi) + delta x. Lake build and audits in `verification/schoenfeld-quadratic-lake-audits-20261107.json` |
| Schoenfeld II Theorem 11 for x >= exp(23) | Proved under finite RH: `SchoenfeldTheorem11Ge23.psi_lt`, `theta_lt` and `psi_upper` give abs(psi(x)-x), abs(theta(x)-x) < x eps0(x) and theta(x)-x <= psi(x)-x < x eps0(x). Three ranges: the RS75 b = 23 row up to exp(700), a far-only quadratic envelope up to exp(1737), and Schoenfeld's parameter balance (7.21)–(7.30) beyond. Lake build and audits in `verification/schoenfeld-balance-lake-audits-20261107.json`. Below exp(23): `Schoenfeld1976Theorem11Proved` (PsiCert on [1500, exp(23)], a kernel walk below 1500); see `docs/SchoenfeldFiniteRanges.md` |

| Schoenfeld II Theorem 7*, (5.6b*) for x in [exp(23), exp(38.3)], [exp(100), exp(313)] and x >= exp(947), and (5.6*) for x >= exp(1737) | Proved under finite RH: `Schoenfeld1976Rows23.psiThetaLog_23_383` (from the RS75 b = 23 bound), `Schoenfeld1976Rows4.psiThetaLog_100_313` and `psiThetaLog_ge947` (far-only quartic envelope rows on [exp(100), exp(313)] and [exp(947), exp(1300)], quadratic rows `Schoenfeld1976Rows2` on [exp(1300), exp(1737)], Theorem 11 beyond) and `Schoenfeld1976Large.thetaLog_large`. The rest of (5.6b*) from exp(22) (`Schoenfeld1976Rows22`, `Rows38`, `Rows6`) and of (5.6*) from 758711 (kernel walk and PsiCert) is now proved; see `docs/SchoenfeldFiniteRanges.md` |




| Weighted zero-sum partial summation and envelope transfers | Proved for the actual zeta zeros with analytic multiplicity, using the unconditional Rosser estimate |
| Reciprocal-zero head through 100 | Proved: the complete first-29 head has sum of reciprocal norms less than 0.592316 |
| Elementary reciprocal and fifth-power integrals | Proved with explicit logarithmic upper bounds for 7 ≤ a ≤ b |
| Contour/count/multiplicity conversions | Proved, including strict/inclusive endpoints and conjugation/reflection multiplicity symmetries |
| Eight-band budget and its actual zero-sum domination | Proved; assembled with the explicit formula to give the b = 23 psi bound |
| Backlund's phase-aligned subsequence for powers of a nonzero complex number | Proved |
| Angular Jensen inequality, constructive reflected pairing, and the limit along phase-aligned powers | Proved, including the reflection loss E/(2 pi) and the actual horizontal zeta argument bound |
| Exact zeta/digamma reflection identity and constructive first/last crossings | Proved by selective reuse; no zero-count premise |
| Actual horizontal reflection-error integral | Proved: at most 4 delta^2/T, hence less than 8/T, for T >= 1 and 0 <= delta <= 3/4, at nonvanishing horizontal segments |
| Euler-product center lower bound | Proved in Lean: 3.425 < zeta(5/4)/zeta(5/2) < 3.426, hence norm(zeta(5/4+it)) >= 1/3.426 for every real t |
| Continuous gamma phase remainder | Proved for every T > 0: abs(S_gamma(T)) <= 1/(4T), hence also <= 25/(48T) |
| Trapezoidal error via the positive Peano kernel | Proved, including the finite error-sum identity |
| Continuous zeta branch on the anchor line Re(s) = 5/4 | Proved via the Euler logarithm; the vertical argument integral equals the principal argument and has absolute value at most pi/2 |
| Exact Riemann–von Mangoldt count identity | Proved for positive heights off zero ordinates, with the actual positive-ordinate zeta multiplicities and the continuous gamma phase |
| Backlund (54) | Proved: norm(zeta(sigma+it)) ≤ log(t) − 0.048 for sigma ≥ 1, t ≥ 50 |
| Backlund (56) | Proved: norm(zeta(sigma+it)) ≤ t²/(t²−4) · (t/(2 pi))^((1−sigma)/2) · log(t), for 0 ≤ sigma ≤ 1, t ≥ 50 |
| Backlund (77) | Proved: norm(zeta(sigma+it)) < (t/(2 pi))^(1/2−sigma) · log(t), for −1/2 ≤ sigma ≤ 0, t ≥ 50 |
| Upper half-strip maximum principle and finite bottom-edge certificate | Proved; used with the actual normalized zeta function to establish (56) |
| Quantitative digamma and horizontal Gamma-modulus bounds | Proved by adapting Zeta23's quantitative estimate to IEANTN's checked Gauss series |
| Actual common circle majorant at radius 1.32 and its angular integral | Proved, including nonnegativity, integrability, both translated zeta bounds, and numerical coefficients |
| Rosser's .137/.443/1.588 zero-count estimate | Proved unconditionally for every T ≥ 2, including zero ordinates |
| Uniform zero-count error < 1 through height 100 | Proved for 0 ≤ T ≤ 100, including T=0 and zero ordinates |
| Complete first-29 zero table | Proved; rational brackets, exact multiplicities, completeness, and computable bracket-count bounds |
| Quartic kernel bounds, fourth-difference identities, and the upper/lower psi sandwich | Proved |
| Mellin transform of the truncated quartic, with its exact five-factor denominator | Proved for Re(s) > 0 |
| Fourfold integral identity and low/high bounds for an individual zero's quartic contribution | Proved |
| Finite rectangular residue identity, including the quartic kernel's pole at zero | Proved |
| Prime-sum Mellin inversion using only hypotheses on the right vertical line | Proved |
| Fourfold integrated explicit formula for the actual finite sum Psi4, using one common sequence of rectangle heights | Proved, with the left vertical remainder explicit |
| Upper and lower averaged explicit formulas, including the exact main terms and constant at zero | Proved, with the left remainders explicit |
| Logarithmic bound for zeta'/zeta on Re(s) = -1/2 | Proved |
| Both actual averaged left-line remainders, with delta = 0.0000211 | Proved: at most 25000/(pi sqrt(x)), and less than 0.1 for x >= exp 23; no RH premise |
| Lower kernel bounds and a sharper cancellation bound for both smoothing signs on a finite ordinate band | Proved; used in the completed b = 23 row |
| RS75 Theorem 1: zero-free region with R = 9.645908801 and log(abs(t)/17) | Proved for absolute ordinate at least 21 under finite RH through 1894438.5122; unconditional above 1894438.5122 |
| RS75 real-axis xi/Gamma increments and variable Stechkin parameters | Proved, audited, and assembled into the full zero-free theorem |
| RS75's exact degree-four cosine polynomial and its nonnegativity | Proved |
| Gauss series for digamma and its summability on Re(s) > 0 | Reused from IEANTN GammaAsymptotics.v2; freshly compiled and audited on this toolchain |
| RS62 analytic inputs and the scalar totient reduction | The scalar implication is proved, and its actual inputs above 100000 are now supplied under finite RH |
| Moderate-error psi row b = 23 | Proved for every x ≥ exp 23, assuming only finite RH through 1894438.5122 |
| Full RS62 weighted Mertens and all-n totient inequalities | Proved under only FiniteRH 1894438.5122; independent native Comparator verdict pending |
| Exact Schoenfeld II Theorem 7* and Theorem 11 targets | Proved under `FiniteRH 1894438.5122`, all but (5.6b*) also given PsiCert; see above |

The unconditional zero-count and finite totient results assume neither RH,
Buethe nor Ramare's sum estimate.
The finite arithmetic through the twentieth prime, 71, is checked by the
ordinary Lean kernel. The checked theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

The unrestricted totient inequality is now proved in
`RS62TotientFromFiniteRH.totient_bound_of_finiteRH`, under the sole finite-RH
premise. The finite prime-product check ends at 100000, where the proved
analytic inputs take over; the conclusion covers every integer `n >= 3`.
The earlier unconditional `10^27` corollary remains a historical finite
result, not the final range of the new theorem.

## The b = 23 proof

The chosen method is RS75's **four integrations**, equivalently a degree-four
truncated-power smoothing. The threshold remains `exp 23`.

`Psi4(y) = (1/24) sum_n Lambda(n) max(y-n,0)^4`.

Normalized fourth differences at x and x−4h give upper and lower smoothings
of psi(x), with main terms x+2h and x−2h. The zero contribution has denominator
`rho*(rho+1)*(rho+2)*(rho+3)*(rho+4)`. The parameters remain `m = 4`,
`delta = 0.0000211`, with finite RH through 1894438.5122. The polynomial smoothing
and its finite psi comparisons are checked, as are the bounds for an individual
zero's contribution, for both smoothing signs. The contour is an ordinary fixed rectangle with vertical
sides at Re(s) = -1/2 and Re(s) = 3/2; no quantitative zero-free boundary is
used for it. The integrated formula is now checked, with the residue at zero
evaluated. The actual averaged left remainder is bounded unconditionally by
`25000/(pi sqrt(x)) < 0.1` for `x >= exp 23` at the historical delta.
The quantitative zero-sum estimate and its final assembly are now proved.
See the [completed proof guide](docs/PsiTable1975.md); the older
[quartic formula note](docs/QuarticProof.md) records the earlier construction.

RS75's zero-free region is now proved in `RSBounds/RS75ZeroFree1975.lean`:
assuming the finite RH verification through 1894438.5122, zeta has no zeros where
`abs(t) >= 21` and `sigma >= 1 - 1/(9.645908801 * log(abs(t)/17))`.
This is Theorem 1 of RS75, whose proof uses the finite verification only
below height 1894438.5122. The fixed-parameter b=23 budget in
`docs/QuarticBudgetAudit.md` uses only the critical strip above the finite RH
height, and therefore does not require this quantitative zero-free region.
It does not itself provide a globally decaying `c/log(x)` relative error.
The zero-free theorem and all its analytic inputs are proved and audited;
their dependency chain is documented in
[the zero-free-region guide](docs/RS75ZeroFreeAudit.md).

The needed zero-count estimate is Rosser (1941), Theorem 19, p. 223:

`abs(N(T)-F(T)) < .137 log(T) + .443 log(log(T)) + 1.588`, for T ≥ 2,

where `F(T) = T/(2*pi)*log(T/(2*pi)) - T/(2*pi) + 7/8`.
**The analytic range `T >= 100` is now proved with these exact constants.**
The public count is an unconditional sum of Mathlib's analytic zero orders,
with the inclusive upper endpoint. The endpoint extension is also proved;
the result is not restricted to heights avoiding zeros.

The checked proof includes the angular Jensen/powers step, constructive
reflected crossings, the actual reflection-error integral, the continuous
anchor argument, the exact count/argument-principle identity, and the
branch-correct gamma phase remainder. Backlund's three zeta estimates
(54), (56), and (77) are proved at their original height threshold 50.
The proof of (56) includes its half-strip maximum principle and finite
bottom-edge computation. An actual nonnegative circle majorant is integrated
over all four sectors; the right-arc quadrature and the final constants are
certified in Lean. The rounded envelope is strictly below Rosser's target
for every `T >= 100`.

No finite RH result is used in that analytic theorem. The finite handoff is
also complete: an independently replayed certificate gives all 29 zeros through
100, and the checked rational endpoint inequalities prove the stronger error
`< 1` throughout `[0,100]`. Combining the ranges proves the full theorem. See [the circle-majorant audit](docs/BacklundCircleMajorantAudit.md),
[the Gamma-modulus audit](docs/BacklundGammaModulusAudit.md),
[the primary-source audit](docs/BacklundCountAudit.md) and
[the current IEANTN/PNT+ reuse audit](docs/ZeroCountReuseAudit.md).

The printed center denominator `3.425` needs care: an independent exact
rational computation puts `zeta(5/4)/zeta(5/2)` between `3.425382` and
`3.425390`. Lean now proves the sufficient enclosure `(3.425, 3.426)` and
the center lower bound with denominator `3.426`; the 625-term sums and their
integral-test tails use no numerical axiom. This does not assert
a failure of the final counting theorem. See [the center audit](docs/BacklundCenterAudit.md).
The unconditional certificate for all 29 zeros through height 100 is reused
from `teal-sea/zeta-lab`. All 99 modules have been replayed on this toolchain,
and all 28 pinned axiom audits passed. Its complete table and the resulting
finite-range error theorem are public exports. It is not imported by the
separate analytic `T >= 100` theorem. See [the finite-height audit](docs/LowHeightCertificateAudit.md).
The older RS75 row uses a finite head of 57 zeros; the improved 1976 row uses
a larger head. Those larger numerical zero certificates remain to be formalized. The new
[first-29 route](docs/QuarticFirst29Budget.md) supplies a checked smaller head
and scalar budget and completes the b=23 assembly using that smaller head.

## Reuse from IEANTN

The Gauss-series representation is imported from the actual proved solution
`GammaAsymptotics.v2`, not from a challenge or node statement. Eight original
proof modules compile unchanged apart from import paths; attribution, license,
upstream hashes, and fresh audits are retained. See
[the port record](docs/IEANTNGammaPort.md) and
[the targeted reuse audit](docs/IEANTNReuseAudit.md).

The quantitative vertical digamma estimate is adapted from Zeta23's
`GammaFacts/StirlingVert.lean` in `teal-sea/zeta-lab`, pinned at
`b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, with IEANTN supplying the
proved series input. The half-strip maximum principle adapts Mathlib's
Phragmén–Lindelöf argument. These are checked proof ports, distinct from the completed finite-height
replay. The local Gamma ports have isolated namespaces so both developments
can be imported together; the affected dependency chain was rebuilt and audited. Original notices, pinned source links, and
licenses are recorded in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

## Reproduction

Run from this directory, using its own toolchain:

```sh
lake exe cache get
lake build
lake comparator
lake comparator --config comparator-zero-count.json
python verification/run_psi_check.py
```

`RSBounds.lean` imports completed modules only. `RSBounds/Targets.lean` defines
propositions, not proofs or axioms. Other source files may be under development.

Three independent Comparator configurations are provided: `comparator.json`
for the restricted totient statements, `comparator-zero-count.json` for
the full Rosser count theorem and the strict finite-range error bound, and
`comparator-psi.json` for the b = 23 psi theorem under finite RH. Use the
Python driver shown above for the psi check; it compiles the independent
challenge and solution directly and passes their fresh exports to Comparator.
All three configurations have passed their independent statement/definition,
allowed-axiom, and default-kernel checks.
None asserts the unfinished global theta, full RS62, or zero-free-region
goals. All completed public theorems have fresh Lean builds and transitive
axiom audits, using only `propext`, `Classical.choice`, and `Quot.sound`.
Fresh build logs, axiom audits,
and exact source hashes are in `verification/`. Comparator outcomes and any
sandbox limitation are recorded there.

The dependency `calr3/ternary-goldbach` is pinned at
`192ca57362fa3ee737cd83205cb9ea99526c4553`; all revisions are in
`lake-manifest.json`. See `THIRD_PARTY_NOTICES.md` for attribution.

## Licence

Apache License 2.0 (`LICENSE`), since 2026-11-14; before that, MIT. A few files remain under
MIT; they are listed in `THIRD_PARTY_NOTICES.md`.

## Sources

- [Rosser (1941), Theorem 19](https://doi.org/10.2307/2371291).
- [Backlund, Acta Mathematica 41, pp. 345–375](https://doi.org/10.1007/BF02422950).
- [Rosser–Schoenfeld (1975), Lemmas 7–9 and Theorem 4](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
- [Schoenfeld (1976)](https://doi.org/10.1090/S0025-5718-1976-0457374-X).
- [Rosser–Schoenfeld (1962)](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).
