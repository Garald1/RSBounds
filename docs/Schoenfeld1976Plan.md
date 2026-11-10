# Exact Schoenfeld II targets and dependencies

Source: L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and
ψ(x), II*, Math. Comp. 30 (1976), 337–360,
[doi:10.1090/S0025-5718-1976-0457374-X](https://doi.org/10.1090/S0025-5718-1976-0457374-X).
The statements were checked against the supplied scan, not OCR alone, and
rechecked against the scan on 2026-11-07, including every display of both
theorems and the table on p. 358.

`RSBounds/Schoenfeld1976Targets.lean` and `RSBounds/Schoenfeld1976TargetsExtra.lean`
record the specifications. **Status (2026-11-08):** all eight displays below are
proved, under `Goals.FiniteRH 1894438.5122`:

- (5.6b*) for `x >= exp(22)` with no other premise
  (`Schoenfeld1976PsiThetaLog.proved`);
- (5.5a*), (5.5b*), (5.6a*), (5.6*) and Theorem 11 (7.2), (7.3), (7.4) given also
  `Goals.Schoenfeld1976.PsiCert`, `|psi(x)-x| <= (4/5)sqrt(x)` for
  `1500 <= x <= 10^10`, a finite computation certified outside this project
  (`Schoenfeld1976Theorem7Proved`, `Schoenfeld1976Theorem11Proved`).

Every one depends only on `propext`, `Classical.choice`, `Quot.sound`
(`logs-claude/SchoenfeldAudit.lean`, `logs-claude/schoenfeld-axiom-audit-1894438.5122.log`).
The finite ranges are described in `docs/SchoenfeldFiniteRanges.md`. Theorem 11
for `x >= exp(23)` is `RSBounds/SchoenfeldTheorem11Ge23.lean`; see
`docs/SchoenfeldTheorem11Balance.md`.

The earlier proposed constant 0.1 is superseded by these targets; any checked
auxiliary estimate remains usable.


Put `X = sqrt(log x / 9.645908801)` and
`epsilon0(x) = sqrt(8/(17*pi)) * sqrt(X) * exp(-X)`.

| Target | Statement | Printed page |
|---|---|---|
| Theorem 11, (7.2) | `abs(psi(x)-x) < x*epsilon0(x)` for `x >= 17` | 342 |
| Theorem 11, (7.3) | `abs(theta(x)-x) < x*epsilon0(x)` for `x >= 101` | 342 |
| Theorem 11, (7.4) | `theta(x)-x <= psi(x)-x < x*epsilon0(x)` for `x >= 1` | 342 |
| Theorem 7*, (5.6*) | `abs(theta(x)-x) < 0.0239922*x/log(x)` for `x >= 758711` | 357 |
| Theorem 7*, (5.6b*) | Both errors `< 0.0077629*x/log(x)` for `x >= exp(22)` | 357 |

The printed (7.4) reads `theta(x)-x <= psi(x)-x eps0(x) if 1 <= x`: a relation
is missing, and read literally it is false. The proof on p. 349 shows
`psi(x) < x + x*eps0(x)` for `1 <= x <= 10^8` and then says this completes
"(7.4), (7.2) and (7.3)", so the target uses the form in the table. For
`x >= 17` it follows from (7.2); the rest is a finite check.

Theorem 7* also states (5.5a*) `abs(psi(x)-x) < 0.0220646*x/log(x)` for
`x >= 161971`, (5.5b*) `-0.0220646*x/log(x) < psi(x)-x` for `x >= 89909`, and
(5.6a*) `theta(x)-x < 0.0201384*x/log(x)` for `x > 1`. These are targeted in
`Schoenfeld1976TargetsExtra.lean` (2026-11-07). The paper derives the upper half
of (5.6*) from (5.6a*); the formal proof does not need that.

All formal statements expose `Goals.FiniteRH 1894438.5122` (until 2026-11-07,
`Goals.FiniteRH 1894439`; RS75's A = 1894438.51224... rounded down, the first
3 502 500 zeros). This is
the finite certificate left to the caller; it is not full RH. The historical
paper incorporates its finite zero computation into its unconditional results.
The current formal proofs must keep any unverified numerical inputs visible.

## Completed inputs

- The RS75 closed zero-free boundary
  `1 - 1/(9.645908801*log(abs(t)/17))`, unconditionally for
  `abs(t) >= 1894438.5122` (from `1894439` until 2026-11-07). Its extension down
  to 21 uses the finite RH premise.
- Rosser's actual multiplicity-count estimate
  `abs(N(T)-F(T)) < .137*log(T)+.443*log(log(T))+1.588` for `T >= 2`.
- The complete first 29 zeros through height 100, including their simplicity,
  rational enclosures and exhaustion.
- The RS75 quartic-smoothed b=23 result with coefficient `.00020211`, under
  finite RH through 1894438.5122. This result does **not** use the quantitative
  zero-free region.
- Weighted zero partial summation and actual zero-sum/multiplicity bridges.

## Theorem 11 proof to implement

Section 7 uses quadratic smoothing (`m=2`) and splits at
`T2 = 17*exp(v*X)`. The elementary bounds behind (7.11) and (7.18) must retain
the paper's coefficients, followed by the choice of `v` and `delta` in
(7.24)–(7.30), and the explicit residual estimates through (7.42); the final
step uses `E(x) < 1` for `log x >= 721`, from (7.42).

The critical-line term uses Rosser 1941, Lemma 17: first ordinate greater than
14.13 and the all-ordinate reciprocal-square sum less than .0463. Both are now
proved here; the envelope uses
`SchoenfeldReciprocalSquare.rectangle_reciprocal_square_sum_lt`. The paper's
theta transfer uses `psi-theta < 1.43*sqrt(x)`; the formal proof uses
`PsiThetaElementary.psi_sub_theta_le`, `psi-theta <= 6.5*sqrt(x)` for
`x >= 10^5`, which suffices at this size.

The analytic argument proves the displayed error for `x >= exp(1737)`, and
that intermediate result is now formal (`SchoenfeldTheorem11Analytic`). Its
residual estimates keep the slack `1-d`, `d = log(17/(2*pi))`, as an explicit
factor instead of reproducing the constants of (7.31)–(7.42); see
`docs/SchoenfeldTheorem11Balance.md`. Theorem 11's full smaller ranges require
the paper's additional table and finite checks, so Theorem 11 is not complete.


The smaller ranges (pp. 348–349) go through (7.43), the stronger factor 0.802
on `[10^8, exp(1737))`. It uses the table bound 0.00121 for `x >= 10^8`, the
value `1.42e-5` for `x > exp(350)`, rows b=1200,1400,1500,1600 of "the table in
Section 5", and rows b=1650,1700 of the 1976 table. Below `10^8` it uses RS62
Theorem 10 and (3.35), `eps0(x) > 0.11` on `[2,10^8]`, and finite checks on
`139 <= x < 149` (theta) and `17 <= x < 101` (psi). Theorem 11 itself only
needs a factor below 1 there. Recomputed with the 1976 rows, the maximum is
0.8014, on `[exp(1700), exp(1737))`, so these rows have about 20% slack.

## Table route to (5.6b*)

On `x >= exp(1737)`, `eps0(x)*log(x) <= 0.0045`, so the analytic range of
Theorem 11 already gives (5.6b*) and (5.6*) there:
`Schoenfeld1976Large.psiThetaLog_large` and `thetaLog_large` (finite RH
explicit). For (5.6b*) this now extends down to `exp(1300)`
(`Schoenfeld1976Rows2.psiThetaLog_ge1300`), from the far-only quadratic envelope
with fixed `δ` on `[1300,1400]`, `[1400,1550]` and `[1550,1737]` in `log x`,
and further down to `exp(947)` (`Schoenfeld1976Rows4.psiThetaLog_ge947`), from
the far-only quartic envelope (`SchoenfeldQuarticFar.psi_error_le_farEnvelope4`)
with fixed `δ` on `[947,957]`, `[957,973]`, `[973,1000]`, `[1000,1046]`,
`[1046,1129]` and `[1129,1300]`. The quartic rows stop working near
`log x = 921`. The same quartic envelope, keeping its critical-line term, also
gives (5.6b*) on `exp(100) <= x <= exp(313)`
(`Schoenfeld1976Rows4.psiThetaLog_100_313`, five rows); between `exp(313)` and
`exp(921)` order 4 is not enough, and lower rows need order 5 or 6.
On `exp(23) <= x <= exp(38.3)` the RS75 `b = 23` bound itself gives (5.6b*)
(`Schoenfeld1976Rows23.psiThetaLog_23_383`).
These gaps are now closed (2026-11-07): `exp(22) <= x < exp(23)` by the RS75
`b = 23` chain at `x^{1/2}` and `psi-theta <= 1.212 sqrt(x)`
(`Schoenfeld1976Rows22`), `exp(38.3) < x < exp(100)` by the same chain as a
function of `x` (`Schoenfeld1976Rows38`), and `exp(313) < x < exp(947)` by an
order-6 far-only envelope in eleven rows (`SchoenfeldSextic*`,
`Schoenfeld1976Rows6`). (5.6*) below `exp(22)` is in `docs/SchoenfeldFiniteRanges.md`.


Planning numerics (2026-11-07; not proofs). Section 8 says the table was
recalculated from RS75's Theorems 4 and 5 with the devices listed there. A
far-only envelope split at A, with m-th order smoothing and the zero-free
region (the Laplace bounds `farPrimitive` and `Phi` already allow general m),
comes within 0.7% of the 1976 rows b=800,1000,1150,1350 for m = 6, 5, 4, 3,
within 3% at b=650 (m=6), and within 7% at b=1650 and 1700 (m=2)
(`scripts/schoenfeld_table_planning.py`). The project's kernels cover only
m = 2 and m = 4; rows near b=400–800 need m = 5 or 6. Separately, the existing
quadratic envelope with `U >= A` gives Theorem 11 pointwise down to about
`log x = 1560` (ratio 0.95 at 1600, 1.01 at 1550;
`scripts/schoenfeld_below_1737.py`). Rows b=22 and b=35 would follow the
method of the proved b=23 row.




The published proof uses rows b=22,23,35,400,550,650,700,750,800,850,900,950,
1000,1050,1150,1350 and then Theorem 11 beyond `exp(1950)`.
There is no required prime enumeration below `exp(22)` for this target.
Theorem 11 enters only for `x >= exp(1950)`, inside its analytic range, so
(5.6b*) does not depend on Theorem 11's smaller ranges.

The improved 1976 b=23 row is `.00020171`, distinct from our proved 1975
row `.00020211`. Its published recipe uses a head of 12555 positive zeros,
far more than the first 100. Numerical planning checks indicate that the
older rows at b=22,23,35 still suffice for (5.6b*); these checks are not Lean
proofs. For b>=40 the paper says that the larger head does not improve its
table values. At b=800 the interval budget is tight:
`9.1328e-6 * 850 = .00776288`, leaving only `2e-8` before the stated constant.
A recomputation of the whole chain from the p. 358 table confirms that every
other interval has slack at least `3.4e-5`.

Section 8 (p. 353) says the 1976 table added the rows b=550(100)1050, among
others, and lowered six old values with `800 <= b <= 1350` by 1 or 2 units.
So this route depends on the 1976 recomputation, not on the 1975 table, and
it needs `eps(800) <= 9.13282e-6`, within a quarter unit of the printed digit.
A fresh table proof can choose its own breakpoints: adding b=825 removes the
dependence on that last digit.

RS75's historical A is the real solution of `F(A)=3502500`, approximately
1894438.51224, with `N(A)=F(A)`. The formal premise is `FiniteRH 1894438.5122`, A rounded
down; the integer 1894439 would claim one zero more (LMFDB: zero 3 502 501 at 1894438.63746).
A fresh table proof must retain and bound its own boundary-count terms; it must
not silently transfer the historical equality `N(A)=F(A)` to the rounded height.

## Additional work for (5.6*)

Done (2026-11-07), without the historical tables: the threshold 758711 and the
range up to `1.35*10^6` come from a kernel-checked walk of `theta` and `psi`
(`SchoenfeldPrimeWalk`), the range up to `exp(22)` from PsiCert, and the rest from
(5.6b*); see `docs/SchoenfeldFiniteRanges.md`. The walk also gives `theta(x) < x`
below `2.5*10^5` for (5.6a*); above that (5.6a*) uses PsiCert and (5.6b*), not
RS62 (4.5).

## IEANTN submission

The first submission is the already proved RS75 b=23 result, as a new
conditional node/version. It must not overwrite the existing unconditional
zero-free-region node. Our native Comparator receipt belongs to the existing
Lean 4.35 build. IEANTN currently pins Lean 4.34.0-rc2 and its own Mathlib
revision; its integration and official verification are separate obligations.
