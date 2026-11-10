# Theorem 11: the parameter balance and the range x ≥ e^23

Status (2026-11-07): **proved for every `x ≥ e^23`**, given `FiniteRH 1894439`.
`RSBounds/SchoenfeldTheorem11Ge23.lean` contains

- `psi_lt`: `|ψ(x) − x| < x ε₀(x)`;
- `theta_lt`: `|θ(x) − x| < x ε₀(x)`;
- `psi_upper`: `θ(x) − x ≤ ψ(x) − x < x ε₀(x)`,

each for `Real.exp 23 ≤ x`, with `ε₀` = `Goals.Schoenfeld1976.epsilon0` from the target file.
The proof has three ranges:

| Range | Module | Method |
|---|---|---|
| `e^23 ≤ x ≤ e^700` | `SchoenfeldTheorem11B23` | the proved RS75 row b = 23, `0.00020211 < 2.1·10⁻⁴ ≤ ε₀(x)` |
| `e^700 ≤ x < e^1737` | `SchoenfeldTheorem11Far`, `SchoenfeldTheorem11Ge23.core_far` | far-only quadratic envelope (`SchoenfeldQuadraticFar`), `δ = ε₀(x)/2`; bound ≤ 0.943 x ε₀(x) |
| `x ≥ e^1737` | `SchoenfeldTheorem11Analytic` | Schoenfeld's parameter balance (below) |

Lake build; every declaration of these modules and of the balance modules behind them (110 in
all, including `Schoenfeld1976Large`) depends only on `propext`, `Classical.choice` and
`Quot.sound` (`verification/schoenfeld-balance-lake-audits-20261107.json`).

The target propositions `PsiTheorem11`, `ThetaTheorem11` and `PsiUpperTheorem11` are **not**
proved: they also cover `17 ≤ x`, `101 ≤ x` and `1 ≤ x`. Below `e^23` the paper uses its table
bound for `10^8 ≤ x` and, below `10^8`, RS62's bounds and finite checks (pp. 348–349; see
`Schoenfeld1976Plan.md`).


The middle range departs from the paper, which uses its table there ((7.43)). Splitting the zeros
at `A = 1894439` itself removes the near region, and with it the condition
`log(U/17)² ≤ log x / R` that forces `log x ≥ 1302.6` when `U ≥ A`. The far allowance is then at
most `0.027 (c₀ s)³` (`far_le`, checked on `8.5 ≤ X ≤ 11`, `11 ≤ X ≤ 12.5`, `12.5 ≤ X ≤ 13.42`).

The rest of this note describes the analytic range `x ≥ e^1737`.

## Inputs

`SchoenfeldQuadraticLeft.psi_error_le_envelope`: for `x > 1`, `0 < δ`, `2δ < 1`,
`1894439 ≤ U` and `log(U/17)² ≤ log x / R < 2 log(U/17)²`,

    |ψ(x) − x| ≤ envelope x δ U + 150000/(δ²√x) + log(2π) + δx,   given FiniteRH 1894439,

where `envelope` is the quadratic-smoothing (`m = 2`) bound: the critical-line term
`(R₂(δ)/δ²)√x·0.0463/14.13`, and `x((1 + δ)·near + (R₂(δ)/δ²)·far)` for the zeros above `U`.

## Modules (new files only; the RS62/RS75 closure is unchanged)

1. `SchoenfeldBalanceAlgebra`: `G₀`, `G₁`, `Y` of (7.12), (7.19), (7.10); closed forms of the near
   and far primitives at `a = X²`, `u = vX`; `X/v = Y + 2X − vX`; the window lemma.
2. `SchoenfeldBalanceV`, `SchoenfeldBalanceVNumeric`: `H(v)` bounds (7.28), `k(v₀) < 1 < k(v₁)`,
   continuity of `k` (7.27), and `exists_split_parameter`: for `X ≥ 13.41` there is
   `v ∈ (v₀, v₁)` with `k(v) = 1` (7.29)–(7.30).
3. `SchoenfeldBalanceHeight.split_height_ge`: `T₂ = 17e^{vX} ≥ 1894439` for `v ≥ v₀` and
   `X ≥ 13.4192`, which `log x ≥ 1737` gives. The margin is about 0.002 in `log T₂`, so 1737 is
   essentially the threshold of this step, as on p. 345.
4. `SchoenfeldBalanceMain`: `δ` of (7.24a); (7.21) as `k(v) = 1 ⟹ δT₂ = 2√(G₁/G₀)`; the main
   terms add up to exactly `δ` (`main_terms_eq`); closed forms of both allowances; `G₂` of (7.20);
   and `allowances_le`, the analogue of (7.26):
   `(1 + δ)·near + (R₂/δ²)·far ≤ G₂δ + (2R(T₂)e^{−Y}e^{−2X}/17)·G₂(1 + G₀/G₁)`.
5. `SchoenfeldBalanceTail`: the residual estimates (below).
6. `SchoenfeldTheorem11Analytic`: assembly and the three theorems.

## How the residual estimates differ from pp. 345–348

The paper bounds everything by `ε₀(x)·M(v)L(v)` (7.37) through the constants 0.0241, 0.0482,
0.11, 0.61, 0.29, 0.62, 0.92 and 3.68, and then shows `L(v) < 1` (7.40) and `M(v) < E(x) < 1`
(7.41)–(7.42). The slack that absorbs every residual term is `d = log(17/2π) ≈ 0.99535 < 1`: on
p. 347 `G₀ = v²(v + d/X)` is replaced by `v²(v + 1/X)`.

The formal proof keeps that slack as an explicit factor instead. With `P = (G₀G₁)^{1/4}e^{−Y/2}`,
so that `2δ = P ε₀(x)`:

- `LM_le`: `v⁴(v + 1/X)(v + 3/(2X))e^{−2Y} ≤ 2v² − 1`, i.e. `L(v)⁴M(v)⁴ ≤ 1`. It uses
  `v⁶ ≤ 2v² − 1` for `0.8 ≤ v ≤ 1`, `(1 + a)(1 + b) ≤ e^{a+b}`, and `2X(1 − v) ≥ 9/4 > √5`,
  which `v < v₁` gives (`gap_of_lt_v1`).
- `P4_le`: `P⁴ ≤ 1 − (1 − d)/(X + 1)`, hence `P ≤ 1 − (1 − d)/(4(X + 1))`.
- `d_le`: `d ≤ 0.996`.
- `tail_le`: `X(X + 1)e^{−X} ≤ 2.95·10⁻⁴` for `X ≥ 13.4192`, by monotonicity via
  `e^s ≥ 1 + s + s²/2` (no derivatives).
- `q_bounds`, `G2_bounds`: `0 ≤ q(T₂) ≤ 0.015/T₂`, so `2πq(T₂) ≤ δ/10` and `1 ≤ G₂ ≤ 1 + 4δ`.
- `rosserR_bounds`: `0 ≤ R(T₂) ≤ X` (the paper's (7.13) amounts to `R(T₂) < 0.41X`); with `Y ≥ 0` the

  boundary factor is at most `(2/17)Xe^{−2X}`.
- `small_terms_le`: the critical-line, left-contour, `log 2π` and `ψ − θ` terms together are
  at most `10⁻⁴ x √X e^{−X}/(X + 1)`, using `1/δ² ≤ 72.25e^{2X}` (from `δT₂ ≥ 2`) and
  `log x ≥ 8X + 80`.

`close_arith` then combines: with `s = √X e^{−X}` and `u = s/(X + 1)`, the total is at most
`x ε₀ − x u((1 − d)c₀/4 − 1.2·10⁻⁴ − 10⁻⁴)` with `c₀ = √(8/(17π)) ≥ 0.38`, and
`(1 − d)c₀/4 ≥ 3.8·10⁻⁴`. So the residual terms use under 60% of the available slack, for every
`x ≥ e^1737`, not only at the threshold.

The θ bound uses `PsiThetaElementary.psi_sub_theta_le`, `ψ(x) − θ(x) ≤ 6.5√x` for `x ≥ 10⁵`, in
place of the paper's `1.43√x`; at this size either is negligible.

## Numerics used for planning (not part of the proof)

Ratio of the formal bound to `x ε₀(x)` with Schoenfeld's `v` and `δ`: 0.926 at `log x = 1737`,
tending to 1 (0.99992 at `log x = 10¹²`), as `M(v)L(v) → 1` predicts. So no fixed numerical
choice of `v` can work for all large `x`; the proof follows the root of `k(v) = 1`. Scripts:
`scripts/schoenfeld_balance_margin.py`, `scripts/schoenfeld_check_7_26.py`.
