# [H] (14.3), (14.24), (14.51) and (14.28) with Helfgott's constants

[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2. calr3/ternary-goldbach
proves these four with weaker constants (`|η₊| ≤ 1.94`, `t|η₊(t)| ≤ 2.32`, `35.5` for `7.3306`,
`8·10⁻¹¹` for `8.4029·10⁻¹²`). `RSBounds/HelfgottAppA/` proves [H]'s constants, about calr3's own
definitions (`TernaryGoldbach.Helfgott.etaPlus`, `repSum`, …):

| theorem (`RSBounds.HelfgottAppA`) | [H] | statement | hypotheses |
|---|---|---|---|
| `abs_etaPlus_le_1079955` | (14.3) | `|η₊(t)| ≤ 1.079955`, `t ≥ 0` | none |
| `mul_abs_etaPlus_le_119073` | (14.24) | `t |η₊(t)| ≤ 1.19073`, `t ≥ 0` | none |
| `nonprime_input_book` | (14.51) | non-prime terms `≤ 7.3306 N^{3/2} log N`, `N ≥ 10²⁷` | `|η_*| ≤ 1.414`, `ψ(n) ≤ 1.03883 n`, `ψ − θ < 1.4262 √y` |
| `E_le_book_formula` | (14.28) | `E ≤ (2.94325 log x + 5.12426) √x`, `x ≥ 1` | `ψ(n) ≤ 1.03883 n`, `ψ − θ < 1.4262 √y` |
| `E_le_14_28_book` | (14.28) | `E ≤ 8.4029·10⁻¹² x`, `x ≥ 4.9·10²⁶` | the same |

The hypotheses are stated as calr3's current main proves them: `Helfgott.abs_etaStar_le_1414`,
`Prelim.psi_bounds` and `Prelim.sum_vonMangoldt_nonprime_lt` (the last two from `PlattGRH`). They
are hypotheses because RSBounds pins an older calr3 revision (`192ca57`), which does not have the
first, and so that RSBounds need not build calr3's ψ tables. `E` is written exactly as in calr3's
`E_le_14_28`, and the non-prime terms exactly as in calr3's `nonprime_input`, so each theorem
replaces calr3's by a one-line application.

## The sup norms of `η₊` (`EtaPlusSup.lean`)

[H, App. A.5] derives (14.3) from (A.36), `|h_H(t) − h(t)|/t < |h'|_∞ (1 + (4/π) log H)/H`.
(A.36) is false for very small `t`. Its proof bounds `e^{−w/H}` by `e^{−|w|/H}` on the half-line
`w < 0` as well, where `e^{−w/H} > 1`. `h_H(t)` decays only like `1/|log t|` as `t → 0⁺` (the
cut-off of `ĝ` at `±H/2π` is a jump), while `h(t) ≍ t²`. Numerically, with `H = 200`,
`|h_H(t) − h(t)|/t` is between 4 and 7 at `t = e^{−20}` and about `10⁹` at `t = e^{−40}`, against
the claimed bound `0.109` (two independent floating-point computations,
`scripts/appA_hH_small_t_fourier.py` and `scripts/appA_hH_small_t_direct.py`; they agree in order of
magnitude only). (14.3) and (14.24)
themselves are true with room to spare (numerically `|η₊|_∞ ≈ 1.0000001`); the proof here goes
another way:

* `h_H(eᵘ)` is `g(u) = h(eᵘ)` with its Fourier transform cut off at `|ξ| ≤ H/2π` (calr3's
  `MajorArcs.hH_eq_fourier`). By Fourier inversion (Mathlib's `Continuous.fourierInv_fourier_eq`),
  `|h(t) − h_H(t)| ≤ ∫_{|ξ| > H/2π} |ĝ(ξ)| dξ`.
* Two integrations by parts (Mathlib's `Real.fourier_deriv`) give `(2πξ)² |ĝ(ξ)| ≤ ‖g''‖₁`, so
  `|h − h_H| ≤ ‖g''‖₁/(πH)`.
* `g''(u) = eᵘ (t h'(t))'|_{t=eᵘ}`, `(t h'(t))' = e^{t−1/2} V(t)` with `|V| ≤ 13` on `[0, 2]`, so
  `‖g''‖₁ ≤ 13 (e^{3/2} − e^{−1/2}) ≤ 50.4` and `|h − h_H| ≤ 0.0803` (`abs_hBase_sub_hH200_le`).
* `h(t) t e^{−t²/2} = (t(2 − t))³ e^{−(t−1)²/2} ≤ 1` and `h(t) t² e^{−t²/2} ≤ 1.106`, so
  `|η₊| ≤ 1 + 0.0803/1.625 ≤ 1.05` and `t|η₊| ≤ 1.106 + 0.0803 · 0.7358 ≤ 1.17`.

## (14.51) (`NonPrime.lean`)

calr3's `repSum_sub_le_of_bounds` with `A₊ = 1.079955` and `A_* = 1.414`, and
`ψ(N) − θ(N) + log 2 ≤ 1.4263 √N`, `ψ(N) ≤ 1.03883 N`: `3 · 1.079955² · 1.414 · 1.4263 · 1.03883 ≤ 7.3306`.

## (14.28) (`EBound.lean`)

[H, §13.2]'s argument, with the majorant `F(t) = min(1.079955, 1.19073 x/t)² ≥ η₊(t/x)²`:

* `n ≤ √x`: `1.079955² (log x/2) ψ(√x) ≤ 0.6058 √x log x`;
* `n` non-prime: with `∑_{n ≤ t, n non-prime} Λ(n)² ≤ B(t) = 1.4262 √t log t`, summation by parts
  (`sum_mul_le_of_partial`) and `B(n) − B(n−1) ≤ ∫_{n−1}^n B'` give `∫_1^∞ B'(t) F(t) dt`, computed in
  closed form on `[1, x]` and `[x, ∞)`.

The result, `E ≤ (2.94323 log x + 1.79748) √x` (`E_le_sharp`, with `2.94325` and `1.8`), is slightly
better than [H]'s `(2.94325 log x + 5.12426) √x`: [H]'s constant term comes from a cruder split
of the integral. Hence both forms of (14.28).

Axioms: `propext`, `Classical.choice`, `Quot.sound` (`verification/helfgott-appa/`).

## Build

```sh
lake build RSBounds.HelfgottAppA.EBound HelfgottAppAChallenge HelfgottAppASolution
```

It needs calr3's `MajorArcs/HHFourier.lean` and `Helfgott/NonPrime.lean` and their imports (no
kernel tables). `comparator-helfgott-appa.json` checks the five theorems of the table; the challenge
copies calr3's definitions of `η₊`, `η_*`, `repSum` and what they use.
