# TernaryGoldbach: what RSBounds can still supply

A read-only survey of `calr3/ternary-goldbach`, made on 2026-11-08 against `main` at `192ca57`
(2026-11-07 22:31 UTC). RSBounds itself is pinned to the older `ce82a5b`.

## 1. `RHUpTo` is gone upstream

`main` no longer has the hypotheses `RHUpTo` (RH to `3·10¹⁰`) or `ButhePsi`.

| Commit | Date (UTC) | Change |
|---|---|---|
| `cbabdb5` | 11-06 12:00 | drop `ButhePsi` |
| `3df3616` | 11-07 13:04 | RH up to `10⁸` from `PlattGRH` (at `q = 1`) |
| `f714a63` | 11-07 17:53 | small cases from a kernel-checked prime ladder to `10²⁷` |
| `ab0a271` | 11-07 20:21 | merge; drop `RHUpTo` |

The main theorem now takes three hypotheses: `PlattGRH`, `BinaryGoldbachInput`, `RamareMoebius`.
The ψ/θ bounds use `RHBelow 1e8`, obtained from `PlattGRH` at `q = 1` (`Explicit.rh_upto_1e8`).

The major arcs need `PlattGRH` at `q = 1` up to `10⁸` anyway (README, "How the proof is
organized"). So `FiniteRH 1894438.5122` cannot shorten the hypothesis list. `NOTES.md`,
"Open directions", records that Helfgott has proposed proofs from smaller inputs.

## 2. What is still weaker than [H]

Two ψ-bounds of [H, §2.5] are weakened. The constants below are as upstream's own docstrings
give them (`Prelim/LambdaMu.lean`), together with [H]'s:

| [H] | Lean | upstream | [H] | used at |
|---|---|---|---|---|
| (2.14) | `sum_vonMangoldt_le_a14` | `∑_{n≤y} Λ(n) ≤ 1.0064 y`, `y ≥ 2.5·10⁷` | `1.0004` | `V ≥ 2.7·10⁷` |
| (2.17) | `sum_vonMangoldt_mul_lt_a17` | `∑_{n≤y} Λ(n) n < 1.022 y²/2`, `y ≥ 2.5·10⁷` | `1.0008` | `V ≥ 2.7·10⁷` |

They are used only in `MinorArcs/TypeI2Large.lean` (l. 71, 323, 332) and `MinorArcs/TypeI2Sum.lean`
(l. 380, 389). Upstream's `|ψ(y) − y| ≤ 31.5√y` near `2.5·10⁷` (`psi_two_sided`) cannot do better.

## 3. How RSBounds restores [H]'s constants

Inputs, all in RSBounds:
- **PsiCert** (`PsiFinite.psi_abs_sub_le_four_fifths_sqrt`): `|ψ(x) − x| ≤ 0.8√x` for
  `1500 ≤ x ≤ 10¹⁰`. Kernel-checked, no premise.
- **RS75 b = 23** (`PsiTable1975.psi_error_b23`): `|ψ(x) − x| < 0.00020211 x` for `x ≥ e²³`, under
  `FiniteRH 1894438.5122`. Note that `e²³ ≈ 9.74·10⁹ < 10¹⁰`.
- **The premise.** `FiniteRH A` and upstream's `RHBelow A` are the same formula, so
  `FiniteRH 1894438.5122` follows from `rh_upto_1e8` by monotonicity.

Schoenfeld (1976) is not needed for these two.

- **(2.14)**:
  - On `[2.5·10⁷, 10¹⁰]`, `0.8/√y ≤ 1.6·10⁻⁴`.
  - Above `e²³`, the relative error is `< 2.03·10⁻⁴`.
  - So `ψ(y) ≤ 1.000203 y`, which beats `1.0004`.
- **(2.17)**:
  - By Abel summation, `∑_{n≤y} Λ(n) n − y²/2 = 1/2 + yE(y) − ∫₁^y E`, where `E(t) = ψ(t) − t`.
  - Bound `|E|` by `t` below 1500, by PsiCert to `10¹⁰`, and by `0.00020211 t` beyond.
  - A float check over `2.5·10⁷ ≤ y ≤ 2.5·10¹⁷` gives the excess `≤ 6.07·10⁻⁴ · y²/2`, the worst case
    being `y → ∞`, where it is `3 · 0.00020211`.
  - So the constant is `1.00061`, which beats `1.0008`.
  - This is a float computation, not yet a Lean proof.

The new statements imply the current ones, so nothing downstream breaks. Tightening the Type I₂
numerics to use them is upstream's choice. Their README says Theorem 3.1.1 currently has
`2.526 x/√t` where [H] has `2.5 x/√t`, which also involves `c₀ = 32` and `c₊ = 2`.

## 4. Integration

- **Pins match.** Upstream `main` and RSBounds both use Lean v4.35.0 and Mathlib `56a00585`.
- **Namespace.** RSBounds already lives in `TernaryGoldbach.RSBounds`.
- **Cycle.** RSBounds imports 15 upstream modules directly, 39 with their closure (14,560 lines,
  all RH-free).
  - So upstream cannot take RSBounds as a Lake package.
  - The files would have to move into upstream's tree, or upstream would copy the two theorems.
- **The upstream modules at `main`.**
  - 12 of the 15 direct imports are byte-identical at `main`.
  - `PNTMertens` and `SmallMertensProd` only gained text (a docstring and `prod_le_1e5`).
  - `ZeroFreeRegion.zero_free` now needs `|γ| ≥ 10⁸` instead of `10⁹`, a stronger theorem.
  - In the same file, `log2508_le` became `log2585_le` (`log 2.5085 ≤ 0.9197`), and RSBounds uses
    the old name (`RSBounds/Theta.lean`, l. 58). A re-pin therefore needs at least that one fix.
- **Build cost.** PsiCert is 1014 modules, about 60 s each on this 2-core machine, so roughly
  17 core-hours. Upstream's ladder is about 5 core-hours (their README).

## 5. Note for `RamareMoebius`

Upstream's notes ("Open directions") already discuss this hypothesis. Their main points:
- Of its two uses, (2.22) with constant `2.8` would follow from `|m(x)| ≤ K/(log x − 0.7521)` with
  `K ≲ 0.65`, where `m(x) = ∑_{n≤x} μ(n)/n`.
- They say that certifying `|ψ(x) − x| ≤ √x` up to `10⁹–10¹⁰` in the kernel would bring `K` to
  about `0.6`. PsiCert is such a certificate. Even so, the middle range `11815 ≤ x < 10¹⁰` needs its
  own argument.
- The other use, the `g₂` tail behind (5.31), needs `|m(x)| ≤ 0.073/log x` for all `x ≥ 11815`, so
  the hypothesis stays there.
- In their assessment, Ramaré's own proof needs `√x`-quality ψ bounds to `10¹⁹`, the bound
  `|M(x)| ≤ x/4345` of Cohen–Dress–El Marraki, and computations of `M(x)` to `10¹²–10¹⁶`.

I have not checked these claims against Ramaré's paper.

## 6. Who does what

- **This chat (Schoenfeld):**
  - this survey;
  - **done:** `RSBounds/HelfgottPsiBounds.lean` proves (2.14) and (2.17) with `1.0004` and
    `1.0008`, in upstream's exact form (`∑ n ∈ Icc 1 ⌊y⌋₊`).
    - It uses PsiCert, taken as a hypothesis, and `psi_error_b23`.
    - It touches no existing file.
    - The audit (`logs-claude/helfgott-axiom-audit.log`) shows only the standard three axioms.
    - `RSBounds/HelfgottPsiBoundsFinal.lean` discharges PsiCert. It is not compiled yet, because it
      needs the PsiFinite build.
- **The other chat:** owns `psi_error_b23` and the RS side; nothing is asked of it.
- **Upstream:** a PR to `calr3/ternary-goldbach` is the user's call.
