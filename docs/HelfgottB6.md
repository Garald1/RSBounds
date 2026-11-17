# [H, Lemma B.1.2, (B.6)] with the book's constant: `|η̂₂''|_∞ ≤ 31.521`

[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2. Lemma B.1.2 states
(B.6), `|η̂₂''|_∞ ≤ 31.521`, for `η₂ = 4 max(log 2 − |log 2t|, 0)` (the numbering is that of the
arXiv source compiled here: `lem:camelo` is B.1.2, `eq:elundot` is (B.6)). [H] proves it
analytically for `|t| ≥ 655` and by a computation on a grid of `[0, 655)` otherwise.

calr3/ternary-goldbach (at the pinned commit `192ca57`) has

* `TernaryGoldbach.MinorArcs.eta2DD_eq`: `(2πt)² η̂₂(t) = eta2DD t` for `t ≠ 0`, with
  `eta2DD t = 16 e(−t/2) − 16 e(−t/4) − 4 e(−t) + 4 ∫_{1/4}^{1/2} e(−ut)/u² du − 4 ∫_{1/2}^1 e(−ut)/u² du`;
* `norm_eta2DD_large`: `‖eta2DD t‖ ≤ 31.521` for `|t| ≥ 655` ([H]'s analytic part);
* `norm_eta2DD_le`: `‖eta2DD t‖ ≤ 32` for `t ≥ 0`, and hence `c₀ = 32` in
  `MinorArcs/InnerSums.lean` (`eta2_fourier_bound'`).

`RSBounds/HelfgottB6/` proves the book's constant for all `t`:

| theorem (`RSBounds.HelfgottB6`) | statement |
|---|---|
| `norm_eta2DD_le_31521` | `‖eta2DD t‖ ≤ 31.521` for `t ≥ 0` |
| `eta2_fourier_bound_31521` | `(2πt)² ‖𝓕 η₂ (t)‖ ≤ 31.521` for all `t` (the form of calr3's `eta2_fourier_bound'`, with `31.521` for `c₀`) |

Both are about calr3's own definitions (`eta2DD`, `Jq`, `e`, `Helfgott.eta2`), and depend only on
`propext`, `Classical.choice` and `Quot.sound`. They import `TernaryGoldbach.MinorArcs.Eta2DDTaylor`
(and through it `Eta2DDExpand`, `Eta2Fourier`), not `Eta2DDBound` or `InnerSums`.

Numerically (floating point, `scripts/b6_max.py`; not used by the proof) the maximum of
`‖eta2DD‖` is about `31.520652`, at `t ≈ 17.4148`. The margin is thus about `0.00035`, and
Charlie's first-order (Lipschitz) cells cannot reach it at any reasonable size; the cells below are
second order.

## Region A: `x = 2πt ∈ [0, 28]`

As in calr3's `Eta2DDTaylor.lean`, with its lemmas (`PQ`, `toC_PQ`, `norm_eta2DD_sub_P`,
`norm_eta2DD_sub_le`): `eta2DD(x/2π)` is the Taylor polynomial of degree `< 90` in `x` up to
`120 · 28⁹⁰/90! < 1.5·10⁻⁶`, and is `24`-Lipschitz in `x`. A bisection of `[0, 28]` checks
`|P(x_c)| + 12(x₁ − x₀) + 120 · 28⁹⁰/90! ≤ 31.521` on each cell, with `P(x_c)` computed exactly over
`ℚ` (`cellA`, `chkA`, `cellA_sound`). It tests about 150 cells (146 in `scripts/b6_region_a_check.py`,
which uses the exact `eta2DD` in place of the polynomial); the maximum of `‖eta2DD‖` on this range
is about `29.90`.

## Region B: `2πt ≥ 28`

**Ten integrations by parts** (`Expand.lean`). With `w = 1/(2πt)`, `E(u) = e(−ut)` and
`Jₙ = ∫_a^b E(u) u⁻ⁿ du`, one integration by parts is `Jₙ = iw([E u⁻ⁿ]_a^b + n Jₙ₊₁)`, so

`J₂ = ∑_{j<K} (iw)^{j+1} (j+1)! [E u^{−(j+2)}]_a^b + (iw)ᴷ (K+1)! J_{K+2}`,
`‖J_{K+2}‖ ≤ (a^{−(K+1)} − b^{−(K+1)})/(K+1)`.

With `z = e(−t/4)` (so `e(−t/2) = z²`, `e(−t) = z⁴`) this gives (`norm_eta2DD_sub_FK`)

`eta2DD t = Φ₁(w) z + Φ₂(w) z² + Φ₄(w) z⁴ + O*(4 · K! · (4^{K+1} − 1) wᴷ)`,

where `Φ₁ = −16 − 4 ∑_{n=1}^{K} n! 4^{n+1} (iw)ⁿ`, `Φ₂ = 16 + 4 ∑ n! 2^{n+2} (iw)ⁿ`,
`Φ₄ = −4 − 4 ∑ n! (iw)ⁿ`. We take `K = 10`; at `w = 1/28` the remainder is about `0.2`.

**The bound for `‖z‖ = 1`, `0 ≤ w ≤ 1/28`** (`Grid.lean`, `Sound.lean`). As in calr3's
`Eta2DDExpand.lean`, `z` and `w` are decoupled and `z = s · zm(m)`, `s = ±1`, `m ∈ [−1, 1]`
(`exists_zm`). A recursive bisection of `[−1, 1] × [0, 1/28]` (for each `s`) checks on each cell,
with centre `(m_c, w_c)`, `hθ = m₁ − m₀`, `h_w = (w₁ − w₀)/2`:

* `zm(m) = zm(m_c) e^{iδ}` with `|δ| ≤ hθ`, since `zm(m) = e^{2i arctan m}` (`zm_eq_cexp`) and
  `arctan` is `1`-Lipschitz (`abs_arctan_sub_le`);
* `Φₖ(w) = Φₖ(w_c) + d Φₖ'(w_c) + O*(C₂,ₖ d²)`, `d = w − w_c`, where
  `C₂,ₖ = ∑ₙ (|ℜ pₖ,ₙ| + |ℑ pₖ,ₙ|) · n(n−1)/2 · w₁^{n−2}` (`norm_polyC_taylor`);
* `e^{ikδ} = 1 + ikδ + O*((kδ)²)` and `|e^{ikδ} − 1| ≤ |kδ|` (for `4hθ ≤ 1`).

So `F = F₀ + iδF_θ + dF_w + O*(E)` (`norm_F_le`) with `F₀ = ∑ Φₖ(w_c) z_cᵏ`,
`F_θ = ∑ k Φₖ(w_c) z_cᵏ`, `F_w = ∑ Φₖ'(w_c) z_cᵏ` and
`E = ∑ₖ (‖Φₖ(w_c)‖ (k hθ)² + h_w ‖Φₖ'(w_c)‖ k hθ + C₂,ₖ h_w²)`, and
`|F₀ + iδF_θ + dF_w|² ≤ Q = |F₀|² + 2hθ|⟨F₀, iF_θ⟩| + 2h_w|⟨F₀, F_w⟩| + 2hθ²|F_θ|² + 2h_w²|F_w|²`
(`quad_le`). The kernel checks, exactly over `ℚ`, `4hθ ≤ 1`, `M = 31.521 − R₁₀(w₁) − E ≥ 0` and
`Q ≤ M²` (`cellB`, with norms bounded by `|ℜ| + |ℑ|`), and `cellB_sound` turns this into
`‖F(z, w)‖ + R₁₀(w) ≤ 31.521` on the cell. With the chunks below the bisection tests 50 cells for
`s = 1` and 1 320 for `s = −1` (`scripts/b6_region_b_check.py` replays the same test in exact
rationals; `b6_region_b_chunks.py` counts cells per chunk).

`norm_eta2DD_le_of_ge` combines the two: `‖eta2DD t‖ ≤ ‖F‖ + R₁₀(w) ≤ 31.521` for `2πt ≥ 28`.

## Kernel memory

The kernel's memory grows with the number of cells checked in one declaration. The whole of
region A in one declaration needed about 4.5 GB, and region B with `s = −1` in one declaration was
killed for lack of memory on this 7 GB machine. The grids are therefore cut
into chunks, each its own declaration (`chunkA`, `chunkB`): region A in 16 chunks of width `7/4`
(`GridA.lean`), region B in 8 chunks of width `1/4` in `m` for `s = 1` (`GridBpos.lean`) and 64 of
width `1/32` for `s = −1` (`GridBneg.lean`); each chunk is bisected as before.
`GoodA_of_chunks` and `GoodB_of_chunks` put them back together. With the chunks the largest module needed about 2.3 GB beyond the shared Mathlib files.

A clean build of the nine modules took 4 min 26 s on 2 cores (`verification/helfgott-b6/`).

## Comparator

`comparator-helfgott-b6.json` checks `eta2_fourier_bound_31521` (`HelfgottB6Challenge`,
`HelfgottB6Solution`). The challenge copies `TernaryGoldbach/Helfgott/Defs.lean` up to `eta2` in
the same order, because the elaborator names the proofs inside numerals (`eta2._proof_1`,
`hBase._proof_1`) after the first declaration of the module that needs them; a challenge that
defined `e` first would give `eta2` a different `_proof_1`. For the same reason the challenge does
not state `norm_eta2DD_le_31521` (it would need `e`, from another calr3 module, before `eta2`).
The non-Mathlib constants reachable from the challenge's statement have the same names and the same
type and value hashes in both environments (`verification/helfgott-b6/precheck-20261117.log`); this
is a local check, not a Comparator run.

## Files

* `RSBounds/HelfgottB6/Grid.lean`: the rational checks (`cellB`, `chkB`, `chunkB`, `cellA`,
  `chkA`, `chunkA`).
* `RSBounds/HelfgottB6/Expand.lean`: the ten integrations by parts.
* `RSBounds/HelfgottB6/Sound.lean`: soundness of the checks.
* `RSBounds/HelfgottB6/GridA.lean`, `GridBpos.lean`, `GridBneg.lean`: the kernel-checked chunks.
* `RSBounds/HelfgottB6/Main.lean`: the two theorems.
* `scripts/b6_region_a_check.py`, `b6_region_b_check.py`, `b6_region_b_chunks.py`, `b6_max.py`:
  the floating-point and rational replays used to choose `K = 10`, `W = 1/28`, `N = 90`.
