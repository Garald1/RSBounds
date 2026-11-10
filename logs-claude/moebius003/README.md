# Formalization of `mobius003.tex`

`theorem TernaryGoldbach.RSBounds.Moebius003.target : Target` is in `RSBounds/Moebius003/Main.lean`.

* Pins: Lean `leanprover/lean4:v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
* The six statement files in `RSBounds/` are byte-identical to the handover (sha256 checked).
* `#print axioms TernaryGoldbach.RSBounds.Moebius003.target` gives
  `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no
  `native_decide` and no new axiom.
* `build.log`: a clean `lake build` of the RSBounds library (Mathlib from the cache) on 2 cores, with
  0 errors and a wall time of 269 s. The slowest modules are `SquarefreeData` ((q), 88 s),
  `Range2` (47 s) and `Cells` (the 208 cells, 46 s). `Cells` peaks at about 5.6 GB of memory, a
  figure measured in an earlier run.
* `statement-sha256.txt` holds the hashes of the six statement files. `axioms.txt` was produced by
  `lake env lean Axioms.lean`.
* No gap was found in the note. The inputs are used as `Target` states them; of (S) only the
  `ψ` half is used (for `x ≥ e²²`, under `FiniteRH 1894438.5122`).

## With (L) plugged in

`RSBounds/LambdaCert/` and `RSBounds/LambdaInputsProof.lean` are copied verbatim from the (L)
package (`weightSumBound`, `ghBounds`). That package's copy of `LambdaInputs.lean` differs from the
handover's only in a docstring ("Lemma 4(a)" for "Lemma 6(a)"); the handover's copy is kept.
`RSBounds/Moebius003/TargetL.lean` proves

```lean
theorem target_L : Schoenfeld1976.PsiThetaLog → Schoenfeld1976.PsiCert →
    MoebiusInputs.MertensSqrt → MoebiusInputs.SmallMoebiusSum →
    FiniteRH 1894438.5122 → RamareMoebius
```

with axioms `[propext, Classical.choice, Quot.sound]` (`axiomsL.txt`, from `lake env lean AxiomsL.lean`).
`buildL.log` is the incremental build that added these modules.

## Files

| file | contents |
|---|---|
| `Defs` | `M`, `N`, `m`, `ρ`, `Q`, `Q₁`, `κ`, `S(x) = ∑_{t<x} |M(t)| log(1+1/t)`, `Iint` |
| `Abel` | summation by parts on finite ranges |
| `Schoenfeld` | Lemma 1 |
| `MofN` | Lemma 2 |
| `ElMarraki` | Lemma 3 |
| `Inputs` | the hypotheses of `Target`, bundled |
| `LogCert` | certified rational bounds for `log` and `√` (kernel-evaluable) |
| `Kappa` | `∑ μ(d)/d² = κ` and `0.6079267 ≤ κ ≤ 0.6079274` |
| `Rho` | Lemma 4 |
| `Squarefree`, `SquarefreeData` | Lemma 5 (a), (b), (d); Lemma 5 (c) together with the computation (q) |
| `Weights` | Lemma 6 |
| `SmallM`, `Misc`, `Range2` | `M(t)` for `t ≤ 32`; Lemma 7 (a), (b), (d), (e); Lemma 7 (c) |
| `Step` | Proposition 8 (steps 2–3) and Corollary 9, for one cell with real parameters |
| `KSum`, `JSum` | Proposition 8, step 1 (the `k`-sum, the term `ρ(y)M(D/y)`, the `j`-sum) |
| `CellsDefs`, `Checker`, `CellData`, `Cells` | the cell checker with its soundness proof, the data of the 208 cells, and the kernel check |
| `TailAux`, `Tail` | Proposition 10 and Corollary 11 |
| `Main` | the theorem |

`gen/` holds the generators and their data:
* `endpoints.py` writes `endpoints.json` (the cell endpoints, `D_mid`).
* `cells.py` writes `RSBounds/Moebius003/CellData.lean` and `cells.csv`. It mirrors the Lean
  checker in floating point, chooses `y`, and rounds `ν`, `η` up. I wrote it from scratch rather
  than modifying `k1.py`.
* `qblocks.py` gives the 53 blocks of (q), and `range2.py` the three intervals of Lemma 7(c).
* `tail.py` evaluates the inequalities of Proposition 10 and Corollary 11 at `L = 160`.
* `explore/` holds exploratory scripts used to choose parameters. Nothing depends on them.

To regenerate the cells, run `cd gen && python3 endpoints.py && python3 cells.py`. `endpoints.py` needs `mpmath`.

## Departures from the note

### Throughout
1. **Everything is at integers.** `M`, `N`, `m`, `ρ`, `Q`, `Q₁` are step functions, so every statement
   is proved at natural numbers. The real `x` of the theorem is reduced to `n = ⌊x⌋` through
   `log x ≤ log(n+1)`. So the statement proved on each range is `|m(n)| log(n+1) ≤ 0.03`, the form in
   which (m) is supplied.
2. **No integrals.** The integrals of the note are replaced by finite sums that equal them:
   `∫₁ˣ |M(t)| dt/t = ∑_{1≤t<x} |M(t)| log(1+1/t)` and
   `∫_X^x |N(u)| du/(u log²u) = ∑_{X≤n<x} |N(n)| (1/log n − 1/log(n+1))`.
   Abel summation is done on finite sums; `Mathlib.NumberTheory.AbelSummation` is not used.
   Where the note compares a sum with an integral (Lemma 6(b), Lemma 7(d), (e), the tail), the
   formalization uses telescoping sums with explicit steps instead.
3. **My own `LogCert`.** `RSBounds/Moebius003/LogCert.lean` implements `log` via the series for `atanh`,
   after reduction by `2^e` with outward rounding to `2⁻⁴⁰`. It implements `√` by Newton's method,
   then checks the result. RSBounds' `BacklundLowScalar.LogCert` is not used.
4. **κ.** `∑ μ(d)/d² = 6/π²` comes from Mathlib's L-series and `ζ(2) = π²/6`. The bounds
   `κ ∈ [0.6079267, 0.6079274]` come from Mathlib's bounds for `π`.

### §2–§3 (Lemmas 1–7)
5. **Lemma 1** is proved for natural `1 ≤ y ≤ x`, with floor division.
6. **Lemma 2** is in the discrete form of item 2, for any `2 ≤ X ≤ x`. The second identity is used as
   `|C₀| ≤ S(X₀)/log X₀`.
7. **Lemma 3** has the same statement, with `S(x)` in place of the integral. The proof uses finite sums
   only: `log x = ∑_{jk≤x} μ(k) log(x/(jk))`, then Abel summation in `k`, then an elementary bound for
   the weights.
8. **Lemma 4.** At a natural number `n`, `ρ(n) = ψ(n) − n`, so the `+1` is dropped there. In
   particular, `|ρ(y)| ≤ 0.8√y` for integer `y`. The `+1` remains only where Lemma 4 is applied at the
   real point `D/j` in the `j`-sums (cells and tail).
9. **Lemma 5.**
   * (a) is unchanged: `|Q(x) − κx| ≤ 2√x + 1`.
   * (b) becomes `∑_{j≤J} μ²(j)/√j ≤ κ(2√J − 1) + 4 + log J`, a discrete variant.
   * (c) is stated at integers: `0.96 ≤ Q₁(i) − κ log i ≤ 1.17` for all `i ≥ 1`. The note's
     `[0.578, 1.166]` is for real `t` (its infimum is approached as `t → 2⁻`). For `i ≤ 10⁴` this
     is the kernel computation (q), on 53 blocks `(a, b]`, with `μ²` by trial division and `Q₁`
     rounded outward to `10⁻¹⁵`. Beyond `10⁴` it follows from (a), with
     `|E(i) − E(10⁴)| ≤ 0.0804` and `E(10⁴) ∈ [1.0441, 1.0443]`.
   * (d) is proved by discrete Abel summation. The bound is
     `κ(log(L/(L−ℓ)) + 2/(L−ℓ)²) + (e_hi − e_lo)/(L−ℓ) + e_lo/L` with `e_lo = 0.96`, `e_hi = 1.17`.
     So the note's `0.588`, `0.578` become `0.21`, `0.96`, and there is an extra `2κ/(L−ℓ)²`.
10. **Lemma 6(a).** For `n ≤ 2²⁰` the bound is the input `WeightSumBound`. For `n > 2²⁰` the
    prime-power count is replaced by the pointwise bound `|λ − 1| ≤ 1 + λ(1 − 2/log n)` for
    `0 ≤ λ ≤ log n`. This gives `A(n) ≤ (n − 1) + (1 − 2/log n) ψ(n)`, and then (P) applies up to
    `10¹⁰` and (S) beyond.
    **Lemma 6(b)** is stated with sums: `∑_{2≤k≤K} a_k g(k) ≤ 2 ∑_{2≤k≤K} g(k)` for `g ≥ 0`
    non-increasing.
11. **Lemma 7.**
    * (a) uses `S(33) ≤ 5.33`, from `log(1+1/t) ≤ 1/t`, instead of computing `I₃₃ = 4.78186`.
      Hence `I₀ = 36113` instead of `36112`. `C₀ ≤ 1743` is unchanged.
    * (c): instead of the monotonicity argument, `(6·10⁵, 10⁹)` is cut into `[600001, 679297]`,
      `[679297, 1605044]` and `[1605044, 10⁹]`. On each `[a, b]`,
      `log(b+1)(3c_M/√a + (log b)/a) ≤ 0.03` is checked by `decide +kernel`. The values are
      `0.0299980`, `0.0299980` and `0.0282878`.
    * (d): `λ₀ = 1.107` (the note has `1.10682`).
    * (e) needs `log a ≥ 5` instead of `log a ≥ 4`, because of the discrete step.

### §4 (the cells)
12. **Endpoints are integers.** `D₁ = 10⁹`. For `2 ≤ i ≤ 208`, `D_i` is `e^{L_i}` rounded to 6
    significant digits, with the note's `L_i`. The last endpoint, `D₂₀₉ = D_end = 306985·10⁶⁴`, is
    `e¹⁶⁰` rounded up; `log D_end = 160.00000012`. Neighbours have ratio below 2. Only `log D_i` is
    certified, by `LogCert`.
13. **`D_mid = 942467·10⁵³ = D₁₇₃`** (`log D_mid ≈ 135.793`) replaces `e¹³⁶`. The checker requires
    `ν_i ≤ 0.014` for every cell with `D₊ > D_mid`.
14. **Choice of `y`.** For each cell, `y` is chosen to minimise `ν_i` among *all* checkpoints of
    `ghTable` in `[1500, min(D₋/33, 2²⁰)]`. That includes the powers of two; the handover suggested
    only the `⌊10^{s/8}⌋`. `G` and `H` are available at every checkpoint, so this is still an
    internal choice. `y = 2²⁰` is used in 149 cells. The blocks are the note's:
    `(2^{s−1}, 2^s]` for `2^s < y`, then a last block ending at `y`.
15. **Integer form of `U_s`.** On the block `(α, β]`, `u = ⌊D/k⌋` lies in
    `[⌊D₋/β⌋, ⌊(D₊ − 1)/max(α+1, 2)⌋]`. (M) is used if the left end is `≤ X₀`, and the `η`-profile
    is used on the cells that meet `[max(lo, X₀+1), hi]`. Differences of `G`, `H` are bounded by
    `hi(β) − lo(α)`. The term `ρ(y)M(D/y)` uses `|ρ(y)| ≤ 0.8√y` (item 8).
16. **The `j`-sum bound** `𝒥` becomes
    `[D₊ > V]·C₅·J_sq + 1.6κ/√y + 0.8(4 − κ + log(D₊/y))/√D₋ + κ/y + 2/√(D₋y) + 1/D₋`, with
    `J_sq = κ(log(L₊/log V) + 2/log²V) + 0.21/log V + 0.96/L₋`. These are the discrete Lemma 5(a),
    (b), (d), with the term `+1` from Lemma 4 at the real points `D/j > V`.
17. **Step 2** (the first failure) becomes strong induction over the integers of the cell.
18. **Rounding.** `ν_i` and `η_i` are stored as multiples of `10⁻¹²`, rounded up by a relative
    `10⁻⁷`. The checker recomputes `I_i` and `T_i` in `ℚ` and rounds them up. `log D_±`, `√D₋` and
    `√y` enter through certified bounds.
19. **Outcome** (from `cells.csv`; the kernel checks the inequalities exactly):
    * `max ν_i = 0.016628` (cell 1), against `ν̄ = 0.017`;
    * `ν_i ≤ 0.011882` on cells with `D₊ > D_mid`, against `ν∞ = 0.014`;
    * `max m_i = 0.027868` (cell 24), against `0.03`.

    The note has `0.01681`, `0.01201` and `0.02812`.

### §5 (beyond `D_end`)
20. **`Y = ⌊D^{3/20}⌋`** is an integer, instead of `y = D^θ`. Then `l = log Y ∈ [θL − 10⁻⁹, θL]`.
    `θ = 0.15`, `ν∞ = 0.014` and `ν̄ = 0.017` are unchanged.
21. **The three bounds.**
    * The `k`-sum uses telescoping sums: `∑ 1/(k log(D/k)) ≤ log log D − log log(D/Y)` and
      `∑ 1/(k log²(D/k)) ≤ 1/log(D/Y) − 1/log D`.
    * The boundary term uses `|ρ(Y)| ≤ C₅Y/log Y`. `Y` is an integer `≥ e²²`, so there is no `e^{−l}`.
    * The `j`-sum uses the discrete Lemma 5(d), which adds `2κ/l²` and has constants `0.21`, `0.96`.
      The terms `κe^{−l} + 2.0001e^{−(L+l)/2}` become `(κD/Y + 2√(D/Y) + 1)/D`.
    * The cell hypothesis `ν ≤ ν∞` is needed on `[D_mid, D)`. This holds since `D/Y ≥ D^{0.85} ≥ e¹³⁶ ≥ D_mid`.
22. **No monotonicity of `Φ`.** Each term is bounded by its value at `L = 160` through elementary
    inequalities. The resulting numerical inequality is checked by `norm_num`, with
    `log(20/17) ≤ 0.162519` and `log(1/(θ − 10⁻⁹/160)) ≤ 1.89712` from `LogCert`. The terms
    `(2 + C₀)/D`, `2C₀Y/D`, `C₅C₀Y/(lD)`, `κ/Y` and `2√(D/Y)/D` are collected into one
    `ε ≤ 10⁻⁸`. What is proved is `|N(D)|(1 − 1/L) ≤ D·(bracket + ε)` with
    `bracket + ε ≤ ν∞(1 − 1/L)`. At `L = 160` the bracket is `0.0136767` in floating point, against
    `ν∞(1 − 1/160) = 0.0139125`. (The note's comparison is `Φ(160) = 0.013851` against `0.014`.)
    The least counterexample becomes strong induction on `D ≥ D_end`.
23. **Corollary 11** is proved as `|m(n)| log(n+1) ≤ 0.03` for `n ≥ D_end`, through
    `0.014(1 + L/(L−2)) + 0.017λ₀(1+λ₀)/L + (terms below 10⁻⁸)`, which is about `0.028425` at
    `L = 160`. The small terms use `∑_{X₀≤t<D_mid} 1/log t ≤ D_mid/20.72` (instead of `e¹³⁶/134`),
    `∑_{X₀≤t<n} 1/t ≤ 2 log n` and `log²n/n ≤ 16/√n`.

### §6 (the theorem)
24. The ranges are `[11815, 6·10⁵]` by (m), `(6·10⁵, 10⁹)` by Lemma 7(c), `[10⁹, D_end)` by the
    cells and `[D_end, ∞)` by Corollary 11. `D_end` is slightly above `e¹⁶⁰`.
