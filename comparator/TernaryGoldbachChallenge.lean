import Mathlib

/-!
# Challenge: upstream's main theorems without `RamareMoebius`, and `RamareMoebius` itself

The definitions are copied verbatim from upstream's `Challenge.lean` (calr3/ternary-goldbach at
`192ca57`), which itself copies them from `TernaryGoldbach/Statement.lean`. The three theorems are
upstream's two main theorems with the hypothesis `hμ : RamareMoebius` removed, and the discharge of
that hypothesis. The solutions are `RSBounds.Moebius003.UpstreamMain` (all three) and
`RSBounds.Moebius003.Upstream` (`ramareMoebius_of_plattGRH` alone).
-/

namespace TernaryGoldbach

/-- `n` is a sum of three primes. -/
def IsSumOfThreePrimes (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- `n` is a sum of two primes. -/
def IsSumOfTwoPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- The ternary Goldbach conjecture: every odd `n > 5` is a sum of three primes. -/
def Statement : Prop :=
  ∀ n : ℕ, Odd n → 5 < n → IsSumOfThreePrimes n

/-- Binary Goldbach verified up to `N`: every even `n` with `4 ≤ n ≤ N` is a sum of two primes. -/
def BinaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → n ≤ N → IsSumOfTwoPrimes n

/-- Ternary Goldbach for odd `n` with `5 < n ≤ N`. -/
def TernaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n : ℕ, Odd n → 5 < n → n ≤ N → IsSumOfThreePrimes n

/-- Ternary Goldbach for odd `n ≥ C`. -/
def TernaryGoldbachFrom (C : ℕ) : Prop :=
  ∀ n : ℕ, Odd n → C ≤ n → IsSumOfThreePrimes n

/-! ## Hypotheses

The proof rests on three published numerical results, stated here as `Prop`s and passed to the
theorems that need them as `Fact` instances. Each is a large computation, and none
is formalized. -/

/-- D. Platt [Plab, Thm 7.1], [H, §9.6]: for every primitive character `χ` of conductor `q`, GRH
holds for `L(s, χ)` up to height `10⁸/q` if `q ≤ 3·10⁵` is odd, and up to height
`max(10⁸/q, 200 + 7.5·10⁷/q)` if `q ≤ 4·10⁵` is even. -/
def PlattGRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    (Odd q → q ≤ 300000 → ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ 1e8 / q → ρ.re = 1 / 2) ∧
    (Even q → q ≤ 400000 → ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ max (1e8 / q : ℝ) (200 + 7.5e7 / q) → ρ.re = 1 / 2)

/-- [OeSHP] Oliveira e Silva, Herzog, Pardi, Math. Comp. 83 (2014): every even `4 ≤ n ≤ 4·10¹⁸` is
a sum of two primes. -/
def BinaryGoldbachInput : Prop := BinaryGoldbachUpTo (4 * 10 ^ 18)

/-- O. Ramaré, Acta Arith. 157 (2013), Cor. 1.4, as cited in [H, (2.21)]:
`|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`. -/
def RamareMoebius : Prop :=
  ∀ x : ℝ, 11815 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n| ≤ 0.03 / Real.log x

end TernaryGoldbach

namespace TernaryGoldbach.RSBounds.Moebius003

open TernaryGoldbach

theorem ramareMoebius_of_plattGRH (h : TernaryGoldbach.PlattGRH) : TernaryGoldbach.RamareMoebius := by
  sorry

theorem ternary_goldbach_of_two_hypotheses (hGRH : PlattGRH) (hBG : BinaryGoldbachInput) :
    Statement := by
  sorry

theorem ternary_goldbach_large_of_plattGRH (hGRH : PlattGRH) : TernaryGoldbachFrom (10 ^ 27) := by
  sorry

end TernaryGoldbach.RSBounds.Moebius003
