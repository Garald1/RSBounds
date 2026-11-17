import Mathlib

/- [H] (14.3), (14.24), (14.51) and (14.28) with Helfgott's constants (H. A. Helfgott, *The ternary
Goldbach problem*, arXiv:1501.05438v2). The definitions are calr3/ternary-goldbach's
(`TernaryGoldbach/Helfgott/Defs.lean`), copied here and compared with the solution's. Only the
challenge contains deliberate theorem holes; the solution is checked against the
standard-three-axiom whitelist. -/

open Complex MeasureTheory ArithmeticFunction

namespace TernaryGoldbach.Helfgott

/-- Mellin convolution `(f *_M g)(t) = ∫₀^∞ f(r) g(t/r) dr/r`. -/
noncomputable def mellinConv (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in Set.Ioi (0:ℝ), f r * g (t / r) / r

/-- `h(t) = t²(2 - t)³ e^{t - 1/2}` on `[0, 2]`, zero elsewhere [H, (7.5)]. -/
noncomputable def hBase (t : ℝ) : ℝ :=
  if t ∈ Set.Icc (0:ℝ) 2 then t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) else 0

/-- `F_H(y) = sin(H log y) / (π log y)` [H, (7.6)]. -/
noncomputable def F (H y : ℝ) : ℝ := Real.sin (H * Real.log y) / (Real.pi * Real.log y)

/-- `h_H(t) = ∫₀^∞ h(t/y) F_H(y) dy/y` [H, (7.6)]. -/
noncomputable def hH (H t : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0:ℝ), hBase (t / y) * F H y / y

/-- `η₊(t) = h₂₀₀(t) · t · e^{-t²/2}` [H, (7.4)]. -/
noncomputable def etaPlus (t : ℝ) : ℝ := hH 200 t * t * Real.exp (-t ^ 2 / 2)

/-- `η₂(t) = 4 max(log 2 - |log 2t|, 0)` for `t > 0` (and `0` for `t ≤ 0`) [H, (11.10)]. -/
noncomputable def eta2 (t : ℝ) : ℝ :=
  if 0 < t then 4 * max (Real.log 2 - |Real.log (2 * t)|) 0 else 0

/-- `φ(t) = t² e^{-t²/2}`. -/
noncomputable def phi (t : ℝ) : ℝ := t ^ 2 * Real.exp (-t ^ 2 / 2)

/-- `κ = 49`. -/
def κ : ℝ := 49

/-- `η_*(t) = (η₂ *_M φ)(κt)`. -/
noncomputable def etaStar (t : ℝ) : ℝ := mellinConv eta2 phi (κ * t)

/-- `x = N / (2 + 9/(196 √(2π)))` [H, (14.15)]. -/
noncomputable def xOf (N : ℕ) : ℝ := N / (2 + 9 / (196 * √(2 * Real.pi)))

open Classical in
/-- The weighted count of representations `N = n₁ + n₂ + n₃` with every `nᵢ` satisfying `P`:
`∑ Λ(n₁)Λ(n₂)Λ(n₃) η₊(n₁/x) η₊(n₂/x) η_*(n₃/x)` (the left side of [H, (14.50)]). -/
noncomputable def repSum (P : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ n₁ ∈ Finset.range (N + 1), ∑ n₂ ∈ Finset.range (N + 1), ∑ n₃ ∈ Finset.range (N + 1),
    if n₁ + n₂ + n₃ = N ∧ P n₁ ∧ P n₂ ∧ P n₃ then
      Λ n₁ * Λ n₂ * Λ n₃ * etaPlus (n₁ / xOf N) * etaPlus (n₂ / xOf N) *
        etaStar (n₃ / xOf N)
    else 0

end TernaryGoldbach.Helfgott

open TernaryGoldbach.Helfgott

namespace TernaryGoldbach.RSBounds.HelfgottAppAComparator

/-- [H, (14.3)]: `|η₊(t)| ≤ 1.079955` for `t ≥ 0`. -/
theorem abs_etaPlus_le_1079955 {t : ℝ} (ht : 0 ≤ t) : |etaPlus t| ≤ 1.079955 := by sorry

/-- [H, (14.24)]: `t |η₊(t)| ≤ 1.19073` for `t ≥ 0`. -/
theorem mul_abs_etaPlus_le_119073 {t : ℝ} (ht : 0 ≤ t) : t * |etaPlus t| ≤ 1.19073 := by sorry

/-- [H, (14.51)] with `7.3306`, given `|η_*| ≤ 1.414` and [RS62, Thms 12, 13]. -/
theorem nonprime_input_book (hAs : ∀ t : ℝ, 0 ≤ t → |etaStar t| ≤ 1.414)
    (hpsi : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    (N : ℕ) (hN27 : 10 ^ 27 ≤ N) :
    repSum (fun _ => True) N - repSum (fun n => n.Prime ∧ Odd n) N ≤
      7.3306 * (N * √N) * Real.log N := by sorry

/-- [H, (14.28)], first form, given [RS62, Thms 12, 13]. -/
theorem E_le_book_formula (hpsi : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤
      (2.94325 * Real.log x + 5.12426) * √x := by sorry

/-- [H, (14.28)], given [RS62, Thms 12, 13]. -/
theorem E_le_14_28_book (hpsi : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∑' n : ℕ, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤ 8.4029e-12 * x := by sorry

end TernaryGoldbach.RSBounds.HelfgottAppAComparator
