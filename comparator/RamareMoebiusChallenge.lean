import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Independent statement of the end-to-end result: upstream's `RamareMoebius` (ternary Goldbach,
calr3/ternary-goldbach at `192ca57`), from finite RH up to height `1894438.5122`. It imports only
Mathlib (the modules the RSBounds statement files import). Only this challenge contains a theorem
hole; the solution is `RSBounds.Moebius003.Complete`. -/

namespace TernaryGoldbach.RSBounds.Goals

def FiniteRH (A : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    |ρ.im| ≤ A → ρ.re = 1 / 2

end TernaryGoldbach.RSBounds.Goals

namespace TernaryGoldbach.RSBounds.Moebius003

open Goals

def RamareMoebius : Prop :=
  ∀ x : ℝ, 11815 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n| ≤ 0.03 / Real.log x

theorem ramareMoebius_of_finiteRH (hRH : FiniteRH 1894438.5122) : RamareMoebius := by sorry

end TernaryGoldbach.RSBounds.Moebius003
