import Mathlib

/- Independent statements of Schoenfeld (1976), Theorem 7* and Theorem 11.
Only the challenge contains deliberate theorem holes; the solution is checked against the
standard-three-axiom whitelist. The definitions are compared with the solution's. -/

namespace TernaryGoldbach.RSBounds.Goals

def FiniteRH (A : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    |ρ.im| ≤ A → ρ.re = 1 / 2

end TernaryGoldbach.RSBounds.Goals

namespace TernaryGoldbach.RSBounds.Goals.Schoenfeld1976

noncomputable def X (x : ℝ) : ℝ := Real.sqrt (Real.log x / 9.645908801)

noncomputable def epsilon0 (x : ℝ) : ℝ :=
  Real.sqrt (8 / (17 * Real.pi)) * Real.sqrt (X x) * Real.exp (-X x)

end TernaryGoldbach.RSBounds.Goals.Schoenfeld1976

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Comparator

/-- Theorem 7*, (5.6b*). -/
theorem psiThetaLog (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : Real.exp 22 ≤ x) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by sorry

/-- Theorem 7*, (5.5a*). -/
theorem psiLog (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 161971 ≤ x) :
    |Chebyshev.psi x - x| < 0.0220646 * x / Real.log x := by sorry

/-- Theorem 7*, (5.5b*). -/
theorem psiLogLower (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 89909 ≤ x) :
    -(0.0220646 * x / Real.log x) < Chebyshev.psi x - x := by sorry

/-- Theorem 7*, (5.6a*). -/
theorem thetaLogUpper (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 1 < x) :
    Chebyshev.theta x - x < 0.0201384 * x / Real.log x := by sorry

/-- Theorem 7*, (5.6*). -/
theorem thetaLog (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 758711 ≤ x) :
    |Chebyshev.theta x - x| < 0.0239922 * x / Real.log x := by sorry

/-- Theorem 11, (7.2). -/
theorem psiTheorem11 (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 17 ≤ x) :
    |Chebyshev.psi x - x| < x * Goals.Schoenfeld1976.epsilon0 x := by sorry

/-- Theorem 11, (7.3). -/
theorem thetaTheorem11 (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 101 ≤ x) :
    |Chebyshev.theta x - x| < x * Goals.Schoenfeld1976.epsilon0 x := by sorry

/-- Theorem 11, (7.4), in the form established on printed page 349. -/
theorem psiUpperTheorem11 (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 1 ≤ x) :
    Chebyshev.theta x - x ≤ Chebyshev.psi x - x ∧
      Chebyshev.psi x - x < x * Goals.Schoenfeld1976.epsilon0 x := by sorry

end TernaryGoldbach.RSBounds.Schoenfeld1976Comparator
