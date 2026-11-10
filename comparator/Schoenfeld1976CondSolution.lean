import RSBounds.Schoenfeld1976Theorem7Proved
import RSBounds.Schoenfeld1976Theorem11Proved

/- The theorems of `Schoenfeld1976CondChallenge`, from the project's proofs. -/

namespace TernaryGoldbach.RSBounds.Schoenfeld1976ComparatorCond

/-- Theorem 7*, (5.6b*). -/
theorem psiThetaLog (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : Real.exp 22 ≤ x) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x :=
  Schoenfeld1976PsiThetaLog.proved hRH x hx

/-- Theorem 7*, (5.5a*). -/
theorem psiLog
    (hcert : ∀ y : ℝ, 1500 ≤ y → y ≤ 10 ^ 10 → |Chebyshev.psi y - y| ≤ 4 / 5 * Real.sqrt y)
    (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 161971 ≤ x) :
    |Chebyshev.psi x - x| < 0.0220646 * x / Real.log x :=
  Schoenfeld1976Theorem7.proved_psiLog hcert hRH x hx

/-- Theorem 7*, (5.5b*). -/
theorem psiLogLower
    (hcert : ∀ y : ℝ, 1500 ≤ y → y ≤ 10 ^ 10 → |Chebyshev.psi y - y| ≤ 4 / 5 * Real.sqrt y)
    (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 89909 ≤ x) :
    -(0.0220646 * x / Real.log x) < Chebyshev.psi x - x :=
  Schoenfeld1976Theorem7.proved_psiLogLower hcert hRH x hx

/-- Theorem 7*, (5.6a*). -/
theorem thetaLogUpper
    (hcert : ∀ y : ℝ, 1500 ≤ y → y ≤ 10 ^ 10 → |Chebyshev.psi y - y| ≤ 4 / 5 * Real.sqrt y)
    (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 1 < x) :
    Chebyshev.theta x - x < 0.0201384 * x / Real.log x :=
  Schoenfeld1976Theorem7.proved_thetaLogUpper hcert hRH x hx

/-- Theorem 7*, (5.6*). -/
theorem thetaLog
    (hcert : ∀ y : ℝ, 1500 ≤ y → y ≤ 10 ^ 10 → |Chebyshev.psi y - y| ≤ 4 / 5 * Real.sqrt y)
    (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 758711 ≤ x) :
    |Chebyshev.theta x - x| < 0.0239922 * x / Real.log x :=
  Schoenfeld1976Theorem7.proved_thetaLog hcert hRH x hx

/-- Theorem 11, (7.2). -/
theorem psiTheorem11
    (hcert : ∀ y : ℝ, 1500 ≤ y → y ≤ 10 ^ 10 → |Chebyshev.psi y - y| ≤ 4 / 5 * Real.sqrt y)
    (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 17 ≤ x) :
    |Chebyshev.psi x - x| < x * Goals.Schoenfeld1976.epsilon0 x :=
  Schoenfeld1976Theorem11Proved.proved_psi hcert hRH x hx

/-- Theorem 11, (7.3). -/
theorem thetaTheorem11
    (hcert : ∀ y : ℝ, 1500 ≤ y → y ≤ 10 ^ 10 → |Chebyshev.psi y - y| ≤ 4 / 5 * Real.sqrt y)
    (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 101 ≤ x) :
    |Chebyshev.theta x - x| < x * Goals.Schoenfeld1976.epsilon0 x :=
  Schoenfeld1976Theorem11Proved.proved_theta hcert hRH x hx

/-- Theorem 11, (7.4), in the form established on printed page 349. -/
theorem psiUpperTheorem11
    (hcert : ∀ y : ℝ, 1500 ≤ y → y ≤ 10 ^ 10 → |Chebyshev.psi y - y| ≤ 4 / 5 * Real.sqrt y)
    (hRH : Goals.FiniteRH 1894438.5122)
    (x : ℝ) (hx : 1 ≤ x) :
    Chebyshev.theta x - x ≤ Chebyshev.psi x - x ∧
      Chebyshev.psi x - x < x * Goals.Schoenfeld1976.epsilon0 x :=
  Schoenfeld1976Theorem11Proved.proved_psiUpper hcert hRH x hx

end TernaryGoldbach.RSBounds.Schoenfeld1976ComparatorCond
