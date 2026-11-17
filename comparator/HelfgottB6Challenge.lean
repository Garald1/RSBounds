import Mathlib

/- [H, Lemma B.1.2, (B.6)] with Helfgott's constant `31.521` (H. A. Helfgott, *The ternary Goldbach
problem*, arXiv:1501.05438v2): `|η̂₂''|_∞ ≤ 31.521`, written as `(2πt)² |η̂₂(t)| ≤ 31.521`. The
definitions are calr3/ternary-goldbach's `TernaryGoldbach/Helfgott/Defs.lean` up to `eta2`, copied
here in the same order (so that the elaborator's auxiliary proofs get the same names) and compared
with the solution's. Only the challenge contains deliberate theorem holes; the solution is checked
against the standard-three-axiom whitelist. -/

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

end TernaryGoldbach.Helfgott

open TernaryGoldbach.Helfgott
open scoped FourierTransform

namespace TernaryGoldbach.RSBounds.HelfgottB6Comparator

/-- [H, Lemma B.1.2, (B.6)]: `|η̂₂''|_∞ ≤ 31.521`, written as `(2πt)² |η̂₂(t)| ≤ 31.521`. -/
theorem eta2_fourier_bound_31521 (t : ℝ) :
    (2 * Real.pi * t) ^ 2 * ‖𝓕 (fun u => (eta2 u : ℂ)) t‖ ≤ 31.521 := by sorry

end TernaryGoldbach.RSBounds.HelfgottB6Comparator
