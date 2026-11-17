import RSBounds.HelfgottB6.Main

/- The theorem of `HelfgottB6Challenge`, from the project's proof. -/

open TernaryGoldbach.Helfgott
open scoped FourierTransform

namespace TernaryGoldbach.RSBounds.HelfgottB6Comparator

/-- [H, Lemma B.1.2, (B.6)]: `|η̂₂''|_∞ ≤ 31.521`, written as `(2πt)² |η̂₂(t)| ≤ 31.521`. -/
theorem eta2_fourier_bound_31521 (t : ℝ) :
    (2 * Real.pi * t) ^ 2 * ‖𝓕 (fun u => (eta2 u : ℂ)) t‖ ≤ 31.521 :=
  _root_.RSBounds.HelfgottB6.eta2_fourier_bound_31521 t

end TernaryGoldbach.RSBounds.HelfgottB6Comparator
