import RSBounds.PolynomialPsi

/-!
# Twice-integrated polynomial smoothing of psi

This is the finite arithmetic smoothing with m=2. It reuses the existing
finite indicator representation of psi and proves the exact second-difference
identities, including prime-power endpoints. No zero assumption is used.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.QuadraticPsi

/-- The CDF of the sum of two unit intervals. -/
noncomputable def W (t : ℝ) : ℝ :=
  ((max t 0) ^ 2 - 2 * (max (t - 1) 0) ^ 2 + (max (t - 2) 0) ^ 2) / 2

theorem W_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : W t = 0 := by
  simp [W, max_eq_right ht, max_eq_right (show t - 1 ≤ 0 by linarith),
    max_eq_right (show t - 2 ≤ 0 by linarith)]

theorem W_eq_one_of_two_le {t : ℝ} (ht : 2 ≤ t) : W t = 1 := by
  rw [W, max_eq_left (by linarith : 0 ≤ t),
    max_eq_left (by linarith : 0 ≤ t - 1), max_eq_left (by linarith : 0 ≤ t - 2)]
  ring

theorem W_bounds (t : ℝ) : 0 ≤ W t ∧ W t ≤ 1 := by
  by_cases h0 : t ≤ 0
  · rw [W_eq_zero_of_nonpos h0]
    norm_num
  have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge h0)
  by_cases h1 : t ≤ 1
  · rw [W, max_eq_left ht0, max_eq_right (by linarith : t - 1 ≤ 0),
      max_eq_right (by linarith : t - 2 ≤ 0)]
    constructor <;> nlinarith [sq_nonneg t,
      mul_nonneg ht0 (show 0 ≤ 1 - t by linarith)]
  have ht1 : 1 ≤ t := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : t ≤ 2
  · rw [W, max_eq_left ht0, max_eq_left (by linarith : 0 ≤ t - 1),
      max_eq_right (by linarith : t - 2 ≤ 0)]
    constructor <;> nlinarith [sq_nonneg (t - 2),
      mul_nonneg (show 0 ≤ t - 1 by linarith) (show 0 ≤ 2 - t by linarith)]
  · rw [W_eq_one_of_two_le (le_of_lt (lt_of_not_ge h2))]
    norm_num

theorem W_nonneg (t : ℝ) : 0 ≤ W t := (W_bounds t).1

theorem W_le_one (t : ℝ) : W t ≤ 1 := (W_bounds t).2

/-- The second truncated-power primitive of a point mass. -/
noncomputable def quadraticPrimitive (t : ℝ) : ℝ := (max t 0) ^ 2 / 2

/-- A common finite truncation of the second primitive of psi. -/
noncomputable def psi2Trunc (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * quadraticPrimitive (t - n)

/-- The canonical finite truncated-power primitive. -/
noncomputable def Psi2 (t : ℝ) : ℝ := psi2Trunc ⌊t⌋₊ t

/-- Forward second difference, before normalization by the step size. -/
def secondDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  f (x + 2 * h) - 2 * f (x + h) + f x

/-- Polynomial upper smoothing of psi. -/
noncomputable def psiUpper (N : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * W ((x + 2 * h - n) / h)

/-- Polynomial lower smoothing of psi. -/
noncomputable def psiLower (N : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * W ((x - n) / h)

/-- The lower smoothing never exceeds psi. -/
theorem psiLower_le_psi {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) : psiLower N x h ≤ Chebyshev.psi x := by
  rw [PolynomialPsi.psi_eq_indicator_sum hx hN]
  unfold psiLower
  apply sum_le_sum
  intro n _
  by_cases hn : (n : ℝ) ≤ x
  · rw [if_pos hn]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (W_le_one ((x - n) / h))
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · rw [if_neg hn, W_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (by linarith [lt_of_not_ge hn]) hh.le), mul_zero]

/-- The upper smoothing majorizes psi, including at prime-power jumps. -/
theorem psi_le_psiUpper {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) : Chebyshev.psi x ≤ psiUpper N x h := by
  rw [PolynomialPsi.psi_eq_indicator_sum hx hN]
  unfold psiUpper
  apply sum_le_sum
  intro n _
  by_cases hn : (n : ℝ) ≤ x
  · have hw : 2 ≤ (x + 2 * h - n) / h := (le_div_iff₀ hh).2 (by linarith)
    rw [if_pos hn, W_eq_one_of_two_le hw, mul_one]
  · rw [if_neg hn]
    exact mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (W_nonneg _)

/-- The two polynomial smoothings sandwich psi on one common truncation. -/
theorem psi_sandwich {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    psiLower N x h ≤ Chebyshev.psi x ∧ Chebyshev.psi x ≤ psiUpper N x h :=
  ⟨psiLower_le_psi hx hh (by linarith), psi_le_psiUpper hx hh (by linarith)⟩

/-- Terms beyond the common truncation have zero upper weight. -/
theorem upper_weight_eq_zero {x h : ℝ} (hh : 0 < h) {N n : ℕ}
    (hN : x + 2 * h ≤ N) (hn : N < n) : W ((x + 2 * h - n) / h) = 0 := by
  apply W_eq_zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ hh.le
  have hn' : (N : ℝ) < n := by exact_mod_cast hn
  linarith

/-- A sufficiently large finite truncation equals the canonical primitive. -/
theorem psi2Trunc_eq_Psi2 {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : t ≤ N) :
    psi2Trunc N t = Psi2 t := by
  have hfloor : ⌊t⌋₊ ≤ N := by exact_mod_cast (Nat.floor_le ht).trans hN
  unfold Psi2 psi2Trunc
  symm
  apply sum_subset (Icc_subset_Icc le_rfl hfloor)
  intro n hn hn'
  have hnf : ⌊t⌋₊ < n := by
    have hn0 : 0 ≤ n := Nat.zero_le n
    simp only [mem_Icc, hn0, true_and] at hn'
    omega
  have hnt : t < n := (Nat.floor_lt ht).1 hnf
  simp [quadraticPrimitive, max_eq_right (show t - n ≤ 0 by linarith)]

/-- Second differences commute with finite sums. -/
theorem secondDifference_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (x h : ℝ) :
    secondDifference (fun t => ∑ i ∈ s, f i t) x h =
      ∑ i ∈ s, secondDifference (f i) x h := by
  simp only [secondDifference, sum_add_distrib, sum_sub_distrib, mul_sum]

/-- Second differences commute with scalar multiplication. -/
theorem secondDifference_mul (c : ℝ) (f : ℝ → ℝ) (x h : ℝ) :
    secondDifference (fun t => c * f t) x h = c * secondDifference f x h := by
  unfold secondDifference
  ring

/-- The normalized second difference of one truncated power is the quadratic
CDF weight. This is a purely algebraic identity. -/
theorem secondDifference_quadraticPrimitive {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    secondDifference (fun t => quadraticPrimitive (t - a)) x h / h ^ 2 =
      W ((x + 2 * h - a) / h) := by
  have hd (t : ℝ) : max (t / h) 0 = max t 0 / h := by
    simpa only [zero_div] using max_div_div_right hh.le t 0
  have e1 : (x + 2 * h - a) / h - 1 = (x + h - a) / h := by
    field_simp [hh.ne']; ring
  have e2 : (x + 2 * h - a) / h - 2 = (x - a) / h := by
    field_simp [hh.ne']; ring
  unfold secondDifference quadraticPrimitive W
  rw [e1, e2]
  simp only [hd, div_pow]
  ring

/-- The normalized forward difference of the finite second primitive is
exactly the upper polynomial smoothing. -/
theorem secondDifference_psi2Trunc {h : ℝ} (hh : 0 < h) (N : ℕ) (x : ℝ) :
    secondDifference (psi2Trunc N) x h / h ^ 2 = psiUpper N x h := by
  unfold psi2Trunc psiUpper
  rw [secondDifference_sum, sum_div]
  apply sum_congr rfl
  intro n _
  rw [secondDifference_mul, mul_div_assoc,
    secondDifference_quadraticPrimitive hh]

/-- The canonical second primitive has the same difference identity whenever
the finite upper sum contains its complete support. -/
theorem secondDifference_Psi2 {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    secondDifference Psi2 x h / h ^ 2 = psiUpper N x h := by
  have h0 := psi2Trunc_eq_Psi2 hx (show x ≤ N by linarith)
  have h1 := psi2Trunc_eq_Psi2 (show 0 ≤ x + h by linarith)
    (show x + h ≤ N by linarith)
  have h2 := psi2Trunc_eq_Psi2 (show 0 ≤ x + 2 * h by linarith) hN
  have hd : secondDifference Psi2 x h = secondDifference (psi2Trunc N) x h := by
    unfold secondDifference
    rw [h0, h1, h2]
  rw [hd]
  exact secondDifference_psi2Trunc hh N x

/-- The backward-shifted forward difference is exactly the lower smoothing. -/
theorem secondDifference_Psi2_lower {x h : ℝ} (hh : 0 < h) (hx : 2 * h ≤ x)
    {N : ℕ} (hN : x ≤ N) :
    secondDifference Psi2 (x - 2 * h) h / h ^ 2 = psiLower N x h := by
  have ht := secondDifference_Psi2 (x := x - 2 * h) (by linarith) hh
    (show x - 2 * h + 2 * h ≤ N by linarith)
  simpa only [psiUpper, psiLower, sub_add_cancel] using ht

/-- Once the two polynomial smoothings have controlled errors, the cost of
unsmoothing is precisely `h`. The analytic error bound remains explicit. -/
theorem psi_error_of_polynomial_errors {x h E : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N)
    (hupper : |psiUpper N x h - (x + h)| ≤ E)
    (hlower : |psiLower N x h - (x - h)| ≤ E) :
    |Chebyshev.psi x - x| ≤ E + h := by
  obtain ⟨hlo, hup⟩ := psi_sandwich hx hh hN
  obtain ⟨hu1, hu2⟩ := abs_le.mp hupper
  obtain ⟨hl1, hl2⟩ := abs_le.mp hlower
  rw [abs_le]
  constructor <;> linarith

end TernaryGoldbach.RSBounds.QuadraticPsi
