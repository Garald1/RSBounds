import RSBounds
import RSBounds.RS62MertensFromFiniteRH
import RSBounds.RS62TotientFromFiniteRH
import RSBounds.Theta

/-! Statements and axiom audit for the public theorems whose finite-RH height
was lowered from 1894439 to 1894438.5122. Expected axioms: `propext`,
`Classical.choice`, `Quot.sound` only. -/

open TernaryGoldbach.RSBounds

-- the specification and the monotonicity lemma
#check @Goals.FiniteRH.mono
#print axioms Goals.FiniteRH.mono
#print Goals.ZeroFreeRegion1975
#print Goals.PsiTable1975

-- item 1: the RS75 zero-free region
#check @RS75ZeroFree1975.zero_free_high
#check @RS75ZeroFree1975.zero_free
#check @RS75ZeroFree1975.xi_zero_re_lt
#check @RS75FiniteHandoff.zero_free_low
#print axioms RS75ZeroFree1975.zero_free_high
#print axioms RS75ZeroFree1975.zero_free
#print axioms RS75ZeroFree1975.proved
#print axioms RS75ZeroFree1975.xi_zero_re_lt
#print axioms RS75ZeroFreeScalars.chosen_residual_lt
#print axioms RS75ZeroFreeScalars.heightRatio_upper

-- item 2: the RS75 b = 23 chain
#check @RosserSchoenfeld1975.psi_error_b23
#print axioms RosserSchoenfeld1975.psi_error_b23
#print axioms PsiTable1975.psi_error_lt
#print axioms PsiTable1975.proved
#print axioms QuarticFirst29BudgetNumerics.scalarBudget_lt
#print axioms QuarticLowZeroBounds.positive_low_sum_le

-- item 3: RS62 and the inputs it uses
#check @RS62MertensFromFiniteRH.mertens_lower_of_finiteRH
#check @RS62TotientFromFiniteRH.totient_bound_of_finiteRH
#print axioms RS62MertensFromFiniteRH.mertens_lower_of_finiteRH
#print axioms RS62TotientFromFiniteRH.totient_bound_of_finiteRH
#print axioms ModeratePsi.psi_error_le
#print axioms WeakPsiTail.psi_error_le
#print axioms WeakPsiTail.low_re_eq_half
#print axioms MertensPotentialBound.mertens_lower_of_moderate_psi
#print axioms MertensPotentialBound.mertens_lower_of_b23_psi
#print axioms MertensPotentialBound.squareAllowance_A_lt
#print axioms MertensLargeBudget.mertens_lower_of_weak_psi
#print axioms MertensPotentialDecay.abs_J_le_cutoff
#print axioms RS75AdaptiveHighBudget.norm_high_sum_upper_lt
#print axioms RS75AdaptiveHighBudget.norm_high_sum_lower_lt
#print axioms RS75DecayingHighZeros.norm_high_sum_upper_lt
#print axioms RS75ZeroPowerDecay.zero_power_weight_le
#check @RosserCubicTail.cubic_sum_A_lt
#print axioms RosserCubicTail.cubic_sum_A_lt

-- item 3: the unconditional R = 20 region (outside the RS62 closure).
-- PsiFiniteRH, PsiFiniteRHZeroFree and ThetaLarge never compiled and were
-- removed on 2026-11-08; see HEIGHT-CHANGE-NOTES.md.
#check @zero_free_rs_height
#print axioms zero_free_rs_height
#print axioms riemannZeta_zero_free_rs_height
