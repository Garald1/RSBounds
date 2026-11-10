import RSBounds.PsiTable1976

/-! Axiom audit for stage 1 of the 1976 plan (`docs/PsiTable1976Plan.md`). -/

open TernaryGoldbach.RSBounds

#check @PsiTable1976.of_certified
#print axioms PsiTable1976.of_certified
#print axioms PsiTable1976.psi_error_lt
#print axioms PsiTable1976.of_zeros0to1000
#print axioms PsiTable1976.psi_error_of_zeros0to1000
#print axioms QuarticHead1000ZeroSumBound.norm_sum_le_budget
#print axioms QuarticHead1000Budget.positive_low_sum_le
#print axioms QuarticHead1000Budget.relativeBudget1000_lt
#print axioms QuarticHead1000BudgetNumerics.scalarBudget1000_lt
#print axioms Head1000.table
#print axioms Head1000.positiveZeroCount_thousand
#print axioms Head1000.weighted_head_le
#print axioms Head1000.sum_up_le
#print axioms Head1000.ord_range
#print axioms Head1000.ord_gap
#print axioms Head1000.length_ordinates
