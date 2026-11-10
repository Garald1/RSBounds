import RSBounds.Schoenfeld1976Final
import RSBounds.HelfgottPsiBoundsFinal

open TernaryGoldbach.RSBounds

-- PsiCert, by the kernel-checked campaign
#print axioms PsiFinite.psi_abs_sub_le_four_fifths_sqrt
#print axioms PsiFinite.psi_abs_sub_le_sqrt
-- Theorem 7* and Theorem 11, with PsiCert discharged
#check @Schoenfeld1976Final.psiCert
#check @Schoenfeld1976Final.psiLog
#check @Schoenfeld1976Final.thetaTheorem11
#print axioms Schoenfeld1976Final.psiCert
#print axioms Schoenfeld1976Final.psiLog
#print axioms Schoenfeld1976Final.psiLogLower
#print axioms Schoenfeld1976Final.thetaLogUpper
#print axioms Schoenfeld1976Final.thetaLog
#print axioms Schoenfeld1976Final.psiThetaLog
#print axioms Schoenfeld1976Final.psiTheorem11
#print axioms Schoenfeld1976Final.thetaTheorem11
#print axioms Schoenfeld1976Final.psiUpperTheorem11
-- [H, (2.14)], [H, (2.17)]
#check @HelfgottPsiBoundsFinal.sum_vonMangoldt_le_a14
#check @HelfgottPsiBoundsFinal.sum_vonMangoldt_mul_lt_a17
#print axioms HelfgottPsiBoundsFinal.sum_vonMangoldt_le_a14
#print axioms HelfgottPsiBoundsFinal.sum_vonMangoldt_mul_lt_a17
-- the statements
#print Goals.FiniteRH
#print Goals.Schoenfeld1976.PsiCert
#print Goals.Schoenfeld1976.PsiLog
#print Goals.Schoenfeld1976.ThetaTheorem11
