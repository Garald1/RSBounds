import RSBounds.Schoenfeld1976PsiThetaLog
import RSBounds.Schoenfeld1976Theorem7Proved
import RSBounds.Schoenfeld1976Theorem11Proved

open TernaryGoldbach.RSBounds

-- Theorem 7*, (5.6b*): finite RH only
#check @Schoenfeld1976PsiThetaLog.proved
#print axioms Schoenfeld1976PsiThetaLog.proved
-- Theorem 7*, (5.5a*), (5.5b*), (5.6a*), (5.6*): finite RH and PsiCert
#check @Schoenfeld1976Theorem7.proved_psiLog
#check @Schoenfeld1976Theorem7.proved_psiLogLower
#check @Schoenfeld1976Theorem7.proved_thetaLogUpper
#check @Schoenfeld1976Theorem7.proved_thetaLog
#print axioms Schoenfeld1976Theorem7.proved_psiLog
#print axioms Schoenfeld1976Theorem7.proved_psiLogLower
#print axioms Schoenfeld1976Theorem7.proved_thetaLogUpper
#print axioms Schoenfeld1976Theorem7.proved_thetaLog
-- Theorem 11, (7.2), (7.3), (7.4): finite RH and PsiCert
#check @Schoenfeld1976Theorem11Proved.proved_psi
#check @Schoenfeld1976Theorem11Proved.proved_theta
#check @Schoenfeld1976Theorem11Proved.proved_psiUpper
#print axioms Schoenfeld1976Theorem11Proved.proved_psi
#print axioms Schoenfeld1976Theorem11Proved.proved_theta
#print axioms Schoenfeld1976Theorem11Proved.proved_psiUpper
-- the target statements themselves
#print Goals.Schoenfeld1976.PsiCert
#print Goals.Schoenfeld1976.PsiThetaLog
#print Goals.Schoenfeld1976.ThetaLog
#print Goals.Schoenfeld1976.PsiLog
#print Goals.Schoenfeld1976.PsiLogLower
#print Goals.Schoenfeld1976.ThetaLogUpper
#print Goals.Schoenfeld1976.PsiTheorem11
#print Goals.Schoenfeld1976.ThetaTheorem11
#print Goals.Schoenfeld1976.PsiUpperTheorem11
