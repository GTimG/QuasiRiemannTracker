import TightIndependentTargets
import QRH

example : QRH.TightIndependent.allDirichlet :=
  @QRH.DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re
example : QRH.TightIndependent.zeta :=
  @QRH.riemannZeta_ne_zero_of_tightTheta_lt_re
example : QRH.TightIndependent.allHecke :=
  @QRH.Hecke.LFunction_ne_zero_of_tightTheta_lt_re
example : QRH.theta = (874957019421 / 1000000000000 : ℝ) := rfl
example : QRH.tightTheta = (874957019420871 / 1000000000000000 : ℝ) := rfl
example : (874957019420871 / 1000000000000000 : ℝ) < (874957019421 / 1000000000000 : ℝ) :=
  QRH.tightTheta_lt_theta

#print axioms QRH.DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re
#print axioms QRH.riemannZeta_ne_zero_of_tightTheta_lt_re
#print axioms QRH.Hecke.LFunction_ne_zero_of_tightTheta_lt_re
#print axioms QRH.riemannZeta_zero_re_le_tightTheta
#print axioms QRH.tightTheta_lt_theta
