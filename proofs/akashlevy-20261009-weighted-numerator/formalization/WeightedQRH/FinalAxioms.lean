import WeightedQRH.Statements

/-! Statement and axiom audit of the unconditional endpoints. -/
open OAI.SevenEighths OAI.SevenEighths.WeightedHighFinalAssembly

#check @WeightedQRH.Numerator.actual_raw_fullW_input
#check @WeightedQRH.fullW_analytic_input
#check @WeightedQRH.beta_le_theta
#check @WeightedQRH.hecke_nonzero
#check @WeightedQRH.dirichlet_nonzero
#check @WeightedQRH.zeta_nonzero
#check @OAI.riemannZeta_ne_zero_of_10499_12000_lt_re
#check @OAI.DirichletCharacter.LFunction_ne_zero_of_10499_12000_lt_re
#check @OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_10499_12000_lt_re

#print axioms WeightedQRH.Numerator.source_integrated_amplitude_classes
#print axioms WeightedQRH.Numerator.actual_raw_fullW_input
#print axioms WeightedQRH.fullW_analytic_input
#print axioms WeightedQRH.beta_le_theta
#print axioms WeightedQRH.hecke_nonzero
#print axioms WeightedQRH.dirichlet_nonzero
#print axioms WeightedQRH.zeta_nonzero
#print axioms OAI.riemannZeta_ne_zero_of_10499_12000_lt_re
#print axioms OAI.DirichletCharacter.LFunction_ne_zero_of_10499_12000_lt_re
#print axioms OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_10499_12000_lt_re
