import QRH.SlackRefinedNonvanishing
import IndependentSlackTargets

/-! UNCOMPILED independent target and axiom gate. This file supplies no new
analytic assumption; source preparation is not proof verification. -/
namespace TrackerSlack.Gate

theorem allDirichlet : TrackerSlack.Independent.allDirichlet :=
  QRH.DirichletCharacter.LFunction_ne_zero_of_slackRefined_lt_re

theorem allHecke : TrackerSlack.Independent.allHecke :=
  QRH.Hecke.LFunction_ne_zero_of_slackRefined_lt_re

theorem zeta : TrackerSlack.Independent.zeta :=
  QRH.riemannZeta_ne_zero_of_slackRefined_lt_re

end TrackerSlack.Gate

#print axioms TrackerSlack.Gate.allDirichlet
#print axioms TrackerSlack.Gate.allHecke
#print axioms TrackerSlack.Gate.zeta
