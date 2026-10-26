/- Private Mark Lewko parameter instance, 2026-10-22.
Analytic/source interfaces: Hailey Collet, Apache-2.0; retained notices in vendor/collet. -/
import Candidate.Main
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.ParentAudit
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.ParentAudit
set_option autoImplicit false
example : (874772906/1000000000:ℝ) = 437386453/500000000 := by norm_num
example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
 (hs : (437386453/500000000:ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
 _root_.DirichletCharacter.LFunction χ s ≠ 0 := Candidate.bound χ hs hpole
#check @Candidate.bound
#print axioms Candidate.bound
#print axioms Lewko.QRH.Endpoint.first_hecke_nonvanishing
#print axioms Lewko.QRH.Endpoint.hecke_nonvanishing
