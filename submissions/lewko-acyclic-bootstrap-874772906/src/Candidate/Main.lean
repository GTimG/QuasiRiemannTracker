/- Private Mark Lewko parameter instance, 2026-10-22.
Analytic/source interfaces: Hailey Collet, Apache-2.0; retained notices in vendor/collet. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Endpoint
set_option autoImplicit false
namespace Candidate
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
 (hs : (437386453/500000000:ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
 _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
 apply Lewko.QRH.Endpoint.dirichlet_nonvanishing χ
 · convert hs using 1 <;> norm_num
 · exact hpole
end Candidate
#print Candidate.bound
#print axioms Candidate.bound
