/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PR97Refinement.RefinedSource
import Candidate.Local.Qrh.PR97Refinement.Return.Tuning.Endpoint

set_option autoImplicit false

namespace Qrh.PR97Refinement
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source

/-- The proved native source supplies the smaller cap used by the return. -/
theorem return_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999/100000) (200001/100000) (671447/5000000) := by
  apply QRH.PR97Refinement.Return.Tuning.uniform_restrict
    (strong := globalFace (99999/100000) (200001/100000) (3/20))
  · constructor <;> norm_num [globalFace]
  · exact QRH.QrhPR97Refinement.refined_end hβ

theorem beta_le_theta :
    HeckeZeroSupremum.beta ≤ (1746764287/2000000000 : ℝ) :=
  QRH.PR97Refinement.Return.Tuning.beta_le_target_of_global_source return_source

/-- Dirichlet nonvanishing for every positive modulus and every character. -/
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1746764287/2000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.PR97Refinement.Return.Tuning.dirichlet_of_global_source return_source χ hs hpole

end
end Qrh.PR97Refinement

#print axioms Qrh.PR97Refinement.beta_le_theta
#print axioms Qrh.PR97Refinement.bound
