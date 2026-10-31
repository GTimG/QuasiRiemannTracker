/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The reserve-parametric seed and above-half selected energy supply the complete return. -/
import Candidate.Local.Qrh.PR98Improvement.RepairedRestrictedSource
import Candidate.Local.Qrh.PR98Improvement.SourceComposition
import Candidate.Local.Qrh.PR99Improvement.Return.Tuning.Endpoint

set_option autoImplicit false
namespace Qrh.PR99Improvement
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source

/-- The proved seed and two finite source lines supply the final return face. -/
theorem return_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999999999999/100000000000000)
      (20000000000001/10000000000000) (671447/5000000) := by
  have hseed : GlobalSource (99999999999999/100000000000000) (93/25) (3/50) := by
    convert Candidate.PR98.RepairedRestrictedSource.generalized_seed
      (1/100000000000000) (by norm_num) (by norm_num) hβ using 1 <;> norm_num
  apply QRH.PR99Improvement.Return.Tuning.uniform_restrict
    (strong := globalFace (99999999999999/100000000000000)
      (20000000000001/10000000000000) (3/20))
  · constructor <;> norm_num [globalFace]
  · exact QRH.QrhPR98Improvement.source_of_generalized_seed hβ hseed

theorem beta_le_theta :
    HeckeZeroSupremum.beta ≤ (8733819666132079/10000000000000000 : ℝ) :=
  QRH.PR99Improvement.Return.Tuning.beta_le_target_of_global_source return_source

/-- Dirichlet nonvanishing for every positive modulus and every character. -/
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (8733819666132079/10000000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.PR99Improvement.Return.Tuning.dirichlet_of_global_source return_source χ hs hpole
end
end Qrh.PR99Improvement

#print axioms Qrh.PR99Improvement.beta_le_theta
#print axioms Qrh.PR99Improvement.bound
