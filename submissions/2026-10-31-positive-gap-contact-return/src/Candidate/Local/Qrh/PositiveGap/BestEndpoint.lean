/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Dirichlet nonvanishing above 5458637291332547/6250000000000000 = 0.87338196661320752. -/
import Candidate.Local.Qrh.PositiveGap.SourceComposition
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.Endpoint

set_option autoImplicit false
namespace Qrh.PositiveGap
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source

/-- The proved positive-gap source supplies the final return face. -/
theorem return_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999999999999999999/100000000000000000000)
      (20000000000000000001/10000000000000000000) (671447/5000000) := by
  apply QRH.PositiveGap.Return.Tuning.uniform_restrict
    (strong := globalFace (99999999999999999999/100000000000000000000)
      (20000000000000000001/10000000000000000000) (3/20))
  · constructor <;> norm_num [globalFace]
  · exact QRH.PositiveGap.source hβ

theorem beta_le_theta :
    HeckeZeroSupremum.beta ≤ (5458637291332547/6250000000000000 : ℝ) :=
  QRH.PositiveGap.Return.Tuning.beta_le_target_of_global_source return_source

/-- Dirichlet nonvanishing for every positive modulus and every character. -/
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (5458637291332547/6250000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.PositiveGap.Return.Tuning.dirichlet_of_global_source return_source χ hs hpole
end
end Qrh.PositiveGap

#print axioms Qrh.PositiveGap.beta_le_theta
#print axioms Qrh.PositiveGap.bound
