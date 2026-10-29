/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.SecondBank
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.ActualProvider
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.FirstEndpoint
import Candidate.Local.Qrh.JointDetector.LowRestartBank.Closures
namespace Qrh.JointDetector.RestartSourceChains.SecondEndpoint
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths

private theorem count_provider (hprev : HeckeZeroSupremum.beta ≤ (43691837/50000000:ℝ))
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) : RestartReturn.SourceBank :=
 RestartReturn.sourceBank_of_suppliers
   (Second.bankSuppliers actualParentCores hβ (LowRestartBank.second_source hβ hprev))

private theorem physical_provider (hprev : HeckeZeroSupremum.beta ≤ (43691837/50000000:ℝ))
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
 QRH.Record12518109Existence.UniformUnitFaceSource RestartReturn.physicalSourceFace :=
 Second.physicalSource actualParentCores hβ (LowRestartBank.second_source hβ hprev)

theorem beta_le_theta_of_previous (hprev : HeckeZeroSupremum.beta ≤ (43691837/50000000:ℝ)) :
 HeckeZeroSupremum.beta ≤ (1747671527/2000000000:ℝ) := by
 simpa only [RestartReturn.theta] using
   RestartReturn.beta_le_theta (count_provider hprev) (physical_provider hprev)

theorem beta_le_theta : HeckeZeroSupremum.beta ≤ (1747671527/2000000000:ℝ) :=
 beta_le_theta_of_previous FirstEndpoint.beta_le_theta

theorem bound_of_previous (hprev : HeckeZeroSupremum.beta ≤ (43691837/50000000:ℝ))
 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
 (hs : (1747671527/2000000000:ℝ) < s.re) (hpole : ¬ (χ=1 ∧ s=1)) :
 DirichletCharacter.LFunction χ s ≠ 0 :=
 RestartReturn.bound (count_provider hprev) (physical_provider hprev) χ hs hpole

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
 (hs : (1747671527/2000000000:ℝ) < s.re) (hpole : ¬ (χ=1 ∧ s=1)) :
 DirichletCharacter.LFunction χ s ≠ 0 :=
 bound_of_previous FirstEndpoint.beta_le_theta χ hs hpole

#print axioms beta_le_theta
#print axioms bound
end
end Qrh.JointDetector.RestartSourceChains.SecondEndpoint
