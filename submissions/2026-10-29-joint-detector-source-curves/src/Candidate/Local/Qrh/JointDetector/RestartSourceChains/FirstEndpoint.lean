/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.FirstBank
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.ActualProvider
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.PreviousCeiling
import Candidate.Local.Qrh.JointDetector.LowRestartBank.Closures
namespace Qrh.JointDetector.RestartSourceChains.FirstEndpoint
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths

private theorem count_provider (hprev : HeckeZeroSupremum.beta ≤ (87393871/100000000:ℝ))
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) : FirstRestartReturn.SourceBank :=
 FirstRestartReturn.sourceBank_of_suppliers
   (First.bankSuppliers actualParentCores hβ (LowRestartBank.first_source hβ hprev))

private theorem physical_provider (hprev : HeckeZeroSupremum.beta ≤ (87393871/100000000:ℝ))
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
 QRH.Record12518109Existence.UniformUnitFaceSource FirstRestartReturn.physicalSourceFace :=
 First.physicalSource actualParentCores hβ (LowRestartBank.first_source hβ hprev)

theorem beta_le_theta_of_previous (hprev : HeckeZeroSupremum.beta ≤ (87393871/100000000:ℝ)) :
 HeckeZeroSupremum.beta ≤ (43691837/50000000:ℝ) := by
 simpa only [FirstRestartReturn.theta] using
   FirstRestartReturn.beta_le_theta (count_provider hprev) (physical_provider hprev)

theorem beta_le_theta : HeckeZeroSupremum.beta ≤ (43691837/50000000:ℝ) :=
 beta_le_theta_of_previous previous_beta_le

theorem bound_of_previous (hprev : HeckeZeroSupremum.beta ≤ (87393871/100000000:ℝ))
 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
 (hs : (43691837/50000000:ℝ) < s.re) (hpole : ¬ (χ=1 ∧ s=1)) :
 DirichletCharacter.LFunction χ s ≠ 0 :=
 FirstRestartReturn.bound (count_provider hprev) (physical_provider hprev) χ hs hpole

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
 (hs : (43691837/50000000:ℝ) < s.re) (hpole : ¬ (χ=1 ∧ s=1)) :
 DirichletCharacter.LFunction χ s ≠ 0 :=
 bound_of_previous previous_beta_le χ hs hpole

#print axioms beta_le_theta
#print axioms bound
end
end Qrh.JointDetector.RestartSourceChains.FirstEndpoint
