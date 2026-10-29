/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.SourceCurveIntegerSources.Endpoint
import Candidate.Local.Qrh.JointDetector.CurvedSourceChains.BestEndpoint
namespace Qrh.JointDetector.SourceCurveIntegerSources.BestEndpoint
noncomputable section
open OAI.SevenEighths

theorem beta_le_theta : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ) :=
 SourceCurveIntegerSources.beta_le_theta_of_previous CurvedSourceChains.BestEndpoint.beta_le_theta

theorem bound {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
 (hs : (8738357037/10000000000:ℝ) < s.re) (hpole : ¬(χ=1 ∧ s=1)) :
 _root_.DirichletCharacter.LFunction χ s≠0 :=
 SourceCurveIntegerSources.bound_of_previous CurvedSourceChains.BestEndpoint.beta_le_theta χ hs hpole
end
end Qrh.JointDetector.SourceCurveIntegerSources.BestEndpoint
