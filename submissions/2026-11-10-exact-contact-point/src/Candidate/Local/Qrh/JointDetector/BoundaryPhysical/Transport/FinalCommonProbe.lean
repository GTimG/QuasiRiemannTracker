import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.FinalFixedHigh
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Continuation
set_option autoImplicit false
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
open scoped Classical
open QRH.Record1252270103Return.Geometry OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Record1252270103Return.GenericPhysical Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
def ChosenFiniteNumeratorInput : Prop :=
  theta < HeckeZeroSupremum.beta →
    ∃ D : BaselineData, ∃ F : BaselineSourceData D, ∃ P : TransportParameters D,
      ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ τ : ℝ,
        HeightAdmissible D P J τ ∧ FixedFiniteNumeratorInputAt D F P τ η
theorem common_probe_of_finite_numerator (hinput : ChosenFiniteNumeratorInput) :
    Cycle25.UniformCommonProbe theta Assembly.signalShift := by
  intro hβ
  obtain ⟨D,F,P,J,hJ,hfinite⟩ := hinput hβ
  let loss := (HeckeZeroSupremum.beta-theta)/2
  have hloss : 0 < loss := by dsimp [loss]; linarith
  have hgap : loss < HeckeZeroSupremum.beta-theta := by dsimp [loss]; linarith
  refine ⟨loss,P.sigma,hloss,hgap,P.sigma_pos,?_⟩
  apply fixed_source_contract D F loss P.sigma hloss
  intro η
  obtain ⟨τ,hheight,hnum⟩ := hfinite η
  exact sourceProbe_high_of_finite_numerator_at D F P J τ hheight hβ.le η hnum
theorem beta_le_theta_of_finite_numerator (hinput : ChosenFiniteNumeratorInput) :
    HeckeZeroSupremum.beta ≤ theta := by
  exact Cycle25.beta_le_of_common_probe
    (show (1/2:ℝ) ≤ theta by linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.theta_bounds.1])
    (show theta ≤ (7/8:ℝ) from Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.theta_bounds.2.le)
    (common_probe_of_finite_numerator hinput)
end
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
