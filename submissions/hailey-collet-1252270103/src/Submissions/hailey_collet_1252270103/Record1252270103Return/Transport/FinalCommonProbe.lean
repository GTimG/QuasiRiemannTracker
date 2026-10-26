/- Common-probe consumer adapted from Zhongpai Gao's PR63 physical closure,
retaining the inherited Hailey Collet/Cycle25 and OpenAI continuation. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.FinalFixedHigh
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Continuation

set_option autoImplicit false
namespace QRH.Record1252270103Return.GenericPhysical.FinalAssembly
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.Bounds]
open scoped Classical
open QRH.Record1252270103Return.Geometry OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Record1252270103Return.GenericPhysical QRH.Record1252270103Return.GenericPhysical.Assembly

/-- The geometry, source and positive saving precede the live character.
Only the buffered height may depend on that character. -/
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
    (show (1/2:ℝ) ≤ theta by linarith [Geometry.Bounds.theta_bounds.1])
    (show theta ≤ (7/8:ℝ) from Geometry.Bounds.theta_bounds.2.le)
    (common_probe_of_finite_numerator hinput)

end
end QRH.Record1252270103Return.GenericPhysical.FinalAssembly
#print axioms QRH.Record1252270103Return.GenericPhysical.FinalAssembly.common_probe_of_finite_numerator
#print axioms QRH.Record1252270103Return.GenericPhysical.FinalAssembly.beta_le_theta_of_finite_numerator
