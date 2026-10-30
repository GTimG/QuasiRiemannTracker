/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module Transport.FinalCommonProbe (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Common-probe consumer adapted from Zhongpai Gao's PR63 physical closure,
retaining the inherited Hailey Collet/Cycle25 and OpenAI continuation. Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
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
    (show (1/2:ℝ) ≤ theta by linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.theta_bounds.1])
    (show theta ≤ (7/8:ℝ) from Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.theta_bounds.2.le)
    (common_probe_of_finite_numerator hinput)

end
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
