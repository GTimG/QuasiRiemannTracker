/- Copyright (c) 2026 Sil. Apache-2.0.
Combines the finite numerator and analytic transport into a primitive
common probe from the full source and the established prior bound.
-/
import Candidate.FourthPower.ReturnFiniteNumerator
import Candidate.FourthPower.TransportFinal
import Candidate.FourthPower.TerminalTransfer
import Candidate.FourthPower.OlderIncumbentContract

set_option autoImplicit false
namespace Candidate.FourthPower.ReturnCommonProbe
noncomputable section
open scoped Classical
open Filter Asymptotics OAI.SevenEighths HeckeFamily
open QRH.Record12518109Existence
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.GenericPhysical.Assembly
open ReturnSourceFaces ReturnFiniteNumerator TargetCompatibility

local instance : Geometry.Parameters := ReturnSourceInputs.parameters
local instance : CountScheme := ReturnWindows.countScheme
local instance : TransportBounds :=
  TransportBounds.of_exact_values rfl rfl rfl rfl

/-- The same actual detector/source/transport data and positive error saving
are fixed before all characters. A character-dependent height is chosen only
inside the proof of its high estimate. The low estimate uses the same probe.
The source hypotheses are consumed; no count, numerator, high estimate or
common-probe conclusion is separately requested. -/
theorem common_probe_from_full_source (hPrior : OlderIncumbentContract.OlderIncumbentInput)
    (hsource : UniformUnitFaceSource fullSourceFace) :
    Cycle25.UniformCommonProbe theta probeShift := by
  intro hgap
  obtain ⟨A,P,J,_hJ,hfinite⟩ :=
    exists_finite_numerator hPrior hsource hgap 1 (by norm_num)
  have hloss : 0<(HeckeZeroSupremum.beta-theta)/2 :=
    half_pos (sub_pos.mpr hgap)
  have hcontract :=
    QRH.Record1252270103Return.GenericPhysical.FourthPowerFinalAssembly.fixed_source_contract
      A.D A.F ((HeckeZeroSupremum.beta-theta)/2) P.sigma hloss (by
        intro η
        obtain ⟨tau,hheight,hnum⟩ := hfinite η
        exact QRH.Record1252270103Return.GenericPhysical.FourthPowerFinalAssembly.sourceProbe_high_of_finite_numerator_at
          A.D A.F P J tau hheight hgap.le η
            hnum)
  have hshift : Assembly.signalShift=probeShift :=
    ReturnFiniteNumerator.actual_signal_shift.trans rfl
  refine ⟨(HeckeZeroSupremum.beta-theta)/2,P.sigma,hloss,?_,P.sigma_pos,?_⟩
  · linarith
  · change Cycle25.PrimitiveProbeContract theta Assembly.signalShift
      ((HeckeZeroSupremum.beta-theta)/2) P.sigma at hcontract
    simpa only [hshift] using hcontract

/-- The source estimate is used in the contrary branch. The complementary
branch directly satisfies the target inequality. -/
theorem common_probe_of_contrary_source (hPrior : OlderIncumbentContract.OlderIncumbentInput)
    (hsource : theta<HeckeZeroSupremum.beta →
      UniformUnitFaceSource fullSourceFace) :
    Cycle25.UniformCommonProbe theta probeShift := by
  intro hgap
  exact common_probe_from_full_source hPrior (hsource hgap) hgap

theorem beta_of_contrary_source (hPrior : OlderIncumbentContract.OlderIncumbentInput)
    (hsource : theta<HeckeZeroSupremum.beta →
      UniformUnitFaceSource fullSourceFace) :
    HeckeZeroSupremum.beta≤theta :=
  TerminalTransfer.beta_of_common_probe (common_probe_of_contrary_source hPrior hsource)

theorem canonical_of_contrary_source (hPrior : OlderIncumbentContract.OlderIncumbentInput)
    (hsource : theta<HeckeZeroSupremum.beta →
      UniformUnitFaceSource fullSourceFace) : TerminalTransfer.CanonicalGoal :=
  TerminalTransfer.canonical_of_return_probe
    (common_probe_of_contrary_source hPrior hsource)

end
end Candidate.FourthPower.ReturnCommonProbe
