import Cycle25.Assembly.Continuation
import Cycle25.Assembly.Low.SourceProbe

/-! Transfer the actual compensated source probe to the common-probe contract.
Adapted from weighted upstream HighRows/ConditionalFinal, revision
2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
namespace Cycle25.FinalAssembly
noncomputable section
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily ProbePhysical Cycle25ProbeFinalAssembly PrincipalSignalComparison
open Cycle25WeightedHighFinalAssembly

noncomputable def signalShift : ℝ := -(4+Cycle25.b)/6

theorem source_contract {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (loss : ℝ) (hloss : 0 < loss)
    (herror : ∀η : Character,
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+signalShift-D.sigma))) :
    PrimitiveProbeContract theta signalShift loss D.sigma := by
  intro η _hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,
    sourceProbe D F η,hmask,hH,hHbound,?_,herror η⟩
  convert sourceProbe_low D F loss hloss η using 1
  funext Z
  congr 1
  dsimp [Cycle25.signal,signalShift]
  ring
end
end Cycle25.FinalAssembly
