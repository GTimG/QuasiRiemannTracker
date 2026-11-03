/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/PlainInputs.lean
Original SHA-256: a440635d8561c5670c88db8e6b11aae88ae5e3a1bc4255454fa0b4fa6c76ff2a
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.PlainInputExtract
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.PlainEnergy

namespace LW56e2.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainUnmarkedField
local notation "O"=>HeckeFamily.O

/-- The required positive and zero arithmetic energy inputs are produced
from the actual proved OpenAI003 energy induction under the accepted ceiling. -/
theorem actual_plain_inputs {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (N:ℕ)(εm:ℝ)(hεm:0<εm)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hceiling:HeckeZeroSupremum.beta≤7/8):
    PositiveFineSourceInput F N εm (plainMesh εm) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (εm/4) U degree control A):=by
  apply plain_inputs F N εm hεm
  intro bΦ hbΦ
  exact actual_plain_energy_fixed_kappa (Slot:=Fin N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x)) (CenteredMomentDetectorPlainSlotProfile.conjugate_source_support F)
    (Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)) bΦ (εm/4) hbΦ (by positivity)
    hbeta hceiling

end
end LW56e2.Transport.PhysicalHigh
