/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalInput
import Candidate.C092.transport.RegularColoredTerminalLeafStateInput
import Candidate.C092.transport.P2StageScalarsLate
import Candidate.C092.transport.RegularColoredTerminalLeafOccupied
import Candidate.C092.transport.RegularColoredTerminalLeafLengths
import Candidate.C092.transport.RegularColoredTerminalLeafHomogeneous
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafOriginalHeights_a3d5062a47951e84_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M]
variable {A : Arithmetic M} {n y mesh U V : ℝ}

/-- The positive half-tau collar handles both the detector's combined
height and the original global source's old-height gate. -/
theorem terminal_original_height_gates (F : TerminalOriginalInput Slot M A n y mesh U V)
    {tau : ℝ} (hU : 1 < U) (htau : tau ≤ 1/4)
    (hhalf : 2 ≤ U^(tau/2))
    (hphysical : 1+|F.tLong|+|F.tShort|+F.height ≤ U^(tau/2)) :
    |F.tShort|+|F.tLong|+2*F.height ≤ U^tau ∧
      |F.tOld|+F.height ≤ U^(1/2:ℝ) := by
  have hH : 0 ≤ 1+|F.tLong|+|F.tShort|+F.height := by
    linarith only [abs_nonneg F.tLong,abs_nonneg F.tShort,F.height_nonneg]
  have hbase : 0 ≤ U^(tau/2) := Real.rpow_nonneg (zero_lt_one.trans hU).le _
  have htwo : 2*(1+|F.tLong|+|F.tShort|+F.height) ≤ U^tau := by
    calc
      _ ≤ U^(tau/2)*U^(tau/2) := mul_le_mul hhalf hphysical hH hbase
      _ = U^tau := by rw [←Real.rpow_add (zero_lt_one.trans hU)];congr 1;ring
  have hfull : |F.tShort|+|F.tLong|+2*F.height ≤ U^tau := by
    linarith only [htwo,abs_nonneg F.tLong,abs_nonneg F.tShort]
  refine ⟨hfull,?_⟩
  have hOld : |F.tOld|+F.height ≤ U^tau := by
    linarith only [htwo,F.old_height,abs_nonneg F.tLong,abs_nonneg F.tShort]
  exact hOld.trans (Real.rpow_le_rpow_of_exponent_le hU.le (by linarith only [htau]))

#print axioms terminal_original_height_gates
end
end QRH.Cycle092.RegularColoredForward
