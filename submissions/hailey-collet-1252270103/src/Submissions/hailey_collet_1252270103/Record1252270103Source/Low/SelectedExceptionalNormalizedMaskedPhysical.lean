/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine corrected exceptional child estimate pays the physical block.
Only finite polynomial caps and the original character-family identity enter;
the full allocation count, frozen weights, divisor seed and row selector remain. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.ExceptionalWindow.MaskedPhysical
import Submissions.hailey_collet_1252270103.Record1252270103Source.ExceptionalWindow.MaskedPair
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.SelectedExceptionalInitialCapsFamily
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalNormalizedMasked
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Record1252270103Source
open Filter ExceptionalWindow
open scoped Classical BigOperators SchwartzMap
open Record1252270103Second Record1252270103GlobalSelected
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentFirstSectors
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondSectorColumns CenteredMomentSecondNonexceptional
open CenteredMomentSecondWholeKernel CenteredMomentSecondSectorRetained CenteredMomentSecondWindowBudget
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentMobiusRegroup RayFourExpansion
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile CenteredMomentSourceProfileMass
open ConcretePrimeRowBridge CenteredExceptionalProfile CenteredMomentChildRows CenteredMomentSecondHeightFamily
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open QRH.Record1252270103Source.ForcedCost
local notation "O"=>ActualEisensteinCubic.O
local notation "coefficient"=>QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι : Type*} [Fintype ι]
local instance selectedExceptionalPhysicalDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
open QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
open QRH.Record1252270103Source.High.GlobalPhysical SecondSectorDatum Cycle61InitialMass

/-- Sharp paired allocation payment at the same residual divisor L.
The full ordinary radical moment survives the two square roots. -/
def radicalPair (s:Input ι)(T:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))
    (Q C D L:Ideal O)(U:Finset (CommonIndex C D))
    (Z ε εL power Lraw Cr Mrow C₀ K₀:ℝ)(J:ℕ)(t:ℝ):ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
    ((Ideal.absNorm (∏p:CommonIndex C D,p.val):ℝ)^(2*power)/((C.absNorm:ℝ)*(D.absNorm:ℝ)))*
    (CenteredMomentCommonExceptionalCost.frozenProfile s)^2*
    correctedExceptionalBudget s T W₁ W₂ Φ Q C D L U Z ε εL power Lraw Cr Mrow C₀ K₀*
    (heightEnvelope t^J*profileMoment J)^2

/-- No divisor is removed: the full original residual pool is still summed. -/
def radicalDivisorSum (d:SecondInputDatum ι)(T:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q:Ideal O)
    (Z ε εL power H brad Lraw C₀ K₀:ℝ)(J:ℕ):ℝ :=
  ∑L∈divisorPool Finset.univ
    (fun I:sectorPool d.D d.hD.1 (finiteColumns (Fintype.piFinset d.input.pools))=>(I:Ideal O)),
    ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      radicalPair d.input T W₁ W₂ Φ Q d.C d.D L d.inactive Z ε εL power Lraw brad
        (Real.logb Z H) C₀ K₀ J d.input.t

def datumPayment (d:SecondInputDatum ι)(T:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q:Ideal O)
    (Z ε εL power H brad Lraw C₀ K₀ Cphys:ℝ)(J decay:ℕ):ℝ :=
  Cphys*(outerScalar d.C d.D d.K d.dyad*normalizer d.C d.D d.inactive)*
    radicalDivisorSum d T W₁ W₂ Φ Q Z ε εL power H brad Lraw C₀ K₀ J/
    (1+dyadicScale (d.dyad 0)*dyadicScale (d.dyad 1)/
      (dyadicScale (d.dyad 2)*dyadicScale (d.dyad 3)))^decay

/-- Exact normalization into the scalar used by actual_second_phase_bound. -/
theorem datum_phase_payment (d:SecondInputDatum ι)(w:ℂ)
    (T:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q:Ideal O)
    (Z ε εL power H brad Lraw C₀ K₀ Cphys:ℝ)(J decay:ℕ):
    ‖w‖*datumPayment d T W₁ W₂ Φ Q Z ε εL power H brad Lraw C₀ K₀ Cphys J decay=
      (‖w‖*d.block.outside*volume d.input)*
        (Cphys*radicalDivisorSum d T W₁ W₂ Φ Q Z ε εL power H brad Lraw C₀ K₀ J/volume d.input)/
        (1+dyadicScale (d.dyad 0)*dyadicScale (d.dyad 1)/
          (dyadicScale (d.dyad 2)*dyadicScale (d.dyad 3)))^decay := by
  have hv:volume d.input≠0:=(volume_pos d.input).ne'
  change ‖w‖*datumPayment d T W₁ W₂ Φ Q Z ε εL power H brad Lraw C₀ K₀ Cphys J decay=
    (‖w‖*(outerScalar d.C d.D d.K d.dyad*normalizer d.C d.D d.inactive)*volume d.input)*_/_
  unfold datumPayment
  field_simp [hv]
  <;> ring

end
end QRH.Record1252270103Source.Low.SelectedExceptionalNormalizedMasked
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalizedMasked.datum_phase_payment
