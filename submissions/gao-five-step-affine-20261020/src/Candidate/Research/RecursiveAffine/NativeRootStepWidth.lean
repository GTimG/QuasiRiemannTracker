/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootStep

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153RootStep
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands
open Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass
open Cycle63Moment.LowBranch Cycle153ContinuationUnit
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The genuine outer source uses radial exponent Mrow=1 from the
initial reduction. No `NaturalState.rowWidth=1` premise is introduced.
The original fixed character and finite native constants are absorbed
only through their literal eventual threshold gates. -/
theorem actual_root_native_width
    (s : Input α) (ch : Chain s) (χ : RayFourExpansion.RayCharacter) (t Z : ℝ) (hZ : 1<Z)
    (n : ℕ) (bs omega xi reserve Bmask : ℝ) (w : α→ℝ)
    (g : LiveMainGeometry s ch Z 1 (rootSourceAmp w) omega xi bs n)
    (hb : 0<bs) (Q : Ideal O) (hP : ch.R₂*ch.E₂≠0)
    (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ Z^Bmask)
    (hfit : Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ reserve/2)
    (hconstants : Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(n:ℝ)*Real.logb Z bs+Real.logb Z 1+
      Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)) ≤ (reserve/2)*1)
    (homega : omega=frequencyLoss Z 32 xi+reserve*1)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2))) (Rdel : Finset α) :
    let st := retainedState Z Bmask hZ (g.datum.τ χ) Q (ch.R₂*ch.E₂) hP hPN
      g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let r := nativeRootStepValues s ch (g.datum.τ χ) t Z n bs 1 omega xi reserve w g second L alloc Rdel
    st.width ≤ r.u := by
  exact (actual_native_unit g Bmask hZ hb χ Q hP hPN (by linarith only [hfit]) hconstants homega).1
end
end OAI.SevenEighths.Cycle153RootStep
#print axioms OAI.SevenEighths.Cycle153RootStep.actual_root_native_width
