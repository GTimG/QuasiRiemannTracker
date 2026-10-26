/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowRows
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSourceRow
open Cycle63FinalNatural CenteredMomentEnergyState Cycle63Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentFiniteProfileExceptional
open LocalMoment
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainHighRowsSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The inclusive high cut keeps both literal buffered height intervals.
No zero, character, puncture or row is replaced by an abstract datum. -/
theorem actual_main_high_bin_intervals
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hhigh : ((1+Cycle63.AffineLedger.q)/2)≤bufferValue e p) :
    ((1+Cycle63.AffineLedger.q)/2)≤bufferValue e p ∧ bufferValue e p≤7/8 ∧
      bufferValue e p≤geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T)<bufferValue e p+e ∧
      bufferValue e p≤geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T)<bufferValue e p+2*e := by
  obtain ⟨_,_,_,hb,hcl,hcu,hnl,hnu,_⟩ := hbin
  exact ⟨hhigh,hb,hcl,hcu,hnl,hnu⟩

end
end OAI.SevenEighths.Cycle63InitialMass
