import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.HighRetainedRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.LowBranch.FinalDictionary

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEnergyState CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual residual allocation changes its two raw plain scales and
restricts the live slot index. It does not change the row mask or frequency. -/
theorem final_source_row_eq
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (src : Data ι) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (pool : ι → Finset (Ideal O)) (coeff : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t : ℝ) (z : O)
    (hchar : src.η = st.character) (hmask : src.m = st.mask)
    (hA : src.A = 1) (ht : src.t = t)
    (hpool : ∀ j, src.slots j = pool j)
    (hcoeff : ∀ j I, src.coefficient j I = coeff j I)
    (hP : ∀ j, src.P j = P j) :
    Cycle61.Physical.sourcePositiveRow src.toSource second L a z =
      retainedPositiveRow st.character st.mask 1 z src.W₁ src.W₂
        (fun j : liveIndices L a => pool j)
        (fun j : liveIndices L a => coeff j)
        (fun j : liveIndices L a => P j) t
        (Cycle61.Physical.postPlainScale L a
          (Cycle61.Physical.sourcePlainScales src.toSource second) 0)
        (Cycle61.Physical.postPlainScale L a
          (Cycle61.Physical.sourcePlainScales src.toSource second) 1) := by
  change retainedPositiveRow src.η src.m src.A z src.W₁ src.W₂
    (fun j : liveIndices L a => src.slots j)
    (fun j : liveIndices L a => src.coefficient j)
    (fun j : liveIndices L a => src.P j) src.t _ _ = _
  rw [hchar,hmask,hA,ht]
  simp_rw [hpool, funext (hcoeff _), hP]
  rfl

#print axioms final_source_row_eq
end
end OAI.SevenEighths.Cycle61Moment
