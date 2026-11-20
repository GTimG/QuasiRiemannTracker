/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
An empty ACTUAL colored carrier has zero fixed and regular physical cost.
No cutoff or nonempty sharp-cap hypothesis is needed on this branch. -/
import Candidate.C092.transport.RootColoredSeed
import Candidate.C092.transport.PairedRetainedBudgetWeights
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentSourceRow
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedFirstLiveSource
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) emptySubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _

theorem groupedPartTerms_of_empty {ι:Type*}[Fintype ι]{a b:ℝ}
    (s:Source ι a b)(ha:0<a)(ω₁ ω₂:Id→ℂ)
    (h:RootColoredSeed.active s ha ω₁ ω₂=∅)(part:Bool)
    (ψ:Character)(χ₀:RayCharacter)(Q:Id)(m:O)(t K Tsec Z ξ H:ℝ) :
    RootColoredSeed.groupedPartTerms part s ha ω₁ ω₂ ψ χ₀ Q m t K Tsec Z ξ H=0 := by
  have hlabels:commonLabels (supportedColumns (RootColoredSeed.active s ha ω₁ ω₂))
      (supportedColumns (RootColoredSeed.active s ha ω₁ ω₂))=∅:=by
    rw [h];simp [supportedColumns,commonLabels]
  haveI:IsEmpty ↥(commonLabels (supportedColumns (RootColoredSeed.active s ha ω₁ ω₂))
      (supportedColumns (RootColoredSeed.active s ha ω₁ ω₂))):=by
    rw [hlabels];infer_instance
  unfold RootColoredSeed.groupedPartTerms
  exact Finset.sum_eq_zero (fun x _=>isEmptyElim x)

/-- The same exact zero applies at each actual first allocation and
selected prefix, for both flags and every native second radius. -/
theorem selectedPartTerm_of_empty {ι:Type}[Fintype ι]
    (s:Source ι (1/4) (9/4))(cover:OriginalEnclosure s)(G:Id)
    (B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val))
    (η₁ η₂ τ:Character)(χ₀:RayCharacter)(Q:Id)(m:O)(t K Z ξ:ℝ)(ζ:RayCharacter)
    (h:RootColoredSeed.active (restOf s (by norm_num) cover G B J) (by norm_num)
      (idealCoeff η₁) (idealCoeff η₂)=∅)(part:Bool) :
    PairedRetainedBudget.selectedPartTerm part s cover G B J η₁ η₂ τ χ₀ Q m t K Z ξ ζ=0 := by
  unfold PairedRetainedBudget.selectedPartTerm
  exact groupedPartTerms_of_empty _ _ _ _ h part _ _ _ _ _ _ _ _ _ _

#print axioms groupedPartTerms_of_empty
#print axioms selectedPartTerm_of_empty
end
end QRH.Cycle092.ActualStageFrameBudget
