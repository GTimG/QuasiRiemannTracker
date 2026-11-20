/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Normalized positive physical shares on the genuine clipped image average. -/
import Candidate.C092.transport.PairedRetainedBudgetRaw
import Candidate.C092.transport.PairedRetainedBudgetLambda
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type} [Fintype ι]

/-- The zero/tail supplier and both physical part suppliers may keep the
    original source-volume denominator throughout. The three shares sum to one. -/
theorem averagedSecondSidePrice_of_normalized_shares
    (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s) (w : ι→ℝ) (G : Id)
    (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ)
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : HeckeFamily.O)
    (t K Z ξ Cz Ct target : ℝ)
    (hJ : ∀B,(∑j∈Js B,w j.val) ≤ 3/5000)
    (hM : MultBound s (by norm_num) cover G Js K
      (fun B=>RawSides.selectionScaleQ s (by norm_num) cover G B (Js B)) M)
    (hMcap : ∀B,M B ≤ (selY (allocatedLiveSource s (by norm_num) cover G B) (Js B)).card)
    (hdiag : averagedDiagonalCost s cover G Js M η₁ η₂ τ t K Z Cz Ct/sourceVolume s ≤
      (1/4)*target/sourceVolume s)
    (hfixed : averagedPartSideCost true s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ/sourceVolume s ≤
      (3/8)*target/sourceVolume s)
    (hregular : averagedPartSideCost false s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ/sourceVolume s ≤
      (3/8)*target/sourceVolume s) :
    AveragedSecondSidePrice s cover w G η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct target := by
  refine ⟨Js,M,hJ,hM,hMcap,?_⟩
  rw [averagedSecondCost_split,add_div,add_div]
  exact (add_le_add (add_le_add hdiag hfixed) hregular).trans_eq (by ring)

/-- A supplied valid multiplicity is clipped once. This is the literal interface
    returned by the authenticated colored Poisson/selection and diagonal bounds. -/
theorem averagedSecondSidePrice_of_clipped_shares
    (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s) (w : ι→ℝ) (G : Id)
    (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ)
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : HeckeFamily.O)
    (t K Z ξ Cz Ct target : ℝ)
    (hJ : ∀B,(∑j∈Js B,w j.val) ≤ 3/5000)
    (hM : MultBound s (by norm_num) cover G Js K
      (fun B=>RawSides.selectionScaleQ s (by norm_num) cover G B (Js B)) M)
    (hdiag : averagedDiagonalCost s cover G Js
      (ColoredSelectionAverage.clippedMultiplicity s (by norm_num) cover G Js M)
      η₁ η₂ τ t K Z Cz Ct/sourceVolume s ≤ (1/4)*target/sourceVolume s)
    (hfixed : averagedPartSideCost true s cover G Js
      (ColoredSelectionAverage.clippedMultiplicity s (by norm_num) cover G Js M)
      η₁ η₂ τ χ₀ Q m t K Z ξ/sourceVolume s ≤ (3/8)*target/sourceVolume s)
    (hregular : averagedPartSideCost false s cover G Js
      (ColoredSelectionAverage.clippedMultiplicity s (by norm_num) cover G Js M)
      η₁ η₂ τ χ₀ Q m t K Z ξ/sourceVolume s ≤ (3/8)*target/sourceVolume s) :
    AveragedSecondSidePrice s cover w G η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct target := by
  exact averagedSecondSidePrice_of_normalized_shares s cover w G Js
    (ColoredSelectionAverage.clippedMultiplicity s (by norm_num) cover G Js M)
    η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct target hJ
    (ColoredSelectionAverage.multBound_clipped s (by norm_num) cover G Js K
      (fun B=>RawSides.selectionScaleQ s (by norm_num) cover G B (Js B)) M hM)
    (ColoredSelectionAverage.clippedMultiplicity_le_card s (by norm_num) cover G Js M)
    hdiag hfixed hregular

#print axioms averagedSecondSidePrice_of_normalized_shares
#print axioms averagedSecondSidePrice_of_clipped_shares
end
end QRH.Cycle092.PairedRetainedBudget
