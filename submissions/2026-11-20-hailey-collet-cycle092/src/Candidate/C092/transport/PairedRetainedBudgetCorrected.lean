/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Concrete second-side prices on the corrected selected-image measure. -/
import Candidate.C092.transport.PairedRetainedBudgetAverageScalar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
local instance (priority := 2000) pairedCorrectedSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource MixedInnerExceptionalBlock
open MixedOriginalTail
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.TwistedRawBall
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

def numericalTerm (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (K Z Cz Ct : ℝ) : ℝ :=
  Cz*profileCap (restOf s (by norm_num) cover G B J)^2*K*Z^(93/100:ℝ)+
    Ct*profileCap (restOf s (by norm_num) cover G B J)^2*Z^(-22:ℝ)

def averagedDiagonalCost (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (G : Id) (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ) (η₁ η₂ τ : Character) (t K Z Cz Ct : ℝ) : ℝ :=
  coloredOuterAverage s cover G Js η₁ η₂ τ t M (fun B _=>numericalTerm s cover G B (Js B) K Z Cz Ct)

def averagedSecondCost (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (G : Id) (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ) (η₁ η₂ τ : Character)
    (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Z ξ Cz Ct : ℝ) : ℝ :=
  coloredOuterAverage s cover G Js η₁ η₂ τ t M (fun B ζ=>
    numericalTerm s cover G B (Js B) K Z Cz Ct+
      selectedPartTerm true s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ+
      selectedPartTerm false s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ)

/-- Only after authentic image compression is the positive physical ledger
    divided into its numerical, fixed and regular pieces. -/
theorem averagedSecondCost_split (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (G : Id) (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ) (η₁ η₂ τ : Character)
    (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Z ξ Cz Ct : ℝ) :
    averagedSecondCost s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct =
      averagedDiagonalCost s cover G Js M η₁ η₂ τ t K Z Cz Ct+
        averagedPartSideCost true s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ+
        averagedPartSideCost false s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ := by
  unfold averagedSecondCost averagedDiagonalCost averagedPartSideCost coloredOuterAverage
  simp only [Finset.sum_add_distrib,mul_add]

/-- An authentic finite child price, including the real image multiplicity
    condition. It has no source-energy hypothesis and no free selY sum. -/
def AveragedSecondSidePrice (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (w : ι→ℝ) (G : Id) (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Z ξ Cz Ct target : ℝ) : Prop :=
  ∃Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val),
  ∃M : actualAllocations (tuplePools s) G→ℝ,
    (∀B,(∑j∈Js B,w j.val) ≤ 3/5000) ∧
    MultBound s (by norm_num) cover G Js K
      (fun B=>RawSides.selectionScaleQ s (by norm_num) cover G B (Js B)) M ∧
    (∀B,M B ≤ (selY (allocatedLiveSource s (by norm_num) cover G B) (Js B)).card) ∧
    averagedSecondCost s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct/sourceVolume s ≤ target/sourceVolume s

theorem averagedSecondSidePrice_of_shares (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (w : ι→ℝ) (G : Id) (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ)
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Z ξ Cz Ct target : ℝ)
    (hJ : ∀B,(∑j∈Js B,w j.val) ≤ 3/5000)
    (hM : MultBound s (by norm_num) cover G Js K
      (fun B=>RawSides.selectionScaleQ s (by norm_num) cover G B (Js B)) M)
    (hMcap : ∀B,M B ≤ (selY (allocatedLiveSource s (by norm_num) cover G B) (Js B)).card)
    (hdiag : averagedDiagonalCost s cover G Js M η₁ η₂ τ t K Z Cz Ct ≤ target/4)
    (hfixed : averagedPartSideCost true s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ ≤ 3*target/8)
    (hregular : averagedPartSideCost false s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ ≤ 3*target/8) :
    AveragedSecondSidePrice s cover w G η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct target := by
  refine ⟨Js,M,hJ,hM,hMcap,?_⟩
  rw [averagedSecondCost_split]
  apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
  linarith

#print axioms averagedSecondCost_split
#print axioms averagedSecondSidePrice_of_shares
end
end QRH.Cycle092.PairedRetainedBudget
