/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Exact allocation-weighted fixed/regular split of the first selected side. -/
import Candidate.C092.transport.TwistedRawBallPhysicalSidesCaps
import Candidate.C092.transport.RawPairDiagonalBudgetLedger
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
local instance (priority := 2000) pairedSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentChildRows
open CenteredMomentFirstAmplificationChoice
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock MixedOriginalNormCap
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.TwistedRawBall QRH.Cycle092.RawPairDiagonalBudget
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

/-- This is the actual fixed or regular physical contribution, retaining
    every allocation, selected assignment, ray and seed-support multiplicity. -/
def partSideCost (part : Bool) (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s) (G : Id)
    (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Z ξ : ℝ) : ℝ :=
  ((actualAllocations (tuplePools s) G).card : ℝ)*
    ∑B : actualAllocations (tuplePools s) G,
      allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
        (let rL := allocatedLiveSource s (by norm_num) cover G B
         let r := restOf s (by norm_num) cover G B (Js B)
         let W := RawSides.selectionScaleQ s (by norm_num) cover G B (Js B)
         let X := RawSides.residualCapQ r
         Atot rL (Js B) τ t * ∑y∈selY rL (Js B),∑χ : RayCharacter,∑ζ : RayCharacter,
           (2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card *
             RootColoredSeed.groupedPartTerms part r (by norm_num) (idealCoeff η₁) (idealCoeff η₂)
               (childCharacter τ ζ) χ₀ Q m t (16*K*W^4)
               (RootColoredSeed.secondCutoffQ X K W) Z ξ X)

/-- The original full-volume denominator is paid exactly once. The two
    signed completed physical parts and the proved numeric remainders are
    separated only after the actual seed completion and norms. -/
theorem secondSideCost_split (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (C D G : Id) (hD : D≠0)
    (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Z ξ Cz Ct : ℝ) :
    secondSideCost s cover C D hD G Js η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct =
      (secondDiagonalCost s (by norm_num) cover G Js η₁ η₂ τ t K Z Cz Ct+
        partSideCost true s cover G Js η₁ η₂ τ χ₀ Q m t K Z ξ+
        partSideCost false s cover G Js η₁ η₂ τ χ₀ Q m t K Z ξ)/sourceVolume s := by
  unfold secondSideCost ColoredGaussSelection.secondSelectedTerms secondDiagonalCost partSideCost
  simp only [mul_add,add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,
    Finset.sum_div,mul_div_assoc,add_div]
  ring

/-- A concrete price assembled from the numerical ledger and the two
    literal physical ledgers. All fractions refer to the same balanced target. -/
theorem secondSidePrice_of_parts (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (w : ι→ℝ) (C D G : Id) (hD : D≠0)
    (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (hJ : ∀B,(∑j∈Js B,w j.val) ≤ 3/5000)
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Z ξ Cz Ct target : ℝ)
    (hdiag : secondDiagonalCost s (by norm_num) cover G Js η₁ η₂ τ t K Z Cz Ct ≤ target/4)
    (hfixed : partSideCost true s cover G Js η₁ η₂ τ χ₀ Q m t K Z ξ ≤ 3*target/8)
    (hregular : partSideCost false s cover G Js η₁ η₂ τ χ₀ Q m t K Z ξ ≤ 3*target/8) :
    SecondSidePrice s cover w C D hD G η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct target := by
  refine ⟨Js,hJ,?_⟩
  rw [secondSideCost_split]
  apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
  linarith

#print axioms secondSideCost_split
#print axioms secondSidePrice_of_parts
end
end QRH.Cycle092.PairedRetainedBudget
