/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The actual packed norm identities and both distinct first-side ledgers. -/
import Candidate.C092.transport.PairedRetainedBudgetScalar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
local instance (priority := 2000) pairedOrientationSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSecondHeightFamily
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.TwistedRawBall QRH.Cycle092.RawPairDiagonalBudget
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

/-- The two orientations use their own genuine packed elements and their
    own displayed side modulus; the resulting denominator is NC*ND on each. -/
theorem actual_packed_norms (η : Character) (C D : Id) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hcf : QRH.SilDensitySplit.CubeFree.Packet.CubeFreeCommon C D)
    (hcpC : commonPart C D=C) (hcpD : commonPart D C=D) (χ ζ : RayCharacter) :
    ((Ideal.span {QRH.SilDensitySplit.CubeFree.Packet.firstPacked C D hC E}).absNorm:ℝ)*D.absNorm ≤
      ((fixedPair η C D hC E χ (ζ⁻¹)).left.modulus.absNorm:ℝ)*C.absNorm ∧
    ((Ideal.span {QRH.SilDensitySplit.CubeFree.Packet.firstPackedRight C D hC E}).absNorm:ℝ)*C.absNorm ≤
      ((fixedPair η C D hC E χ (ζ⁻¹)).right.modulus.absNorm:ℝ)*D.absNorm := by
  exact ⟨packed_norm_left C D hC E hcf hcpC hcpD
      (fixedPair η C D hC E χ (ζ⁻¹)).left η (fixedPair η C D hC E χ (ζ⁻¹)).left_modulus,
    packed_norm_right C D hC E hcf hcpC hcpD
      (fixedPair η C D hC E χ (ζ⁻¹)).right η (fixedPair η C D hC E χ (ζ⁻¹)).right_modulus⟩

/-- Concrete finite ledgers for both actual ray orientations produce the
    original first-side price. No divisor or allocation is omitted here. -/
theorem physicalBalancedSidesQ_of_cost_shares
    (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s) (w : ι→ℝ)
    (η₁ η₂ η : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (KL KR A Z loss ξ Cz Ct : ℝ) (J : ℕ)
    (hleft : ∀χ ζ : RayCharacter,∀v : ℝ,
      let τ := (fixedPair η C D hC E χ (ζ⁻¹)).left
      let target := balancedBudget s τ C D A Z loss*(1+‖v‖)^(2*J)
      ∃Js : ∀B : actualAllocations (tuplePools s) C,Finset (liveIndices B.val),
        (∀B,(∑j∈Js B,w j.val) ≤ 3/5000) ∧
        secondDiagonalCost s (by norm_num) cover C Js η₁ η₂ τ v KL Z Cz Ct ≤ target/4 ∧
        partSideCost true s cover C Js η₁ η₂ τ χ₀ Q m v KL Z ξ ≤ 3*target/8 ∧
        partSideCost false s cover C Js η₁ η₂ τ χ₀ Q m v KL Z ξ ≤ 3*target/8)
    (hright : ∀χ ζ : RayCharacter,∀v : ℝ,
      let τ := (fixedPair η C D hC E χ (ζ⁻¹)).right
      let target := balancedBudget s τ D C A Z loss*(1+‖v‖)^(2*J)
      ∃Js : ∀B : actualAllocations (tuplePools s) D,Finset (liveIndices B.val),
        (∀B,(∑j∈Js B,w j.val) ≤ 3/5000) ∧
        secondDiagonalCost s (by norm_num) cover D Js η₁ η₂ τ v KR Z Cz Ct ≤ target/4 ∧
        partSideCost true s cover D Js η₁ η₂ τ χ₀ Q m v KR Z ξ ≤ 3*target/8 ∧
        partSideCost false s cover D Js η₁ η₂ τ χ₀ Q m v KR Z ξ ≤ 3*target/8) :
    PhysicalBalancedSidesQ s cover w η₁ η₂ η χ₀ Q m C D hC hD E KL KR A Z loss ξ Cz Ct J := by
  intro χ ζ v
  obtain ⟨JL,hJL,hdiagL,hfixedL,hregL⟩ := hleft χ ζ v
  obtain ⟨JR,hJR,hdiagR,hfixedR,hregR⟩ := hright χ ζ v
  exact ⟨secondSidePrice_of_parts s cover w C D C hD.1 JL hJL η₁ η₂
      (fixedPair η C D hC E χ (ζ⁻¹)).left χ₀ Q m v KL Z ξ Cz Ct _ hdiagL hfixedL hregL,
    secondSidePrice_of_parts s cover w C D D hD.1 JR hJR η₁ η₂
      (fixedPair η C D hC E χ (ζ⁻¹)).right χ₀ Q m v KR Z ξ Cz Ct _ hdiagR hfixedR hregR⟩

#print axioms actual_packed_norms
#print axioms physicalBalancedSidesQ_of_cost_shares
end
end QRH.Cycle092.PairedRetainedBudget
