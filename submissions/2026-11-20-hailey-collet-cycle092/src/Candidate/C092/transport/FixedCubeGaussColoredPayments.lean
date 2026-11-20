/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussPaymentLift
import Candidate.C092.transport.FixedCubeGaussColoredPrimary
import Candidate.C092.transport.FixedAllocationWeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentDivisorAllocation
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussColoredPayments_27b0cc4b4160ccdc_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- The extracted colors equal their actual full ordinary-prefix values,
including zeros at either ramified common or primary allocation. -/
lemma primaryPrefix_colors (r : Source ι a b) (ω₁ ω₂ : Character) (G L : Id)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L) :
    (idealCoeff ω₁ r.d.1*idealCoeff ω₂ r.d.2)*
      TwistedRawSource.ordinaryColor (idealCoeff ω₁) (idealCoeff ω₂) B.val*
      TwistedRawSource.ordinaryColor (idealCoeff ω₁) (idealCoeff ω₂) E.val=
    idealCoeff ω₁ (primaryOrdinaryPrefix r G L B E).1*
      idealCoeff ω₂ (primaryOrdinaryPrefix r G L B E).2 := by
  unfold TwistedRawSource.ordinaryColor primaryOrdinaryPrefix commonLiveD
  simp only [Prod.fst,Prod.snd,map_mul]
  ring

/-- Instantiates the controller's squared allocation weight with the literal
native common tuple and the full primary tuple extended by units. -/
theorem native_primary_squared_weight (r : Source ι a b) (G L : Id) (hG : G≠0) (hL : Squarefree L)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L)
    (aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (hactive : allocationTerm L Finset.univ E.val aL≠0) (Lf : ℝ) :
    let pd : ℝ:=(r.d.1.absNorm:ℝ)*r.d.2.absNorm
    let q : ℝ:=pd*(∏j,((B.val j*liftPrimaryTuple B.val E.val j).absNorm:ℝ))
    q⁻¹^2*(max 1 (Lf/q))^(-(6/5):ℝ)≤(pd*G.absNorm*L.absNorm*max 1 Lf)⁻¹ := by
  have hd : L∣∏j,liftPrimaryTuple B.val E.val j := by
    change L∣finiteTupleProduct (liftPrimaryTuple B.val E.val)
    rw [liftPrimaryTuple_product]
    exact allocationTerm_ne_zero_divides L hL E.val aL hactive
  exact QRH.Cycle092.FixedAllocationWeight.actual_squared_weight B.val
    (liftPrimaryTuple B.val E.val) r.d.1 r.d.2 G L r.hd.1 r.hd.2 hG hL.ne_zero
    (liftPrimaryTuple_nonzero B.val E.val (fullPrimaryAlloc_ne r G B L E))
    (commonAlloc_product r G B) hd Lf

#print axioms primaryPrefix_colors
#print axioms native_primary_squared_weight
end
end QRH.Cycle092.FixedCubeGauss
