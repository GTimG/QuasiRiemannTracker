/- Copyright (c) 2026 Hailey Collet; source specialization (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildJoinedRow
import Candidate.Research.RecursiveAffine.ActualRecordRebase

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63InitialMass Cycle63Moment CanonicalQuadraticSieve Cycle63FinalCapacity CenteredMomentSectorLocalization

/-- The literal joined LOW-source return coefficient. `oldPaymentExponent`
is the same shell/normalizer exponent used by the actual native source;
`ownSecondNorm` is retained reciprocally. The native returned count is
absolute, so no additional factor `Z^Mrow` belongs in this expression. -/
def physicalLowReturnWeight
    (Z loss amp oldPaymentExponent oldEnergyExponent ownSecondNorm
      slotLoss q deletion mesh : ℝ) : ℝ :=
  Z^(loss+amp+oldPaymentExponent-oldEnergyExponent) / ownSecondNorm *
    Z^(slotLoss+q*(deletion+mesh))

/-- The actual own-second ideal and the actual four-coordinate row give
exactly the outside exponent used by native prefix counting. The formula is
valid at every explicit regional junction q and every actual deletion. It
retains the reciprocal own-second norm rather than hiding it in a cap. -/
theorem physical_low_return_weight_eq
    (reflected second left : Bool) (first label : FirstSourceLabel)
    (Z Mrow A amp xi reserve eps unit common pad loss epsV normCap shellLoss
      slotLoss q deletion mesh : ℝ)
    (hZ : 1 < Z) (hC : Supported label.1.1) (hD : Supported label.1.2) :
    let oldPaymentExponent := lowGeometryExponent reflected Z A first +
      (common+pad) + (unit-Mrow) + epsV + normCap*shellLoss
    let oldEnergyExponent := secondNominal unit Z amp (frequencyLoss Z 32 xi+reserve)
      (if reflected then first.1.2 else first.1.1)
      (if reflected then first.1.1 else first.1.2)
      label.1.1 label.1.2 label.2.val + amp+common
    let ownSecondNorm := ((if second then label.1.2 else label.1.1).absNorm : ℝ)
    let E0 := loss+amp+epsV+normCap*shellLoss+pad+slotLoss
    physicalLowReturnWeight Z loss amp oldPaymentExponent oldEnergyExponent ownSecondNorm
      slotLoss q deletion mesh =
      Z^(E0+actualHighCoordinates reflected left second first label.1.1 label.1.2 label.2.val
        Z Mrow A amp xi reserve eps 0+q*(deletion+mesh)) := by
  dsimp only
  unfold physicalLowReturnWeight
  apply returned_weight_eq hZ (second_norm_pos second hC hD) rfl
  exact returned_row_exponent reflected second left first label Z Mrow A amp xi reserve eps
    unit (common+pad) common pad loss epsV normCap shellLoss slotLoss (q*(deletion+mesh))
    (loss+amp+epsV+normCap*shellLoss+pad+slotLoss)
    (lowGeometryExponent reflected Z A first + (common+pad)+(unit-Mrow)+epsV+normCap*shellLoss)
    (secondNominal unit Z amp (frequencyLoss Z 32 xi+reserve)
      (if reflected then first.1.2 else first.1.1)
      (if reflected then first.1.1 else first.1.2) label.1.1 label.1.2 label.2.val+amp+common)
    rfl rfl rfl rfl

/-- Appending one genuine source edge multiplies the existing outside
weight, while the descendant record is only rebased. The count's current
energy scale is not inserted as a second weight. -/
theorem source_edge_weight_value {Base : Type} {base : Base → Character}
    {eta : Character} {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Z B T U : ℝ} {left : Bool} {v : O} {units : FirstSourceLabel → O}
    (hZ : 0 < Z)
    (R : SecondStepHighCount M H hH base eta (Z^U) B T left v units)
    (outside edgeWeight : ℝ) :
    (outside*edgeWeight)*(rebaseHighRecord M H hH hZ R).value =
      outside*(edgeWeight*R.value) := by
  rw [rebaseHighRecord_value hZ R]
  ring

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.physical_low_return_weight_eq
#print axioms OAI.SevenEighths.Cycle153RegionalLow.source_edge_weight_value
