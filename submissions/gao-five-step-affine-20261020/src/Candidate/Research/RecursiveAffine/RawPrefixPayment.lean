/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualCoordinateLift

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section

/-- The raw AtState factor is retained in the parent exponent. It cancels
only upon forming the parent's normalized Pays expression. Global prefix
multipliers are kept relative to the parent, so this lemma can be iterated
beyond the original first physical prefix.

The child premise is the aggregate path payment at the actual child state;
it is initialized by the native own-HIGH record and then propagated with
this same theorem. No assertion is made here that the actual recursive
source family or its scalar edge envelopes has already been constructed. -/
theorem raw_physical_prefix_attachment
    (rho delta cost X0 X1 X2 X3 unit parentScale A amp small Gamma
      childScale parentLog childLog childExponent childMissing childRow
      childLength childAmp childLoss D extraVolume scalePad volumePad q fees : ℝ)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdelta : 0 ≤ delta)
    (hunit : parentScale ≤ unit)
    (hparent : X0+X1+rho*X2+delta*X3 ≤
      small-(unit*(1-rho)-delta*A-amp*cost)-Gamma)
    (hchild : childExponent-childScale+childMissing+rho*(childRow-childLog) ≤
      childLoss-(childScale*(1-rho)-delta*childLength-childAmp*cost))
    (hscale : childScale+childLog-parentLog ≤ X2+scalePad)
    (hvolume : childLength ≤ X3-D-extraVolume+volumePad) :
    let rawParentExponent := parentScale+X0+q*D+childExponent+fees
    rawParentExponent-parentScale+(X1+childMissing)+rho*(childRow-parentLog) ≤
      small+childLoss+fees+rho*scalePad+delta*volumePad-
        (parentScale*(1-rho)-delta*A-(amp+childAmp)*cost)-
        (Gamma+delta*extraVolume+(delta-q)*D) := by
  dsimp only
  have hs := mul_le_mul_of_nonneg_left hscale hrho
  have hv := mul_le_mul_of_nonneg_left hvolume hdelta
  have hu := mul_le_mul_of_nonneg_right hunit (sub_nonneg.mpr hrho1)
  nlinarith only [hparent,hchild,hs,hv,hu]

/-- Exact outward scale-factor accounting before normalization. The
intermediate row scale is present in the raw exponent; no cancellation is
claimed at the level of the unnormalized count value. -/
theorem raw_source_edge_exponent
    (parentScale driverLoss amp loss epsV normCap shellLoss pad slotLoss X0 q D mesh childExponent : ℝ) :
    (parentScale+driverLoss-amp)+
      (loss+amp+epsV+normCap*shellLoss+pad+slotLoss+X0+q*(D+mesh))+childExponent =
    parentScale+X0+q*D+childExponent+
      (driverLoss+loss+epsV+normCap*shellLoss+pad+slotLoss+q*mesh) := by
  ring

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.raw_physical_prefix_attachment
#print axioms OAI.SevenEighths.Cycle153RegionalLow.raw_source_edge_exponent
