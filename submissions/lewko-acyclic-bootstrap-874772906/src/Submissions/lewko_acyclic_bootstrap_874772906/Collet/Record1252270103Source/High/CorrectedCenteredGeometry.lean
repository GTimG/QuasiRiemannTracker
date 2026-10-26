/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The exact cofactor children retain positive raw scales and equal products. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CorrectedCenteredRows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CorrectedCentered
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily QRH.Record1252270103Low QRH.Record1252270103Restoration
open QRH.Record1252270103KernelMass OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O

lemma frozenProfile_nonzero_iff (W₁ W₂:ℝ→ℂ)(A₁ A₂:Ideal O)(X₁ X₂ Y₁ Y₂:ℝ)(n:IdealPair) :
    frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0 ↔
      ordinarySmallHole (A₁*n.1) (A₂*n.2) ∧ centeredProfile W₁ W₂ X₁ X₂ Y₁ Y₂ n≠0 := by
  by_cases h:ordinarySmallHole (A₁*n.1) (A₂*n.2) <;>
    simp [frozenProfile,ordinaryHoleIndicator,h]

lemma extracted_centered_scales (d:IdealPair)(hd:GoodPair d)(X₁ X₂ Y₁ Y₂ T:ℝ)
    (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)
    (hX:X₁*X₂=T)(hY:Y₁*Y₂=T) :
    0<X₁/d.1.absNorm ∧ 0<X₂/d.2.absNorm ∧ 0<Y₁/d.1.absNorm ∧ 0<Y₂/d.2.absNorm ∧
    0<T/pairNorm d ∧
    (X₁/d.1.absNorm)*(X₂/d.2.absNorm)=T/pairNorm d ∧
    (Y₁/d.1.absNorm)*(Y₂/d.2.absNorm)=T/pairNorm d := by
  have h₁:0<(d.1.absNorm:ℝ):=lt_of_lt_of_le zero_lt_one (ideal_norm_one_le hd.1)
  have h₂:0<(d.2.absNorm:ℝ):=lt_of_lt_of_le zero_lt_one (ideal_norm_one_le hd.2.1)
  refine ⟨div_pos hX₁ h₁,div_pos hX₂ h₂,div_pos hY₁ h₁,div_pos hY₂ h₂,
    div_pos (hX ▸ mul_pos hX₁ hX₂) (pairNorm_pos hd.1 hd.2.1),?_,?_⟩
  · rw [div_mul_div_comm,hX];rfl
  · rw [div_mul_div_comm,hY];rfl

end
end QRH.Record1252270103Source.High.CorrectedCentered
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.frozenProfile_nonzero_iff
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.extracted_centered_scales
