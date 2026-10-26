/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalRoundedPosition

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Cycle153
noncomputable section
open Cycle63.Optimization

/-- Convert the paid global-unit source inequalities to the exact local
ledger at the continuing state. The frozen dual margins are uniform in
the global unit; U≤1 can only improve them after normalization. -/
theorem normalized_roundedPosition_facts
    (S : RegionalStage) {g eta U B n₁ n₂ z A capA a : ℝ}
    (hg : 0<g) (heta : 0<eta) (hgrid : 500*g ≤ eta) (hetacap : eta ≤ 1/1000)
    (hU : 0<U) (hU1 : U ≤ 1)
    (hK : amplifierRatio S.price S.intercept S.q ≤ 7) (hlam : S.lam ≤ 5)
    (hz : 0 ≤ z) (hzcap : z ≤ (1-eta)*U) (hB : B ≤ (1-eta)*U)
    (hplane : n₁+n₂+S.lam*z ≤ B)
    (hA : A=n₁+n₂+z) (hcap : capA=B-(S.lam-1)*z) (hcap0 : 0 ≤ capA)
    (ha : a/U=planeAmplifier S.price S.intercept S.q S.lam (B/U) (z/U))
    (hbalanced : |n₁-n₂| ≤ 6*slotPrice*z+U/100)
    (hactive : 0<A+(6*slotPrice-1)*z-U)
    (hamp : eta ≤ a)
    (hfirst : eta ≤ (S.primeFraction-1/2)*a-
      (B-U+(6*slotPrice-S.lam)*z)/6-lowReserveAt S.price S.intercept S.q*U)
    (hshort : eta ≤ (A-(1+6*slotPrice)*z-U/100)/2)
    (hcomparison : eta ≤ (A-(11/2)*z-U/100)/2)
    (hfixed0 : eta ≤ U-capA-4*a-U/50)
    (hfixed1 : eta ≤ U-capA-4*a-U/50-
      (2/3)*((51/200)*U-A/2+(1+6*slotPrice)*z/2))
    (hfixed2 : eta ≤ U-capA-4*a-U/50-
      (2/3)*((51/200)*U-A/2+(11/4)*z))
    (hexception0 : eta ≤ U-capA-(9/2)*a-U/50)
    (hexception1 : eta ≤ U-capA-(9/2)*a-U/50-
      (2/3)*((51/200)*U-A/2+(1+6*slotPrice)*z/2))
    (hexception2 : eta ≤ U-capA-(9/2)*a-U/50-
      (2/3)*((51/200)*U-A/2+(11/4)*z))
    (hzero : eta ≤ U-capA-6*a-(1/380+S.zeroSaving)*U) :
    (roundedPosition g (B/U) (n₁/U) (n₂/U) (z/U)).Facts S := by
  have hUne : U≠0 := ne_of_gt hU
  have normalize {e E : ℝ} (h : eta ≤ E) (he : e*U=E) : eta ≤ e := by
    apply le_of_mul_le_mul_right ?_ hU
    calc eta*U ≤ eta := mul_le_of_le_one_right heta.le hU1
      _ ≤ E := h
      _ = e*U := he.symm
  apply roundedPosition_facts S (A:=A/U) (a:=a/U) hg heta hgrid hetacap hK hlam
    (div_nonneg hz hU.le) ((div_le_iff₀ hU).mpr hzcap) ((div_le_iff₀ hU).mpr hB)
  · simpa only [add_div,mul_div_assoc] using div_le_div_of_nonneg_right hplane hU.le
  · rw [hA]
    simp only [add_div]
  · exact ha
  · rw [←sub_div,abs_div,abs_of_pos hU]
    apply (div_le_iff₀ hU).mpr
    have he : (6*slotPrice*(z/U)+1/100)*U=6*slotPrice*z+U/100 := by
      field_simp [hUne]
      <;> ring
    rw [he]
    exact hbalanced
  · have he : (n₁/U+n₂/U+6*slotPrice*(z/U)-1)*U=A+(6*slotPrice-1)*z-U := by
      field_simp [hUne]
      <;> nlinarith only [hA]
    have hp : 0<(n₁/U+n₂/U+6*slotPrice*(z/U)-1)*U := by rw [he];exact hactive
    exact (mul_pos_iff_of_pos_right hU).mp hp
  · exact normalize hamp (div_mul_cancel₀ a hUne)
  · apply normalize hfirst
    field_simp [hUne]
    <;> ring
  · apply normalize hshort
    field_simp [hUne]
    <;> ring
  · apply normalize hcomparison
    field_simp [hUne]
    <;> ring
  · apply normalize hfixed0
    field_simp [hUne]
    <;> nlinarith only [hcap]
  · apply normalize hfixed1
    field_simp [hUne]
    <;> nlinarith only [hcap]
  · apply normalize hfixed2
    field_simp [hUne]
    <;> nlinarith only [hcap]
  · apply normalize hexception0
    field_simp [hUne]
    <;> nlinarith only [hcap]
  · apply normalize hexception1
    field_simp [hUne]
    <;> nlinarith only [hcap]
  · apply normalize hexception2
    field_simp [hUne]
    <;> nlinarith only [hcap]
  · apply normalize hzero
    field_simp [hUne]
    <;> nlinarith only [hcap]
  · have he : (B/U-(S.lam-1)*(z/U))*U=capA := by
      field_simp [hUne]
      <;> nlinarith only [hcap]
    apply (mul_nonneg_iff_of_pos_right hU).mp
    rw [he]
    exact hcap0

end
end Cycle153
#print axioms Cycle153.normalized_roundedPosition_facts
