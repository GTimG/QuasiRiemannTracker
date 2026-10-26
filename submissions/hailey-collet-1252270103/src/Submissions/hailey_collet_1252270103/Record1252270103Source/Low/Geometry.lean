/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Generalized C28 reference geometry. Clipped-length API: Hailey Collet's
Cycle61.FirstBranches, using the OpenAI/math natural source convention. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.FirstBranches.Geometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Low
noncomputable section
open HeckeFamily CenteredMomentEnergyBands Cycle61FirstGeometry

/-- C28 uses the whole range of short lengths, including subunit scales. -/
theorem clipped_short_capacity (Z M width short along slots r cap K xi : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hwidth : M ≤ width)
    (hr : 0 ≤ r) (hcap : 0 ≤ cap) (hK : 0 ≤ K)
    (hshort : short ≤ r) (hslots : slots ≤ cap)
    (hbudget : r + K*cap ≤ 49*M/100)
    (hlong : M/2 ≤ along) (hxi : 0 ≤ xi) (hpad : xi ≤ M/100) :
    max 0 (width-along+xi) + length Z (Z^short) + K*slots ≤ width := by
  rw [length_rpow Z short hZ]
  have hs : max 0 short ≤ r := max_le hr hshort
  have hw : max 0 (width-along+xi) ≤ width-M/2+xi :=
    max_le (by linarith) (by linarith)
  have hk := mul_le_mul_of_nonneg_left hslots hK
  linarith

/-- On the other side of the half-width cut, the natural capacity is at most .99M. -/
theorem direct_short_capacity (Z M width short along slots r cap K : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hwidth : M ≤ width)
    (hr : 0 ≤ r) (hK : 0 ≤ K) (hshort : short ≤ r)
    (hslots : slots ≤ cap) (hbudget : r + K*cap ≤ 49*M/100)
    (hlong : along ≤ M/2) :
    length Z (Z^along) + length Z (Z^short) + K*slots ≤ width := by
  rw [length_rpow Z short hZ, length_rpow Z along hZ]
  have hs : max 0 short ≤ r := max_le hr hshort
  have hl : max 0 along ≤ M/2 := max_le (by linarith) hlong
  have hk := mul_le_mul_of_nonneg_left hslots hK
  linarith

/-- Exact equal-product reference for any real reference length. -/
theorem reference_product (Z n₁ n₂ r : ℝ) (hZ : 0 < Z) :
    Z^r * Z^(n₁+n₂-r) = Z^n₁ * Z^n₂ := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

/-- Both reference factors are at least the reference when both originals are. -/
theorem reference_floor (n₁ n₂ r : ℝ) (h₁ : r ≤ n₁) (h₂ : r ≤ n₂) :
    r ≤ n₁+n₂-r := by linarith

/-- The manuscript's adjustable reference pays the complete slot budget exactly. -/
theorem reference_budget (K b M : ℝ) :
    (49/100-K*b)*M + K*(b*M) = 49*M/100 := by ring

end
end OAI.SevenEighths.Record1252270103Low
#print axioms OAI.SevenEighths.Record1252270103Low.clipped_short_capacity
#print axioms OAI.SevenEighths.Record1252270103Low.direct_short_capacity
#print axioms OAI.SevenEighths.Record1252270103Low.reference_product
#print axioms OAI.SevenEighths.Record1252270103Low.reference_budget
