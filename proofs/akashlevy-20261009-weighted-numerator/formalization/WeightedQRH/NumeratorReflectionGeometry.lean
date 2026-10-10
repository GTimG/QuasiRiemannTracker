import WeightedQRH.NumeratorDamping
import OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength

noncomputable section
namespace WeightedQRH.Numerator

/-- The combined primitive/redundant conductor controls the coefficient dilation. -/
def coefficientDilation (U C conductor N : ℝ) : ℝ := max 1 (conductor*N/(C*U))

theorem coefficientDilation_le_norm (U C conductor N : ℝ)
    (hU : 0 < U) (hC : 0 < C) (hconductor : conductor ≤ C*U)
    (hN : 1 ≤ N) : coefficientDilation U C conductor N ≤ N := by
  unfold coefficientDilation
  apply max_le hN
  apply (div_le_iff₀ (mul_pos hC hU)).mpr
  nlinarith

theorem coefficientDilation_ge_one (U C conductor N : ℝ) :
    1 ≤ coefficientDilation U C conductor N := le_max_left _ _

/-- Exhausting reflected prime capacity forces the original sum to be short.
This gives an optional direct branch. The stronger certified ZeroAt endpoint also
controls bounded reflected lengths without a two-plain-length capacity condition. -/
theorem original_short_of_capacity_exhausted (U C conductor N y : ℝ)
    (hU : 1 < U) (hC : 0 < C) (hconductor : conductor ≤ C*U)
    (hN : 1 ≤ N)
    (hexhausted : U^(y-1/2) ≤ coefficientDilation U C conductor N) :
    0 < U^y/N ∧ U^y/N ≤ U^(1/2:ℝ) := by
  have hUp : 0 < U := zero_lt_one.trans hU
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hT := coefficientDilation_le_norm U C conductor N hUp hC hconductor hN
  refine ⟨div_pos (Real.rpow_pos_of_pos hUp _) hNp,?_⟩
  apply (div_le_iff₀ hNp).mpr
  have h := mul_le_mul_of_nonneg_left (hexhausted.trans hT)
    (Real.rpow_nonneg hUp.le (1/2:ℝ))
  calc
    U^y = U^(1/2:ℝ)*U^(y-1/2) := by rw [←Real.rpow_add hUp];congr 1;ring
    _ ≤ U^(1/2:ℝ)*N := h

theorem exhausted_capacity_zero (y v : ℝ) (hv : y-1/2 ≤ v) :
    selectedCapacity ((2*y-1)/(9/2)) v = 0 := by
  unfold selectedCapacity
  apply max_eq_left
  linarith

/-- On the reflection branch, the allowed prime capacity exactly fills width one. -/
theorem reflected_capacity_eq (y v : ℝ) (hv : v ≤ y-1/2) :
    2*(1-y+v)+(9/2)*selectedCapacity ((2*y-1)/(9/2)) v = 1 := by
  unfold selectedCapacity
  rw [max_eq_right (by linarith : 0 ≤ (2*y-1)/(9/2)-4*v/9)]
  ring

/-- The short branch has the same saturated selected-prime saving after damping. -/
theorem original_branch_damping (delta q y v : ℝ)
    (hd : 0 ≤ delta) (hq : 0 ≤ q) (hqd : q ≤ delta/2)
    (hv : 0 ≤ v) (hexhausted : y-1/2 ≤ v) :
    -delta*v/4 ≤ -q*((2*y-1)/(9/2))/2 := by
  have h := capacity_damping_weak delta q ((2*y-1)/(9/2)) v hd hq hqd hv
  rw [exhausted_capacity_zero y v hexhausted] at h
  simpa using h

end WeightedQRH.Numerator
