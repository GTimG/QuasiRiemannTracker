import Candidate.Uneven.CriticalAmplitude
import Candidate.Uneven.RoundedRowsBase

/- Original module: Candidate.Uneven.CriticalMargin. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Sil.Uneven.Critical

/-- Exact dependence on the proposed boundary, before any losses are chosen. -/
theorem critical_row_parameter_shift (a t h d p : ℝ) :
    t-criticalRow t h d p = a-criticalRow a h d p+
      (t-a)*(3+4*d*p+8*d*p/physicalLambda) := by
  unfold criticalRow physicalLambda
  ring

/-- Every larger boundary leaves a uniform positive margin on the critical
rectangle. The equality at the endpoint therefore causes no missing reserve. -/
theorem critical_rectangle_uniform_margin {t d p : ℝ}
    (ht : endpoint < t)
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    criticalRow t (criticalHeight criticalParameter) d p ≤
      t-3*(t-endpoint) := by
  have hb := endpoint_critical_rectangle hd hp
  have hdp : 0 ≤ d*p := mul_nonneg (by linarith only [hd.1])
    (by linarith only [hp.1])
  have hcoef : 3 ≤ 3+4*d*p+8*d*p/physicalLambda := by
    have hl : 0 < physicalLambda := by norm_num [physicalLambda]
    have h₁ : 0 ≤ 4*(d*p) := mul_nonneg (by norm_num) hdp
    have h₂ : 0 ≤ 8*(d*p)/physicalLambda := div_nonneg
      (mul_nonneg (by norm_num) hdp) hl.le
    simp only [mul_assoc]
    linarith only [h₁,h₂]
  have hm := mul_le_mul_of_nonneg_left hcoef (sub_nonneg.mpr ht.le)
  have hi := critical_row_parameter_shift endpoint t
    (criticalHeight criticalParameter) d p
  linarith only [hb,hm,hi]


end Sil.Uneven.Critical
end

/- Original module: Candidate.Uneven.CriticalRounded. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Sil.Uneven.Critical

def roundedHeight : ℝ :=
  797070601673337477249729489432/1000000000000000000000000000000
def roundedPadding : ℝ := 1/10000000000000000
def roundedReserve : ℝ := 1/20000000000000

theorem critical_product_bounds {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 ≤ d*p ∧ d*p ≤ 1 := by
  have hd0 : 0 ≤ d := by linarith only [hd.1]
  have hp0 : 0 ≤ p := by linarith only [hp.1]
  refine ⟨mul_nonneg hd0 hp0,?_⟩
  exact (mul_le_mul hd.2 hp.2 hp0 (by norm_num)).trans (by norm_num)

theorem critical_count_bounds {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 ≤ countNumerator d p/countDenominator d p ∧
      countNumerator d p/countDenominator d p ≤ 1 := by
  have hJ := count_denominator_pos hd hp
  have hd0 : 0 ≤ d := by linarith only [hd.1]
  have hd1 : 0 ≤ 1-d := by linarith only [hd.2]
  have hdt : 0 ≤ 5/6-d := by linarith only [hd.2]
  have hp0 : 0 ≤ p := by linarith only [hp.1]
  have hp1 : 0 ≤ 1-p := by linarith only [hp.2]
  let C := 1-2*p*countB/countLambda
  let A := 2-4*p/countLambda
  let D := 3-p-4*p/countLambda
  have hC : 0 ≤ C ∧ C ≤ 1 := by
    dsimp [C,countB,countLambda]
    constructor <;> linarith only [hp0,hp.2]
  have hA : 0 ≤ A := by dsimp [A,countLambda]; linarith only [hp.2]
  have hD : 1-p ≤ D := by dsimp [D,countLambda]; linarith only [hp.2]
  have hsmall : (5/6-d)*(1-p)*C ≤ countDenominator d p := by
    have h₁ := mul_le_mul_of_nonneg_left hC.2 hp1
    have h₂ := mul_le_mul_of_nonneg_left
      ((by simpa only [mul_one] using h₁ : (1-p)*C ≤ 1-p).trans hD) hdt
    have h₃ := mul_nonneg (mul_nonneg hd0 hp1) hA
    change 0 ≤ d*(1-p)*(2-4*p/countLambda) at h₃
    change (5/6-d)*((1-p)*C) ≤ (5/6-d)*(3-p-4*p/countLambda) at h₂
    unfold countDenominator
    nlinarith only [h₂,h₃]
  have hN : countNumerator d p = (1-d)*countDenominator d p+
      d*((5/6-d)*(1-p)*C) := by dsimp [countNumerator,C]; ring
  have hn0 : 0 ≤ countNumerator d p := by
    rw [hN]
    exact add_nonneg (mul_nonneg hd1 hJ.le)
      (mul_nonneg hd0 (mul_nonneg (mul_nonneg hdt hp1) hC.1))
  have hn1 : countNumerator d p ≤ countDenominator d p := by
    have hm := mul_le_mul_of_nonneg_left hsmall hd0
    rw [hN]
    nlinarith only [hm]
  exact ⟨div_nonneg hn0 hJ.le,(div_le_one hJ).mpr hn1⟩

theorem critical_height_shift (t h₀ h₁ d p : ℝ) :
    criticalRow t h₁ d p-criticalRow t h₀ d p =
      (h₁-h₀)*(-5/12-d*p*physicalB/(2*physicalLambda)+
        3/4*(countNumerator d p/countDenominator d p)) := by
  unfold criticalRow physicalLambda
  ring

theorem critical_height_coefficient_bound {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    |(-5/12-d*p*physicalB/(2*physicalLambda)+
        3/4*(countNumerator d p/countDenominator d p))| ≤ 2 := by
  have hx := critical_product_bounds hd hp
  have hr := critical_count_bounds hd hp
  have hb : 0 ≤ physicalB/(2*physicalLambda) ∧ physicalB/(2*physicalLambda) ≤ 1 := by
    norm_num [physicalB,physicalLambda]
  have h₀ := mul_nonneg hx.1 hb.1
  have h₁ := mul_le_mul hx.2 hb.2 hb.1 (by norm_num : (0:ℝ) ≤ 1)
  have he : d*p*physicalB/(2*physicalLambda)=d*p*(physicalB/(2*physicalLambda)) := by ring
  rw [he,abs_le]
  constructor <;> linarith only [h₀,h₁,hr.1,hr.2]

theorem rounded_height_close :
    |roundedHeight-criticalHeight criticalParameter| ≤
      1/100000000000000000000000000 := by
  have hl := critical_parameter_isolation.1
  have hu := critical_parameter_isolation.2
  norm_num [parameterLower,parameterUpper] at hl hu
  rw [abs_le]
  norm_num [roundedHeight,criticalHeight]
  constructor <;> linarith only [hl,hu]

theorem rounded_critical_margin {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    criticalRow submittedBound roundedHeight d p ≤
      submittedBound-1/10000000000000 := by
  have hm := critical_rectangle_uniform_margin endpoint_lt_submitted hd hp
  have hh : |criticalRow submittedBound roundedHeight d p-
      criticalRow submittedBound (criticalHeight criticalParameter) d p| ≤
        (1/100000000000000000000000000)*2 := by
    rw [critical_height_shift,abs_mul]
    exact mul_le_mul rounded_height_close (critical_height_coefficient_bound hd hp)
      (abs_nonneg _) (by norm_num)
  have he := endpoint_isolation.2
  have hgap : (1/20000000000000:ℝ) ≤ submittedBound-endpoint := by
    norm_num [upper] at he
    norm_num [submittedBound]
    linarith only [he]
  have hdiff := (abs_le.mp hh).2
  linarith only [hm,hgap,hdiff]

/-- The upper physical row with its strictly positive padding, on the linear
capacity branch. Its agreement with the actual min-capacity row is separate. -/
def paddedCriticalRow (t h pad d p : ℝ) : ℝ :=
  criticalRow t h d p+pad*(-9/100+d*p*(2-physicalB)/(2*physicalLambda)+
    3/4*(countNumerator d p/countDenominator d p))

theorem rounded_padded_critical_margin {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    paddedCriticalRow submittedBound roundedHeight roundedPadding d p ≤
      submittedBound-roundedReserve := by
  have hm := rounded_critical_margin hd hp
  have hx := critical_product_bounds hd hp
  have hr := critical_count_bounds hd hp
  have hb : 0 ≤ (2-physicalB)/(2*physicalLambda) ∧
      (2-physicalB)/(2*physicalLambda) ≤ 1 := by norm_num [physicalB,physicalLambda]
  have h₁ := mul_le_mul hx.2 hb.2 hb.1 (by norm_num : (0:ℝ) ≤ 1)
  have hc : -9/100+d*p*(2-physicalB)/(2*physicalLambda)+
      3/4*(countNumerator d p/countDenominator d p) ≤ 2 := by
    have he : d*p*(2-physicalB)/(2*physicalLambda)=d*p*((2-physicalB)/(2*physicalLambda)) := by ring
    rw [he]
    linarith only [h₁,hr.2]
  have hpad := mul_le_mul_of_nonneg_left hc (show 0 ≤ roundedPadding by norm_num [roundedPadding])
  unfold paddedCriticalRow
  norm_num [roundedPadding,roundedReserve] at hpad ⊢
  linarith only [hm,hpad]

end Sil.Uneven.Critical
end

/- Original module: Candidate.Uneven.RoundedCriticalBridge. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

/-- The actual minimum of the two physical-capacity branches. -/
def actualCapacity (r : ℕ) : ℝ :=
  if r ≤ 1 then min (rowHeight r) (2*y-rowHeight r)/(6*frozen_kappa)
  else min ((399999/10000000)*rowHeight r)
    ((2*y-(2-Critical.physicalB)*rowHeight r)/Critical.physicalLambda)

theorem row_capacity_eq_actual {r : ℕ} (hr : r ≤ 3) :
    rowCapacity r = actualCapacity r := by
  interval_cases r <;>
    norm_num [rowCapacity,actualCapacity,rowHeight,y,frozen_kappa,
      Critical.physicalB,Critical.physicalLambda,min_def]

theorem upper_row_eq_padded_critical (d p : ℝ) :
    row 3 7 d p = Critical.paddedCriticalRow submittedBound
      Critical.roundedHeight Critical.roundedPadding d p := by
  have hJ : denominator 7 d p = Critical.countDenominator d p := by
    norm_num [denominator,planeLambda,Critical.countDenominator,Critical.countLambda]
  have hN : numerator 7 d p = Critical.countNumerator d p := by
    unfold numerator Critical.countNumerator
    rw [hJ]
    norm_num [planeB,planeLambda,Critical.countB,Critical.countLambda]
  unfold row
  rw [hJ,hN]
  unfold base Critical.paddedCriticalRow Critical.criticalRow
  norm_num [rowHeight,rowCapacity,h,y,ell,submittedBound,
    Critical.roundedHeight,Critical.roundedPadding,Critical.physicalB,Critical.physicalLambda]
  ring

theorem upper_row_critical_margin {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    row 3 7 d p ≤ theta-1/20000000000000 := by
  rw [upper_row_eq_padded_critical]
  simpa only [theta,submittedBound,Critical.roundedReserve] using
    Critical.rounded_padded_critical_margin hd hp

end Sil.Uneven.RoundedRows
end
