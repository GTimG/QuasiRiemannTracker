/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.AuxHighTemplates
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceStepAffine
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open HighTemplates AuxHighTemplates

private theorem quadratic_hasDerivAt (a b c z : ℝ) :
 HasDerivAt (fun x : ℝ => a+b*x+c*x^2) (b+2*c*z) z := by
 have hh := ((hasDerivAt_const z a).add ((hasDerivAt_id z).const_mul b)).add
   (((hasDerivAt_id z).pow 2).const_mul c)
 convert hh using 1 <;> (try funext x) <;> simp only [id_eq,Pi.add_apply,Pi.mul_apply,Pi.pow_apply] <;> ring

theorem rayCapD_hasDerivAt (B L c r s ν z : ℝ) :
 HasDerivAt (rayCapD B L c 0 r s ν) (rayCapDz B L c 0 r s ν z) z := by
 convert quadratic_hasDerivAt (5/2-ν) (-5/12*r-ν*r/2) 0 z using 1
 · funext x; unfold rayCapD; ring
 · unfold rayCapDz; ring

theorem rayBudgetD_hasDerivAt (B L c r s ν z : ℝ) :
 HasDerivAt (rayBudgetD B L c 0 r s ν) (rayBudgetDz B L c 0 r s ν z) z := by
 convert quadratic_hasDerivAt (5/2-ν) (-5/12*r-5/3*r/L-ν*r/2) (ν*r^2/L) z using 1
 · funext x; unfold rayBudgetD; ring
 · unfold rayBudgetDz; ring

theorem rayCapK_hasDerivAt (B L c r s ν z : ℝ) :
 HasDerivAt (rayCapK B L c 0 r s ν) (rayCapKz B L c 0 r s ν z) z := by
 convert quadratic_hasDerivAt (5/3*ν) (5/6*ν*c*r-ν^2*r-ν^2*c*r)
   (-5/12*ν*c*r^2+ν^2*c*r^2/2) z using 1
 · funext x; unfold rayCapK; ring
 · unfold rayCapKz; ring

theorem rayBudgetK_hasDerivAt (B L c r s ν z : ℝ) :
 HasDerivAt (rayBudgetK B L c 0 r s ν) (rayBudgetKz B L c 0 r s ν z) z := by
 convert quadratic_hasDerivAt (5/3*ν) (-5/3*ν*r/L+5/6*ν*B*r/L-ν^2*r-ν^2*B*r/L)
   (-5/12*ν*B*r^2/L+ν^2*r^2/L+ν^2*B*r^2/(2*L)) z using 1
 · funext x; unfold rayBudgetK; ring
 · unfold rayBudgetKz; ring

theorem rayCapD_eq_den (B L c r s ν z : ℝ) :
 rayCapD B L c 0 r s ν z=rayCapDen ν r z := by
 unfold rayCapD rayCapDen crossingDen
 ring

theorem rayBudgetD_eq_den (B L c r s ν z : ℝ) :
 rayBudgetD B L c 0 r s ν z=rayBudgetDen L ν r z := by
 unfold rayBudgetD rayBudgetDen crossingDen
 ring

theorem rayCapK_eq_save (B L c r s ν z : ℝ) :
 rayCapK B L c 0 r s ν z=rayCapSave c ν r z := by
 unfold rayCapK rayCapSave rayCapDen crossingDen
 ring

theorem rayBudgetK_eq_save (B L c r s ν z : ℝ) :
 rayBudgetK B L c 0 r s ν z=rayBudgetSave B L ν r z := by
 unfold rayBudgetK rayBudgetSave rayBudgetDen crossingDen
 ring


/-- Rational polynomial reserve, divided only by its positive denominator. -/
theorem rational_high_of_polynomial {K D ν r H P S u rho : ℝ}
 (hD : 0 < D)
 (hp : 0 ≤ H*K-ν*P*D-(r*ν)*S*D+u*D-rho*D) :
 ν*P+((1-K/D)-1)*H+(r*ν)*S ≤ u-rho := by
 have hh : (ν*P+((1-K/D)-1)*H+(r*ν)*S)*D ≤ (u-rho)*D := by
  field_simp [hD.ne'] at *
  nlinarith only [hp]
 exact (mul_le_mul_iff_left₀ hD).mp hh

theorem rayCap_den_pos {B L c r s ν z : ℝ}
 (hν : 0 < ν) (hνhi : ν ≤ 3/4) (hr : r ≤ 1) (hr0 : 0 ≤ r)
 (hz : z ∈ Set.Icc (0:ℝ) 1) :
 0 < rayCapD B L c 0 r s ν z := by
 rw [rayCapD_eq_den]
 apply branch_den_pos hν hνhi
 · nlinarith [hz.1,hz.2,mul_nonneg hr0 hz.1,mul_nonneg (sub_nonneg.mpr hr) hz.1]
 · norm_num

theorem rayBudget_den_pos {B L c r s ν z : ℝ}
 (hν : 0 < ν) (hνhi : ν ≤ 3/4) (hr : r ≤ 1) (hr0 : 0 ≤ r)
 (hL : 3/2 ≤ L) (hz : z ∈ Set.Icc (0:ℝ) 1) :
 0 < rayBudgetD B L c 0 r s ν z := by
 have hp : r*z/2 ≤ 1/2 := by
  nlinarith [hz.1,hz.2,mul_nonneg hr0 hz.1,mul_nonneg (sub_nonneg.mpr hr) hz.1]
 have hp0 : 0 ≤ r*z/2 := by exact div_nonneg (mul_nonneg hr0 hz.1) (by norm_num)
 have hA := (budget_coefficients (B:=0) (by norm_num) (by norm_num) hL hp0 hp).1
 rw [rayBudgetD_eq_den]
 apply branch_den_pos hν hνhi hp
 convert lt_of_lt_of_le (by norm_num : (0:ℝ)<2/3) hA using 1 <;> ring

/-- The amplitude derivative is transported to the actual common width. -/
theorem rayCap_weighted_monotone {B L c r s ν H S : ℝ}
 (hν : 0 < ν) (hνhi : ν ≤ 3/4) (hr : 0 < r) (hrhi : r ≤ 1)
 (hH : 0 ≤ H) (hS : s*H ≤ S)
 (hamp : ∀ z ∈ Set.Icc (0:ℝ) 1, 0 ≤ rayCapAmp B L c 0 r s ν z) :
 MonotoneOn (weightedRatio (rayCapK B L c 0 r s ν)
   (rayCapD B L c 0 r s ν) H (r*ν*S)) (Set.Icc (0:ℝ) 1) := by
 apply weightedRatio_monotoneOn
   (fun z _ => rayCapK_hasDerivAt B L c r s ν z)
   (fun z _ => rayCapD_hasDerivAt B L c r s ν z)
   (fun z hz => rayCap_den_pos hν hνhi hrhi hr.le hz)
 intro z hz
 have hp := mul_nonneg hν.le (hamp z hz)
 rw [rayCap_amplitude_identity] at hp
 have hh := derivative_reserve_transport (a:=r*ν) (by positivity) hH hS hp
 convert hh using 1 <;> ring

theorem rayBudget_weighted_monotone {B L c r s ν H S : ℝ}
 (hν : 0 < ν) (hνhi : ν ≤ 3/4) (hr : 0 < r) (hrhi : r ≤ 1)
 (hL : 3/2 ≤ L) (hH : 0 ≤ H) (hS : s*H ≤ S)
 (hamp : ∀ z ∈ Set.Icc (0:ℝ) 1, 0 ≤ rayBudgetAmp B L c 0 r s ν z) :
 MonotoneOn (weightedRatio (rayBudgetK B L c 0 r s ν)
   (rayBudgetD B L c 0 r s ν) H (r*ν*S)) (Set.Icc (0:ℝ) 1) := by
 apply weightedRatio_monotoneOn
   (fun z _ => rayBudgetK_hasDerivAt B L c r s ν z)
   (fun z _ => rayBudgetD_hasDerivAt B L c r s ν z)
   (fun z hz => rayBudget_den_pos hν hνhi hrhi hr.le hL hz)
 intro z hz
 have hp := mul_nonneg hν.le (hamp z hz)
 rw [rayBudget_amplitude_identity] at hp
 have hh := derivative_reserve_transport (a:=r*ν) (by positivity) hH hS hp
 convert hh using 1 <;> ring


theorem affine_endpoint_upper {a b lo hi bound w : ℝ}
 (hlo : a+b*lo ≤ bound) (hhi : a+b*hi ≤ bound)
 (hw : w ∈ Set.Icc lo hi) : a+b*w ≤ bound := by
 by_cases hb : 0 ≤ b
 · have hh := mul_le_mul_of_nonneg_left hw.2 hb
   linarith
 · have hh := mul_le_mul_of_nonpos_left hw.1 (by linarith : b ≤ 0)
   linarith

theorem selected_rate_eq_saving {ν r : ℝ} (hD : selectedDen 0 r ν ≠ 0) (ha : r*ν ≤ ν) :
 detectorRate ν (r*ν)=1-selectedSave 0 r ν/selectedDen 0 r ν := by
 have hJ : witnessDen ν (r*ν) ≠ 0 := by
  convert hD using 1 <;> unfold witnessDen selectedDen <;> ring
 simp only [detectorRate,if_pos ha]
 unfold jointCountExponent selectedSave
 field_simp [hD,hJ]
 unfold witnessDen selectedDen
 ring

end
end Qrh.JointDetector.RepeatedMarks
