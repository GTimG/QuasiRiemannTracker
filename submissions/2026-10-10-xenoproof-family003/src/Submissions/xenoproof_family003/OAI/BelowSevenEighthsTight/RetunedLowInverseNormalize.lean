import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedLowSourceScales
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedLowReflectionGeometry

/- Radial normalization of a supplied squared-energy bound. No analytic
   producer of that bound is assumed to have been constructed by this file. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.LowExtension
noncomputable section

lemma low_inverse_power_cancel (radial Z d α : ℝ) (hZ : 0<Z) :
    Z^(radial-2*d+α)*(Z^d)^2/Z^(radial:ℝ)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma low_inverse_sqrt_normalized (radial q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0<q) (hC : 0≤C) (_hB : 0≤B) (hZ : 0<Z) (hL : 0<L) (hH : 1≤H)
    (hE : 0≤E) (hEL : E≤C*H^n*Z^(radial-2*d+α)) (hLB : L≤B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^(radial:ℝ)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^(radial:ℝ)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^(radial-2*d+α))/(q*Z^(radial:ℝ)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^(radial-2*d+α))*L^2/(q*Z^(radial:ℝ)) := by field_simp
      _≤(C*H^n*Z^(radial-2*d+α))*(B*Z^d)^2/(q*Z^(radial:ℝ)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^(radial-2*d+α)*(Z^d)^2/Z^(radial:ℝ)) := by ring
      _=_ := by rw [low_inverse_power_cancel radial Z d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α)=Z^(α/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)


theorem low_inverse_sqrt_with_decay (total radial q C B Z L d α H E : ℝ) (n : ℕ)
    (htotal : total≤1/5) (hd : 0≤d)
    (hq : 0<q) (hC : 0≤C) (hB : 0≤B) (hZ : 1≤Z) (hL : 0<L) (hH : 1≤H)
    (hE : 0≤E)
    (hEL : E≤C*H^n*Z^(radial-2*d+(max 0 (5*total+d-1)/4+α)))
    (hLB : L≤B*Z^d) :
    Z^(-d/2)*(Real.sqrt E/Real.sqrt (q*Z^radial/L^2))≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hb := low_inverse_sqrt_normalized radial q C B Z L d
    (max 0 (5*total+d-1)/4+α) H E n hq hC hB hz hL hH hE hEL hLB
  have ha := unselected_decay_absorbs_reflection_loss total d htotal hd
  calc
    _≤Z^(-d/2)*(Real.sqrt (C*B^2/q)*H^n*Z^((max 0 (5*total+d-1)/4+α)/2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=(Real.sqrt (C*B^2/q)*H^n)*Z^(-d/2+(max 0 (5*total+d-1)/4+α)/2) := by
      rw [Real.rpow_add hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

#print axioms low_inverse_sqrt_normalized
#print axioms low_inverse_sqrt_with_decay
end
end BelowSevenEighthsTight.LowExtension
