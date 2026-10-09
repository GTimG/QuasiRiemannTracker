import OAI.NumberTheory.DirichletL.Detector.LowSourceScales
import QRH.Detector.LowReflectedLength
import QRH.Detector.LowGramScale

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual physical objects unchanged. Optimized scales and explicit reflected penalty. -/
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

section
variable (Z : ℝ) (hZ : 0<Z)
include Z hZ

lemma source_scale_ratio_optimized :
    Z^(QRH.ly:ℝ)/Z^(QRH.lx:ℝ)=Z^(QRH.b:ℝ) := by
  rw [←Real.rpow_sub hZ]
  norm_num [QRH.b, QRH.ell, QRH.tightTheta, QRH.lx, QRH.ly, QRH.M]


lemma source_scale_square_optimized :
    Z^((2*QRH.lx-QRH.ly):ℝ)*Z^(QRH.ly:ℝ)=(Z^(QRH.lx:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  norm_num [QRH.b, QRH.ell, QRH.tightTheta, QRH.lx, QRH.ly, QRH.M]


end

lemma source_compensated_scale_admissible_optimized (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(QRH.b:ℝ)) (hLl : L≤Z^((2*QRH.lx-QRH.ly):ℝ)) :
    1≤Z^(QRH.ly:ℝ)/L ∧
    q*Z^(QRH.lx:ℝ)≤Z^(QRH.ly:ℝ) ∧
    L*Z^(QRH.ly:ℝ)≤q^2*(Z^(QRH.lx:ℝ))^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show ((2*QRH.lx-QRH.ly):ℝ)≤QRH.ly by norm_num [QRH.b, QRH.ell, QRH.tightTheta, QRH.lx, QRH.ly, QRH.M]))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (QRH.lx))).mp
    rwa [source_scale_ratio_optimized Z hz]
  · calc
      _≤Z^((2*QRH.lx-QRH.ly):ℝ)*Z^(QRH.ly:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(QRH.lx:ℝ))^2 := source_scale_square_optimized Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)


section
variable (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z) (hL : 1≤L) (hql : q≤Z^(QRH.b:ℝ)) (hLl : L≤Z^((2*QRH.lx-QRH.ly):ℝ)) (hδ : 0≤δ)
include q Z L δ hq hZ hL hql hLl hδ

lemma source_compensated_gram_scale_optimized :
    (q*(Z^(QRH.lx:ℝ)/L)*(Z^(QRH.ly:ℝ)/L)/(Z^(QRH.ly:ℝ)/L))*
      (1+((Z^(QRH.ly:ℝ)/L)^2/(q*(Z^(QRH.lx:ℝ)/L)*(Z^(QRH.ly:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(QRH.ly:ℝ)/L)^2/(q*(Z^(QRH.lx:ℝ)/L)*(Z^(QRH.ly:ℝ)/L)))^2/(Z^(QRH.ly:ℝ)/L))*
      (Z^(QRH.ly:ℝ)/L)^δ ≤
        (3*q/L)*Z^((2*QRH.C QRH.tightTheta)+(QRH.ly)*δ:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible_optimized q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(QRH.lx:ℝ)) (Z^(QRH.ly:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(QRH.ly:ℝ)/(q*Z^(QRH.lx:ℝ))≤Z^(QRH.b:ℝ) := by
    rw [←source_scale_ratio_optimized Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(QRH.ly:ℝ)/(q*Z^(QRH.lx:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(QRH.lx:ℝ)/L)*(Z^(QRH.b:ℝ))^(1/6:ℝ)*(Z^(QRH.ly:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(QRH.lx:ℝ)*(Z^(QRH.b:ℝ))^(1/6:ℝ)*(Z^(QRH.ly:ℝ))^δ) := by ring
    _=_ := by rw [source_gram_power_optimized Z δ hz]


lemma source_compensated_gram_sqrt_optimized :
    Real.sqrt ((q*(Z^(QRH.lx:ℝ)/L)*(Z^(QRH.ly:ℝ)/L)/(Z^(QRH.ly:ℝ)/L))*
      (1+((Z^(QRH.ly:ℝ)/L)^2/(q*(Z^(QRH.lx:ℝ)/L)*(Z^(QRH.ly:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(QRH.ly:ℝ)/L)^2/(q*(Z^(QRH.lx:ℝ)/L)*(Z^(QRH.ly:ℝ)/L)))^2/(Z^(QRH.ly:ℝ)/L))*
      (Z^(QRH.ly:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(QRH.C QRH.tightTheta+((QRH.ly/2))*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale_optimized q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power_optimized Z δ (lt_of_lt_of_le zero_lt_one hZ)]


end

lemma lowGramFactor_source_bound_optimized (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^(QRH.b:ℝ))
    (hLl : L≤Z^((2*QRH.lx-QRH.ly):ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(QRH.lx:ℝ)/L) (Z^(QRH.ly:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(QRH.C QRH.tightTheta+((QRH.ly/2))*δ:ℝ) :=
  source_compensated_gram_sqrt_optimized _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ


lemma eventually_compensated_source_scales_optimized (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^(QRH.b:ℝ) ∧
      ∀L : ℝ,1≤L→L≤B*Z^QRH.ell→
        1≤Z^(QRH.ly:ℝ)/L ∧
        1≤(Z^(QRH.ly:ℝ)/L)^2/lowPhysicalScale C (Z^(QRH.lx:ℝ)/L) (Z^(QRH.ly:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(QRH.lx:ℝ)/L) (Z^(QRH.ly:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(QRH.C QRH.tightTheta+((QRH.ly/2))*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<(QRH.b:ℝ) by norm_num [QRH.b, QRH.ell, QRH.tightTheta, QRH.lx, QRH.ly, QRH.M])).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<((2*QRH.lx-QRH.ly-QRH.ell):ℝ) by norm_num [QRH.b, QRH.ell, QRH.tightTheta, QRH.lx, QRH.ly, QRH.M])).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^((2*QRH.lx-QRH.ly):ℝ) := calc
    L≤B*Z^QRH.ell := hLB
    _≤Z^((2*QRH.lx-QRH.ly-QRH.ell):ℝ)*Z^QRH.ell := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^((2*QRH.lx-QRH.ly):ℝ) := by rw [←Real.rpow_add hz];norm_num [QRH.b, QRH.ell, QRH.tightTheta, QRH.lx, QRH.ly, QRH.M]
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible_optimized _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound_optimized C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.ProbePhysical
end

end OAI
