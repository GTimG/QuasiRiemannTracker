import OAI.NumberTheory.DirichletL.Detector.LowSourceScales
import WeightedQRH.LowDetector.LowGramScale
/-! Adapted from OpenAI/math family003, pinned original module Detector.LowSourceScales.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace OAI

noncomputable section
namespace SevenEighths.WeightedProbeLow
open ProbePhysical

lemma source_scale_ratio (Z : ℝ) (hZ : 0<Z) :
    Z^(919/2000:ℝ)/Z^(747/2000:ℝ)=Z^(43/500:ℝ) := by
  rw [←Real.rpow_sub hZ]
  norm_num

lemma source_scale_square (Z : ℝ) (hZ : 0<Z) :
    Z^(23/80:ℝ)*Z^(919/2000:ℝ)=(Z^(747/2000:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  norm_num

lemma source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(43/500:ℝ)) (hLl : L≤Z^(23/80:ℝ)) :
    1≤Z^(919/2000:ℝ)/L ∧
    q*Z^(747/2000:ℝ)≤Z^(919/2000:ℝ) ∧
    L*Z^(919/2000:ℝ)≤q^2*(Z^(747/2000:ℝ))^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show (23/80:ℝ)≤919/2000 by norm_num))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (747/2000))).mp
    rwa [source_scale_ratio Z hz]
  · calc
      _≤Z^(23/80:ℝ)*Z^(919/2000:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(747/2000:ℝ))^2 := source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(43/500:ℝ)) (hLl : L≤Z^(23/80:ℝ)) (hδ : 0≤δ) :
    (q*(Z^(747/2000:ℝ)/L)*(Z^(919/2000:ℝ)/L)/(Z^(919/2000:ℝ)/L))*
      (1+((Z^(919/2000:ℝ)/L)^2/(q*(Z^(747/2000:ℝ)/L)*(Z^(919/2000:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(919/2000:ℝ)/L)^2/(q*(Z^(747/2000:ℝ)/L)*(Z^(919/2000:ℝ)/L)))^2/(Z^(919/2000:ℝ)/L))*
      (Z^(919/2000:ℝ)/L)^δ ≤
        (3*q/L)*Z^(2327/6000+(919/2000)*δ:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(919/2000:ℝ)/(q*Z^(747/2000:ℝ))≤Z^(43/500:ℝ) := by
    rw [←source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(919/2000:ℝ)/(q*Z^(747/2000:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(747/2000:ℝ)/L)*(Z^(43/500:ℝ))^(1/6:ℝ)*(Z^(919/2000:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(747/2000:ℝ)*(Z^(43/500:ℝ))^(1/6:ℝ)*(Z^(919/2000:ℝ))^δ) := by ring
    _=_ := by rw [source_gram_power Z δ hz]

lemma source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(43/500:ℝ)) (hLl : L≤Z^(23/80:ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(747/2000:ℝ)/L)*(Z^(919/2000:ℝ)/L)/(Z^(919/2000:ℝ)/L))*
      (1+((Z^(919/2000:ℝ)/L)^2/(q*(Z^(747/2000:ℝ)/L)*(Z^(919/2000:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(919/2000:ℝ)/L)^2/(q*(Z^(747/2000:ℝ)/L)*(Z^(919/2000:ℝ)/L)))^2/(Z^(919/2000:ℝ)/L))*
      (Z^(919/2000:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(2327/12000+(919/4000)*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^(43/500:ℝ))
    (hLl : L≤Z^(23/80:ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(747/2000:ℝ)/L) (Z^(919/2000:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(2327/12000+(919/4000)*δ:ℝ) :=
  source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^(43/500:ℝ) ∧
      ∀L : ℝ,1≤L→L≤B*Z^(167/1000:ℝ)→
        1≤Z^(919/2000:ℝ)/L ∧
        1≤(Z^(919/2000:ℝ)/L)^2/lowPhysicalScale C (Z^(747/2000:ℝ)/L) (Z^(919/2000:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(747/2000:ℝ)/L) (Z^(919/2000:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(2327/12000+(919/4000)*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<(43/500:ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<(241/2000:ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^(23/80:ℝ) := calc
    L≤B*Z^(167/1000:ℝ) := hLB
    _≤Z^(241/2000:ℝ)*Z^(167/1000:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^(23/80:ℝ) := by rw [←Real.rpow_add hz];norm_num
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.WeightedProbeLow
end

end OAI
