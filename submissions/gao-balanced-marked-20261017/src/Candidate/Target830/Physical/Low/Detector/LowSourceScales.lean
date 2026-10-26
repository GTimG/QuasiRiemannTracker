/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/
import Candidate.Target830.Physical.LowGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSourceScales
import Candidate.Target830.Physical.Low.Detector.LowGramScale
/-! Adapted from OpenAI/math family003, pinned original module Detector.LowSourceScales.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
namespace SevenEighths.Target830PhysicalProbeLow
open ProbePhysical

lemma source_scale_ratio (Z : ℝ) (hZ : 0< Z) :
    Z^(Target830Physical.Arithmetic.y:ℝ)/Z^(Target830Physical.Arithmetic.x:ℝ)=Z^((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ) := by
  rw [←Real.rpow_sub hZ]

lemma source_scale_square (Z : ℝ) (hZ : 0< Z) :
    Z^((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y):ℝ)*Z^(Target830Physical.Arithmetic.y:ℝ)=(Z^(Target830Physical.Arithmetic.x:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  rw [Target830Physical.Assembly.LowGeometry.scale_square]
  congr 1
  norm_num
  ring

lemma source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ)) (hLl : L≤ Z^((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y):ℝ)) :
    1≤ Z^(Target830Physical.Arithmetic.y:ℝ)/L ∧
    q*Z^(Target830Physical.Arithmetic.x:ℝ)≤ Z^(Target830Physical.Arithmetic.y:ℝ) ∧
    L*Z^(Target830Physical.Arithmetic.y:ℝ)≤ q^2*(Z^(Target830Physical.Arithmetic.x:ℝ))^2 := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0< L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show ((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y):ℝ)≤ Target830Physical.Arithmetic.y from Target830Physical.Assembly.LowGeometry.dilation_le_y))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (Target830Physical.Arithmetic.x))).mp
    rwa [source_scale_ratio Z hz]
  · calc
      _≤ Z^((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y):ℝ)*Z^(Target830Physical.Arithmetic.y:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(Target830Physical.Arithmetic.x:ℝ))^2 := source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ)) (hLl : L≤ Z^((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y):ℝ)) (hδ : 0≤ δ) :
    (q*(Z^(Target830Physical.Arithmetic.x:ℝ)/L)*(Z^(Target830Physical.Arithmetic.y:ℝ)/L)/(Z^(Target830Physical.Arithmetic.y:ℝ)/L))*
      (1+((Z^(Target830Physical.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Target830Physical.Arithmetic.x:ℝ)/L)*(Z^(Target830Physical.Arithmetic.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(Target830Physical.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Target830Physical.Arithmetic.x:ℝ)/L)*(Z^(Target830Physical.Arithmetic.y:ℝ)/L)))^2/(Z^(Target830Physical.Arithmetic.y:ℝ)/L))*
      (Z^(Target830Physical.Arithmetic.y:ℝ)/L)^δ ≤
        (3*q/L)*Z^((2*Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+(Target830Physical.Arithmetic.y)*δ:ℝ) := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0< q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0< L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(Target830Physical.Arithmetic.x:ℝ)) (Z^(Target830Physical.Arithmetic.y:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(Target830Physical.Arithmetic.y:ℝ)/(q*Z^(Target830Physical.Arithmetic.x:ℝ))≤ Z^((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ) := by
    rw [←source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤ Z^(Target830Physical.Arithmetic.y:ℝ)/(q*Z^(Target830Physical.Arithmetic.x:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(Target830Physical.Arithmetic.x:ℝ)/L)*(Z^((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Target830Physical.Arithmetic.y:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(Target830Physical.Arithmetic.x:ℝ)*(Z^((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Target830Physical.Arithmetic.y:ℝ))^δ) := by ring
    _=_ := by rw [source_gram_power Z δ hz]

lemma source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ)) (hLl : L≤ Z^((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y):ℝ)) (hδ : 0≤ δ) :
    Real.sqrt ((q*(Z^(Target830Physical.Arithmetic.x:ℝ)/L)*(Z^(Target830Physical.Arithmetic.y:ℝ)/L)/(Z^(Target830Physical.Arithmetic.y:ℝ)/L))*
      (1+((Z^(Target830Physical.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Target830Physical.Arithmetic.x:ℝ)/L)*(Z^(Target830Physical.Arithmetic.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(Target830Physical.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Target830Physical.Arithmetic.x:ℝ)/L)*(Z^(Target830Physical.Arithmetic.y:ℝ)/L)))^2/(Z^(Target830Physical.Arithmetic.y:ℝ)/L))*
      (Z^(Target830Physical.Arithmetic.y:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+((Target830Physical.Arithmetic.y/2))*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : elementNorm C.generator≤ Z^((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ))
    (hLl : L≤ Z^((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y):ℝ)) (hδ : 0≤ δ) :
    lowGramFactor C (Z^(Target830Physical.Arithmetic.x:ℝ)/L) (Z^(Target830Physical.Arithmetic.y:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+((Target830Physical.Arithmetic.y/2))*δ:ℝ) :=
  source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤ Z ∧ elementNorm C.generator≤ Z^((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ) ∧
      ∀L : ℝ,1≤ L→L≤ B*Z^(Target830Physical.Arithmetic.ell:ℝ)→
        1≤ Z^(Target830Physical.Arithmetic.y:ℝ)/L ∧
        1≤(Z^(Target830Physical.Arithmetic.y:ℝ)/L)^2/lowPhysicalScale C (Z^(Target830Physical.Arithmetic.x:ℝ)/L) (Z^(Target830Physical.Arithmetic.y:ℝ)/L) ∧
        ∀δ : ℝ,0≤ δ→lowGramFactor C (Z^(Target830Physical.Arithmetic.x:ℝ)/L) (Z^(Target830Physical.Arithmetic.y:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+((Target830Physical.Arithmetic.y/2))*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<((Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.x):ℝ) from Target830Physical.Assembly.LowGeometry.b_pos)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.ell):ℝ) from Target830Physical.Assembly.LowGeometry.dilation_gap)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0< L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤ Z^((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y):ℝ) := calc
    L≤ B*Z^(Target830Physical.Arithmetic.ell:ℝ) := hLB
    _≤ Z^((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y-Target830Physical.Arithmetic.ell):ℝ)*Z^(Target830Physical.Arithmetic.ell:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^((2*Target830Physical.Arithmetic.x-Target830Physical.Arithmetic.y):ℝ) := by rw [←Real.rpow_add hz]; congr 1; ring
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.Target830PhysicalProbeLow
end

end OAI

#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.source_scale_ratio
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.source_scale_square
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.source_compensated_scale_admissible
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.source_compensated_gram_scale
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.source_compensated_gram_sqrt
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.lowGramFactor_source_bound
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.eventually_compensated_source_scales
