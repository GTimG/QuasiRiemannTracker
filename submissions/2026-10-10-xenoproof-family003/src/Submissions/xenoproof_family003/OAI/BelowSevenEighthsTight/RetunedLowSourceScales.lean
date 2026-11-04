import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSourceScales
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate

/- Source powers for the ORIGINAL lowGramFactor and its compensated Gram
   expression. This is not yet the full low physical-probe estimate. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.LowExtension
noncomputable section
open OAI OAI.SevenEighths ProbePhysical

lemma source_gram_power (ξ υ Z δ : ℝ) (hZ : 0<Z) :
    Z^ξ*(Z^(υ-ξ))^(1/6:ℝ)*(Z^υ)^δ=Z^((5*ξ+υ)/6+υ*δ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma source_gram_sqrt_power (ξ υ Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^((5*ξ+υ)/6+υ*δ))=Z^((5*ξ+υ)/12+(υ/2)*δ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

lemma source_scale_ratio (ξ υ : ℝ) (Z : ℝ) (hZ : 0<Z) :
    Z^υ/Z^ξ=Z^(υ-ξ) := by
  rw [←Real.rpow_sub hZ]

lemma source_scale_square (ξ υ : ℝ) (Z : ℝ) (hZ : 0<Z) :
    Z^(2*ξ-υ)*Z^υ=(Z^ξ)^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  ring

lemma source_compensated_scale_admissible (ξ υ : ℝ) (hxy : ξ≤υ) (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(υ-ξ)) (hLl : L≤Z^(2*ξ-υ)) :
    1≤Z^υ/L ∧
    q*Z^ξ≤Z^υ ∧
    L*Z^υ≤q^2*(Z^ξ)^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show 2*ξ-υ≤υ by linarith))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz ξ)).mp
    rwa [source_scale_ratio ξ υ Z hz]
  · calc
      _≤Z^(2*ξ-υ)*Z^υ := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^ξ)^2 := source_scale_square ξ υ Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale (ξ υ : ℝ) (hxy : ξ≤υ) (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(υ-ξ)) (hLl : L≤Z^(2*ξ-υ)) (hδ : 0≤δ) :
    (q*(Z^ξ/L)*(Z^υ/L)/(Z^υ/L))*
      (1+((Z^υ/L)^2/(q*(Z^ξ/L)*(Z^υ/L)))^(1/6:ℝ)+
        ((Z^υ/L)^2/(q*(Z^ξ/L)*(Z^υ/L)))^2/(Z^υ/L))*
      (Z^υ/L)^δ ≤
        (3*q/L)*Z^((5*ξ+υ)/6+υ*δ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible ξ υ hxy q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^ξ) (Z^υ) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^υ/(q*Z^ξ)≤Z^(υ-ξ) := by
    rw [←source_scale_ratio ξ υ Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^υ/(q*Z^ξ)) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^ξ/L)*(Z^(υ-ξ))^(1/6:ℝ)*(Z^υ)^δ := by gcongr
    _=(3*q/L)*(Z^ξ*(Z^(υ-ξ))^(1/6:ℝ)*(Z^υ)^δ) := by ring
    _=_ := by rw [source_gram_power ξ υ Z δ hz]

lemma source_compensated_gram_sqrt (ξ υ : ℝ) (hxy : ξ≤υ) (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(υ-ξ)) (hLl : L≤Z^(2*ξ-υ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^ξ/L)*(Z^υ/L)/(Z^υ/L))*
      (1+((Z^υ/L)^2/(q*(Z^ξ/L)*(Z^υ/L)))^(1/6:ℝ)+
        ((Z^υ/L)^2/(q*(Z^ξ/L)*(Z^υ/L)))^2/(Z^υ/L))*
      (Z^υ/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^((5*ξ+υ)/12+(υ/2)*δ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale ξ υ hxy q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power ξ υ Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound (ξ υ : ℝ) (hxy : ξ≤υ) (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^(υ-ξ))
    (hLl : L≤Z^(2*ξ-υ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^ξ/L) (Z^υ/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^((5*ξ+υ)/12+(υ/2)*δ) :=
  source_compensated_gram_sqrt ξ υ hxy _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ


lemma eventually_compensated_source_scales (ξ υ total : ℝ)
    (hgap : 0<υ-ξ) (hmargin : 0<2*ξ-υ-total) (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^(υ-ξ) ∧
      ∀L : ℝ,1≤L→L≤B*Z^total→
        1≤Z^υ/L ∧
        1≤(Z^υ/L)^2/lowPhysicalScale C (Z^ξ/L) (Z^υ/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^ξ/L) (Z^υ/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^((5*ξ+υ)/12+(υ/2)*δ) := by
  have hq := (tendsto_rpow_atTop hgap).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop hmargin).eventually (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^(2*ξ-υ) := calc
    L≤B*Z^total := hLB
    _≤Z^(2*ξ-υ-total)*Z^total := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^(2*ξ-υ) := by rw [←Real.rpow_add hz];congr 1;ring
  have hxy : ξ≤υ := by linarith
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible ξ υ hxy _ Z L
    (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound ξ υ hxy C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

theorem rational_gram_geometry :
    0<lyRat-lxRat ∧ 0<2*lxRat-lyRat-ellRat ∧
    (5*lxRat+lyRat)/12=sigmaRat+(-2/3-bRat/6) := by
  norm_num [lxRat,lyRat,ellRat,bRat,sigmaRat]

#print axioms source_compensated_gram_sqrt
#print axioms eventually_compensated_source_scales
#print axioms rational_gram_geometry
end
end BelowSevenEighthsTight.LowExtension
