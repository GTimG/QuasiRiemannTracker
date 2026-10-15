import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowGramScaleGeneric
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowTupleGram
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PhysicalCrudeMass
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometryGeneric

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma source_scale_ratio_generic (Z lx ly : ℝ) (hZ : 0<Z) :
    Z^ly/Z^lx=Z^(ly-lx) := by
  rw [←Real.rpow_sub hZ]

lemma source_scale_square_generic (Z lx ly : ℝ) (hZ : 0<Z) :
    Z^(2*lx-ly)*Z^ly=(Z^lx)^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  push_cast
  ring

lemma source_compensated_scale_admissible_generic
    (q Z L lx ly : ℝ) (hq : 1≤q) (hZ : 1≤Z) (hL : 1≤L)
    (hlxly : lx≤ly) (hql : q≤Z^(ly-lx)) (hLl : L≤Z^(2*lx-ly)) :
    1≤Z^ly/L ∧ q*Z^lx≤Z^ly ∧ L*Z^ly≤q^2*(Z^lx)^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa only [one_mul] using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show 2*lx-ly ≤ ly by linarith))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz lx)).mp
    rwa [source_scale_ratio_generic Z lx ly hz]
  · calc
      _≤Z^(2*lx-ly)*Z^ly := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^lx)^2 := source_scale_square_generic Z lx ly hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale_generic
    (q Z L lx ly δ : ℝ) (hq : 1≤q) (hZ : 1≤Z) (hL : 1≤L)
    (hlxly : lx≤ly) (hql : q≤Z^(ly-lx)) (hLl : L≤Z^(2*lx-ly))
    (hδ : 0≤δ) :
    (q*(Z^lx/L)*(Z^ly/L)/(Z^ly/L))*
      (1+((Z^ly/L)^2/(q*(Z^lx/L)*(Z^ly/L)))^(1/6:ℝ)+
        ((Z^ly/L)^2/(q*(Z^lx/L)*(Z^ly/L)))^2/(Z^ly/L))*
      (Z^ly/L)^δ≤(3*q/L)*Z^(lx+(ly-lx)/6+ly*δ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible_generic
    q Z L lx ly hq hZ hL hlxly hql hLl
  have hb := compensated_gram_scale_bound q (Z^lx) (Z^ly) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^ly/(q*Z^lx)≤Z^(ly-lx) := by
    rw [←source_scale_ratio_generic Z lx ly hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow
    (by positivity : 0≤Z^ly/(q*Z^lx)) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^lx/L)*(Z^(ly-lx))^(1/6:ℝ)*(Z^ly)^δ := by gcongr
    _=(3*q/L)*(Z^lx*(Z^(ly-lx))^(1/6:ℝ)*(Z^ly)^δ) := by ring
    _=_ := by rw [source_gram_power_generic Z lx ly δ hz]

lemma source_compensated_gram_sqrt_generic
    (q Z L lx ly δ : ℝ) (hq : 1≤q) (hZ : 1≤Z) (hL : 1≤L)
    (hlxly : lx≤ly) (hql : q≤Z^(ly-lx)) (hLl : L≤Z^(2*lx-ly))
    (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^lx/L)*(Z^ly/L)/(Z^ly/L))*
      (1+((Z^ly/L)^2/(q*(Z^lx/L)*(Z^ly/L)))^(1/6:ℝ)+
        ((Z^ly/L)^2/(q*(Z^lx/L)*(Z^ly/L)))^2/(Z^ly/L))*
      (Z^ly/L)^δ)≤
      Real.sqrt (3*q/L)*Z^(lx/2+(ly-lx)/12+ly*δ/2) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale_generic
    q Z L lx ly δ hq hZ hL hlxly hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power_generic Z lx ly δ
    (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound_generic
    (C : CalibrationData) (Z L lx ly δ : ℝ) (hZ : 1≤Z) (hL : 1≤L)
    (hlxly : lx≤ly) (hql : elementNorm C.generator≤Z^(ly-lx))
    (hLl : L≤Z^(2*lx-ly)) (hδ : 0≤δ) :
    lowGramFactor C (Z^lx/L) (Z^ly/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*
        Z^(lx/2+(ly-lx)/12+ly*δ/2) :=
  source_compensated_gram_sqrt_generic _ Z L lx ly δ
    (calibration_elementNorm_ge_one C) hZ hL hlxly hql hLl hδ

theorem eventually_compensated_source_scales_generic
    (C : CalibrationData) (B Etotal lx ly : ℝ)
    (hElx : Etotal<lx) (hlxly : lx<ly) (hgap : Etotal<2*lx-ly) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      elementNorm C.generator≤Z^(ly-lx) ∧
      ∀L : ℝ,1≤L→L≤B*Z^Etotal→
        1≤Z^ly/L ∧
        1≤(Z^ly/L)^2/lowPhysicalScale C (Z^lx/L) (Z^ly/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^lx/L) (Z^ly/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*
            Z^(lx/2+(ly-lx)/12+ly*δ/2) := by
  have hqexp : 0<ly-lx := by linarith
  have hbexp : 0<2*lx-ly-Etotal := by linarith
  have hq := (tendsto_rpow_atTop hqexp).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop hbexp).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^(2*lx-ly) := calc
    L≤B*Z^Etotal := hLB
    _≤Z^(2*lx-ly-Etotal)*Z^Etotal :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^(2*lx-ly) := by
      rw [←Real.rpow_add hz]
      congr 1
      ring
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible_generic
    _ Z L lx ly (calibration_elementNorm_ge_one C) hZ hL hlxly.le hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound_generic
    C Z L lx ly δ hZ hL hlxly.le hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _
    (calibration_elementNorm_pos C) (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr
    (by simpa using hp)

end SevenEighths.ProbePhysical
end

end OAI
