/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalProbe/Geometry.lean
Original SHA-256: d1926593bd86246834f70d6cd63a2f6439f35795b2203fb752cc072e9feb4db8
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGramScale
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowTupleGram
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PhysicalCrudeMass

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical

lemma transport_source_gram_power (x y Z δ : ℝ) (hZ : 0<Z) :
    Z^x*(Z^(y-x))^(1/6:ℝ)*(Z^y)^δ=Z^(x+(y-x)/6+y*δ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma transport_source_gram_sqrt_power (x y Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^(x+(y-x)/6+y*δ))=Z^(x/2+(y-x)/12+(y/2)*δ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

lemma transport_lowLength_bounds {K : ℕ} (ell : Fin K→ℝ) (totalWidth : ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤totalWidth) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤totalWidth ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤totalWidth-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma transport_lowPhysicalScale_source (x y : ℝ) (C : CalibrationData) (Z L : ℝ)
    (hZ : 0<Z) :
    lowPhysicalScale C (Z^x/L) (Z^y/L)=elementNorm C.generator*Z^(x+y)/L^2 := by
  unfold lowPhysicalScale
  rw [Real.rpow_add hZ]
  ring

lemma transport_lowPhysicalScale_nominal_bound (x y : ℝ) (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^x/L) (Z^y/L)≤
      (elementNorm C.generator/c^2)*Z^(x+y-2*d) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [transport_lowPhysicalScale_source x y C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^(x+y)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring

lemma transport_source_scale_ratio (x y : ℝ) (Z : ℝ) (hZ : 0<Z) :
    Z^y/Z^x=Z^(y-x) := by
  rw [←Real.rpow_sub hZ]

lemma transport_source_scale_square (x y : ℝ) (Z : ℝ) (hZ : 0<Z) :
    Z^(2*x-y)*Z^y=(Z^x)^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  push_cast
  ring

lemma transport_source_compensated_scale_admissible (x y : ℝ) (hxy : x≤y) (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(y-x)) (hLl : L≤Z^(2*x-y)) :
    1≤Z^y/L ∧
    q*Z^x≤Z^y ∧
    L*Z^y≤q^2*(Z^x)^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show 2*x-y≤y by linarith))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz x)).mp
    rwa [transport_source_scale_ratio x y Z hz]
  · calc
      _≤Z^(2*x-y)*Z^y := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^x)^2 := transport_source_scale_square x y Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma transport_source_compensated_gram_scale (x y : ℝ) (hxy : x≤y) (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(y-x)) (hLl : L≤Z^(2*x-y)) (hδ : 0≤δ) :
    (q*(Z^x/L)*(Z^y/L)/(Z^y/L))*
      (1+((Z^y/L)^2/(q*(Z^x/L)*(Z^y/L)))^(1/6:ℝ)+
        ((Z^y/L)^2/(q*(Z^x/L)*(Z^y/L)))^2/(Z^y/L))*
      (Z^y/L)^δ ≤
        (3*q/L)*Z^(x+(y-x)/6+y*δ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := transport_source_compensated_scale_admissible x y hxy q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^x) (Z^y) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^y/(q*Z^x)≤Z^(y-x) := by
    rw [←transport_source_scale_ratio x y Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^y/(q*Z^x)) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^x/L)*(Z^(y-x))^(1/6:ℝ)*(Z^y)^δ := by gcongr
    _=(3*q/L)*(Z^x*(Z^(y-x))^(1/6:ℝ)*(Z^y)^δ) := by ring
    _=_ := by rw [transport_source_gram_power x y Z δ hz]

lemma transport_source_compensated_gram_sqrt (x y : ℝ) (hxy : x≤y) (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(y-x)) (hLl : L≤Z^(2*x-y)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^x/L)*(Z^y/L)/(Z^y/L))*
      (1+((Z^y/L)^2/(q*(Z^x/L)*(Z^y/L)))^(1/6:ℝ)+
        ((Z^y/L)^2/(q*(Z^x/L)*(Z^y/L)))^2/(Z^y/L))*
      (Z^y/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(x/2+(y-x)/12+(y/2)*δ) := by
  apply (Real.sqrt_le_sqrt (transport_source_compensated_gram_scale x y hxy q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),transport_source_gram_sqrt_power x y Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma transport_lowGramFactor_source_bound (x y : ℝ) (hxy : x≤y) (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^(y-x))
    (hLl : L≤Z^(2*x-y)) (hδ : 0≤δ) :
    lowGramFactor C (Z^x/L) (Z^y/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(x/2+(y-x)/12+(y/2)*δ) :=
  transport_source_compensated_gram_sqrt x y hxy _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma transport_eventually_compensated_source_scales (x y totalWidth : ℝ)
    (hxy : x < y) (hgrow : totalWidth < 2*x-y) (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^(y-x) ∧
      ∀L : ℝ,1≤L→L≤B*Z^totalWidth→
        1≤Z^y/L ∧
        1≤(Z^y/L)^2/lowPhysicalScale C (Z^x/L) (Z^y/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^x/L) (Z^y/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(x/2+(y-x)/12+(y/2)*δ) := by
  have hq := (tendsto_rpow_atTop (show 0<y-x by linarith)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<2*x-y-totalWidth by linarith)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^(2*x-y) := calc
    L≤B*Z^totalWidth := hLB
    _≤Z^(2*x-y-totalWidth)*Z^totalWidth := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^(2*x-y) := by rw [←Real.rpow_add hz];congr 1;ring
  obtain ⟨hy,hp,_⟩ := transport_source_compensated_scale_admissible x y hxy.le _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>transport_lowGramFactor_source_bound x y hxy.le C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.ProbePhysical
end

end OAI
