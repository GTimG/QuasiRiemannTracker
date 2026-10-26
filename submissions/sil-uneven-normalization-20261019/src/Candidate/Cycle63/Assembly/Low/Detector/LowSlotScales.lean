import Candidate.Cycle63.Assembly.Low.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGramScale
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSourceScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSlotScales

/- Original module: Candidate.Cycle63.Assembly.Low.Detector.LowGramScale. -/
section

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned original module Detector.LowGramScale.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace OAI

noncomputable section
namespace SevenEighths.Cycle63ProbeLow
open ProbePhysical

lemma compensated_gram_ratio (q X Y L : ℝ) (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hL : 0<L) :
    (Y/L)^2/(q*(X/L)*(Y/L))=Y/(q*X) := by
  field_simp

lemma compensated_gram_scale_bound (q X Y L δ : ℝ)
    (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hL : 1≤L) (hδ : 0≤δ)
    (hP : q*X≤Y) (htail : L*Y≤q^2*X^2) :
    (q*(X/L)*(Y/L)/(Y/L))*
      (1+((Y/L)^2/(q*(X/L)*(Y/L)))^(1/6:ℝ)+
        ((Y/L)^2/(q*(X/L)*(Y/L)))^2/(Y/L))*(Y/L)^δ ≤
      3*(q*X/L)*(Y/(q*X))^(1/6:ℝ)*Y^δ := by
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hp : 1≤Y/(q*X) := (le_div_iff₀ (mul_pos hq hX)).mpr (by simpa using hP)
  have hr : 1≤(Y/(q*X))^(1/6:ℝ) := Real.one_le_rpow hp (by norm_num)
  have ht : (Y/(q*X))^2/(Y/L)≤1 := by
    have he : (Y/(q*X))^2/(Y/L)=L*Y/(q^2*X^2) := by field_simp
    rw [he]
    exact (div_le_one (by positivity)).mpr htail
  have hys : (Y/L)^δ≤Y^δ := Real.rpow_le_rpow (by positivity)
    ((div_le_self hY.le hL)) hδ
  rw [compensated_gram_ratio q X Y L hq hX hY hl]
  have he : q*(X/L)*(Y/L)/(Y/L)=q*X/L := by field_simp
  rw [he]
  calc
    _≤(q*X/L)*(3*(Y/(q*X))^(1/6:ℝ))*Y^δ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hys
        (by positivity) (by positivity)
    _=_ := by ring

lemma source_gram_power (Z δ : ℝ) (hZ : 0<Z) :
    Z^(Cycle63.Arithmetic.x:ℝ)*(Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Cycle63.Arithmetic.y:ℝ))^δ=
      Z^((2*Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+(Cycle63.Arithmetic.y)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  exact Cycle63.Assembly.LowGeometry.gram_power δ

lemma source_gram_sqrt_power (Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^((2*Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+(Cycle63.Arithmetic.y)*δ:ℝ))=Z^((Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+((Cycle63.Arithmetic.y/2))*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

end SevenEighths.Cycle63ProbeLow
end

end OAI
end

/- Original module: Candidate.Cycle63.Assembly.Low.Detector.LowSourceScales. -/
section
/-! Adapted from OpenAI/math family003, pinned original module Detector.LowSourceScales.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
namespace SevenEighths.Cycle63ProbeLow
open ProbePhysical

lemma source_scale_ratio (Z : ℝ) (hZ : 0<Z) :
    Z^(Cycle63.Arithmetic.y:ℝ)/Z^(Cycle63.Arithmetic.x:ℝ)=Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ) := by
  rw [←Real.rpow_sub hZ]

lemma source_scale_square (Z : ℝ) (hZ : 0<Z) :
    Z^((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y):ℝ)*Z^(Cycle63.Arithmetic.y:ℝ)=(Z^(Cycle63.Arithmetic.x:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  rw [Cycle63.Assembly.LowGeometry.scale_square]
  congr 1
  norm_num
  ring

lemma source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ)) (hLl : L≤Z^((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y):ℝ)) :
    1≤Z^(Cycle63.Arithmetic.y:ℝ)/L ∧
    q*Z^(Cycle63.Arithmetic.x:ℝ)≤Z^(Cycle63.Arithmetic.y:ℝ) ∧
    L*Z^(Cycle63.Arithmetic.y:ℝ)≤q^2*(Z^(Cycle63.Arithmetic.x:ℝ))^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show ((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y):ℝ)≤Cycle63.Arithmetic.y from Cycle63.Assembly.LowGeometry.dilation_le_y))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (Cycle63.Arithmetic.x))).mp
    rwa [source_scale_ratio Z hz]
  · calc
      _≤Z^((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y):ℝ)*Z^(Cycle63.Arithmetic.y:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(Cycle63.Arithmetic.x:ℝ))^2 := source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ)) (hLl : L≤Z^((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y):ℝ)) (hδ : 0≤δ) :
    (q*(Z^(Cycle63.Arithmetic.x:ℝ)/L)*(Z^(Cycle63.Arithmetic.y:ℝ)/L)/(Z^(Cycle63.Arithmetic.y:ℝ)/L))*
      (1+((Z^(Cycle63.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Cycle63.Arithmetic.x:ℝ)/L)*(Z^(Cycle63.Arithmetic.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(Cycle63.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Cycle63.Arithmetic.x:ℝ)/L)*(Z^(Cycle63.Arithmetic.y:ℝ)/L)))^2/(Z^(Cycle63.Arithmetic.y:ℝ)/L))*
      (Z^(Cycle63.Arithmetic.y:ℝ)/L)^δ ≤
        (3*q/L)*Z^((2*Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+(Cycle63.Arithmetic.y)*δ:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(Cycle63.Arithmetic.x:ℝ)) (Z^(Cycle63.Arithmetic.y:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(Cycle63.Arithmetic.y:ℝ)/(q*Z^(Cycle63.Arithmetic.x:ℝ))≤Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ) := by
    rw [←source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(Cycle63.Arithmetic.y:ℝ)/(q*Z^(Cycle63.Arithmetic.x:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(Cycle63.Arithmetic.x:ℝ)/L)*(Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Cycle63.Arithmetic.y:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(Cycle63.Arithmetic.x:ℝ)*(Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Cycle63.Arithmetic.y:ℝ))^δ) := by ring
    _=_ := by rw [source_gram_power Z δ hz]

lemma source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ)) (hLl : L≤Z^((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y):ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(Cycle63.Arithmetic.x:ℝ)/L)*(Z^(Cycle63.Arithmetic.y:ℝ)/L)/(Z^(Cycle63.Arithmetic.y:ℝ)/L))*
      (1+((Z^(Cycle63.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Cycle63.Arithmetic.x:ℝ)/L)*(Z^(Cycle63.Arithmetic.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(Cycle63.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Cycle63.Arithmetic.x:ℝ)/L)*(Z^(Cycle63.Arithmetic.y:ℝ)/L)))^2/(Z^(Cycle63.Arithmetic.y:ℝ)/L))*
      (Z^(Cycle63.Arithmetic.y:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^((Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+((Cycle63.Arithmetic.y/2))*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ))
    (hLl : L≤Z^((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y):ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(Cycle63.Arithmetic.x:ℝ)/L) (Z^(Cycle63.Arithmetic.y:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^((Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+((Cycle63.Arithmetic.y/2))*δ:ℝ) :=
  source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ) ∧
      ∀L : ℝ,1≤L→L≤B*Z^(Cycle63.Arithmetic.ell:ℝ)→
        1≤Z^(Cycle63.Arithmetic.y:ℝ)/L ∧
        1≤(Z^(Cycle63.Arithmetic.y:ℝ)/L)^2/lowPhysicalScale C (Z^(Cycle63.Arithmetic.x:ℝ)/L) (Z^(Cycle63.Arithmetic.y:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(Cycle63.Arithmetic.x:ℝ)/L) (Z^(Cycle63.Arithmetic.y:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^((Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+((Cycle63.Arithmetic.y/2))*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ) from Cycle63.Assembly.LowGeometry.b_pos)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y-Cycle63.Arithmetic.ell):ℝ) from Cycle63.Assembly.LowGeometry.dilation_gap)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y):ℝ) := calc
    L≤B*Z^(Cycle63.Arithmetic.ell:ℝ) := hLB
    _≤Z^((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y-Cycle63.Arithmetic.ell):ℝ)*Z^(Cycle63.Arithmetic.ell:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^((2*Cycle63.Arithmetic.x-Cycle63.Arithmetic.y):ℝ) := by rw [←Real.rpow_add hz]; congr 1; ring
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.Cycle63ProbeLow
end

end OAI
end

/- Original module: Candidate.Cycle63.Assembly.Low.Detector.LowSlotScales. -/
section
/-! Adapted from OpenAI/math family003, pinned original module Detector.LowSlotScales.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Cycle63ProbeLow
open ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma elementNorm_finset_prod {ι : Type*} (F : Finset ι) (p : ι→O) :
    elementNorm (∏i∈F,p i)=∏i∈F,elementNorm (p i) := by
  induction F using Finset.induction_on with
  | empty => simp [elementNorm_one]
  | @insert i F hi ih => simp only [Finset.prod_insert hi,elementNorm_mul,ih]

lemma lowUnselectedProduct_norm_ge_one {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    1≤elementNorm (∏i : J,(a i).val) := by
  have hn : (∏i : J,(a i).val)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hslots i.val _ (a i).property)
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hn))

lemma lowUnselectedProduct_norm_bound {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤Cycle63.Arithmetic.ell)
    (b Z : ℝ) (hb : 1≤b) (hZ : 1≤Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤b^K*Z^(Cycle63.Arithmetic.ell:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤Cycle63.Arithmetic.ell :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)).trans hsum
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤b^K*Z^(Cycle63.Arithmetic.ell:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem eventually_original_slot_scales {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤Cycle63.Arithmetic.ell) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤Z^(Cycle63.Arithmetic.y:ℝ)/L ∧
      1≤(Z^(Cycle63.Arithmetic.y:ℝ)/L)^2/lowPhysicalScale C (Z^(Cycle63.Arithmetic.x:ℝ)/L) (Z^(Cycle63.Arithmetic.y:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(Cycle63.Arithmetic.x:ℝ)/L) (Z^(Cycle63.Arithmetic.y:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^((Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+((Cycle63.Arithmetic.y/2))*δ:ℝ) := by
  filter_upwards [eventually_compensated_source_scales C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)

end SevenEighths.Cycle63ProbeLow
end

end OAI
end
