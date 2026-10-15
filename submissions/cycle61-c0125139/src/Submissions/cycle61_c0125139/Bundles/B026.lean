/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B025
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSlotScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSourceScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolGood

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Detector.LowSourceScales; sha256 4642312b3e6f86166394b067778d4fefb9aa71e3f44189d2dc6285c49bd7ff56 -/
section
                                    
                                                           
                                                 
/-! Adapted from OpenAI/math family003, pinned original module Detector.LowSourceScales.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
namespace SevenEighths.Cycle61ProbeLow
open ProbePhysical

lemma source_scale_ratio (Z : ℝ) (hZ : 0<Z) :
    Z^(Cycle61.Arithmetic.y:ℝ)/Z^(Cycle61.Arithmetic.x:ℝ)=Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ) := by
  rw [←Real.rpow_sub hZ]

lemma source_scale_square (Z : ℝ) (hZ : 0<Z) :
    Z^((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y):ℝ)*Z^(Cycle61.Arithmetic.y:ℝ)=(Z^(Cycle61.Arithmetic.x:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  rw [Cycle61.Assembly.LowGeometry.scale_square]
  congr 1
  norm_num
  ring

lemma source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ)) (hLl : L≤Z^((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y):ℝ)) :
    1≤Z^(Cycle61.Arithmetic.y:ℝ)/L ∧
    q*Z^(Cycle61.Arithmetic.x:ℝ)≤Z^(Cycle61.Arithmetic.y:ℝ) ∧
    L*Z^(Cycle61.Arithmetic.y:ℝ)≤q^2*(Z^(Cycle61.Arithmetic.x:ℝ))^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show ((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y):ℝ)≤Cycle61.Arithmetic.y from Cycle61.Assembly.LowGeometry.dilation_le_y))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (Cycle61.Arithmetic.x))).mp
    rwa [source_scale_ratio Z hz]
  · calc
      _≤Z^((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y):ℝ)*Z^(Cycle61.Arithmetic.y:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(Cycle61.Arithmetic.x:ℝ))^2 := source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ)) (hLl : L≤Z^((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y):ℝ)) (hδ : 0≤δ) :
    (q*(Z^(Cycle61.Arithmetic.x:ℝ)/L)*(Z^(Cycle61.Arithmetic.y:ℝ)/L)/(Z^(Cycle61.Arithmetic.y:ℝ)/L))*
      (1+((Z^(Cycle61.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Cycle61.Arithmetic.x:ℝ)/L)*(Z^(Cycle61.Arithmetic.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(Cycle61.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Cycle61.Arithmetic.x:ℝ)/L)*(Z^(Cycle61.Arithmetic.y:ℝ)/L)))^2/(Z^(Cycle61.Arithmetic.y:ℝ)/L))*
      (Z^(Cycle61.Arithmetic.y:ℝ)/L)^δ ≤
        (3*q/L)*Z^((2*Cycle61.Assembly.signal Cycle61.Arithmetic.theta)+(Cycle61.Arithmetic.y)*δ:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(Cycle61.Arithmetic.y:ℝ)/(q*Z^(Cycle61.Arithmetic.x:ℝ))≤Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ) := by
    rw [←source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(Cycle61.Arithmetic.y:ℝ)/(q*Z^(Cycle61.Arithmetic.x:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(Cycle61.Arithmetic.x:ℝ)/L)*(Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Cycle61.Arithmetic.y:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(Cycle61.Arithmetic.x:ℝ)*(Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Cycle61.Arithmetic.y:ℝ))^δ) := by ring
    _=_ := by rw [source_gram_power Z δ hz]

lemma source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ)) (hLl : L≤Z^((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y):ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(Cycle61.Arithmetic.x:ℝ)/L)*(Z^(Cycle61.Arithmetic.y:ℝ)/L)/(Z^(Cycle61.Arithmetic.y:ℝ)/L))*
      (1+((Z^(Cycle61.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Cycle61.Arithmetic.x:ℝ)/L)*(Z^(Cycle61.Arithmetic.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(Cycle61.Arithmetic.y:ℝ)/L)^2/(q*(Z^(Cycle61.Arithmetic.x:ℝ)/L)*(Z^(Cycle61.Arithmetic.y:ℝ)/L)))^2/(Z^(Cycle61.Arithmetic.y:ℝ)/L))*
      (Z^(Cycle61.Arithmetic.y:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^((Cycle61.Assembly.signal Cycle61.Arithmetic.theta)+((Cycle61.Arithmetic.y/2))*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ))
    (hLl : L≤Z^((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y):ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(Cycle61.Arithmetic.x:ℝ)/L) (Z^(Cycle61.Arithmetic.y:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^((Cycle61.Assembly.signal Cycle61.Arithmetic.theta)+((Cycle61.Arithmetic.y/2))*δ:ℝ) :=
  source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ) ∧
      ∀L : ℝ,1≤L→L≤B*Z^(Cycle61.Arithmetic.ell:ℝ)→
        1≤Z^(Cycle61.Arithmetic.y:ℝ)/L ∧
        1≤(Z^(Cycle61.Arithmetic.y:ℝ)/L)^2/lowPhysicalScale C (Z^(Cycle61.Arithmetic.x:ℝ)/L) (Z^(Cycle61.Arithmetic.y:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(Cycle61.Arithmetic.x:ℝ)/L) (Z^(Cycle61.Arithmetic.y:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^((Cycle61.Assembly.signal Cycle61.Arithmetic.theta)+((Cycle61.Arithmetic.y/2))*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ) from Cycle61.Assembly.LowGeometry.b_pos)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y-Cycle61.Arithmetic.ell):ℝ) from Cycle61.Assembly.LowGeometry.dilation_gap)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y):ℝ) := calc
    L≤B*Z^(Cycle61.Arithmetic.ell:ℝ) := hLB
    _≤Z^((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y-Cycle61.Arithmetic.ell):ℝ)*Z^(Cycle61.Arithmetic.ell:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^((2*Cycle61.Arithmetic.x-Cycle61.Arithmetic.y):ℝ) := by rw [←Real.rpow_add hz]; congr 1; ring
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.Cycle61ProbeLow
end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Low.Detector.LowSourceScales -/

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Detector.LowSlotScales; sha256 ec66fcdfdf745a8334a7316c63f8739bac92a09852acb783929070a3f9a101f5 -/
section
                                    
                                                         
                                                    
/-! Adapted from OpenAI/math family003, pinned original module Detector.LowSlotScales.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Cycle61ProbeLow
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
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤Cycle61.Arithmetic.ell)
    (b Z : ℝ) (hb : 1≤b) (hZ : 1≤Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤b^K*Z^(Cycle61.Arithmetic.ell:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤Cycle61.Arithmetic.ell :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)).trans hsum
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤b^K*Z^(Cycle61.Arithmetic.ell:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem eventually_original_slot_scales {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤Cycle61.Arithmetic.ell) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤Z^(Cycle61.Arithmetic.y:ℝ)/L ∧
      1≤(Z^(Cycle61.Arithmetic.y:ℝ)/L)^2/lowPhysicalScale C (Z^(Cycle61.Arithmetic.x:ℝ)/L) (Z^(Cycle61.Arithmetic.y:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(Cycle61.Arithmetic.x:ℝ)/L) (Z^(Cycle61.Arithmetic.y:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^((Cycle61.Assembly.signal Cycle61.Arithmetic.theta)+((Cycle61.Arithmetic.y/2))*δ:ℝ) := by
  filter_upwards [eventually_compensated_source_scales C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)

end SevenEighths.Cycle61ProbeLow
end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Low.Detector.LowSlotScales -/

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Detector.LowOriginalPools; sha256 ffd4d58ded11ec30c13bf0cf633bc0803620d0db6c126793e1cb9b754680a4e4 -/
section
                                    
                                                         
                                                       
                                                  
/-! Adapted from OpenAI/math family003, module Detector.LowOriginalPools at openai/math fd4aeeb2e
(the pruned source fork c388e88e6 no longer has it, so this file imports that module's own
imports). Changed physical geometry and explicit compensation bookkeeping.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Cycle61ProbeLow
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma originalPool_element_norm (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤a) (hab : a≤b) (hY : 0<Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : elementNorm n≤Y*b := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  exact (pool_norm_bounds R S ha hab hY P hP).2

theorem originalPools_low_scales {K : ℕ} (R : Set Id) (S : Finset Id)
    (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤Cycle61.Arithmetic.ell)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      let T := fun i=>canonicalSlotSupport (pool R S a b (Z^(ell i)))
      ∀(J : Finset (Fin K))(p : LowUnselectedTuple T J),
      let L := elementNorm (∏i : J,(p i).val)
      1≤Z^(Cycle61.Arithmetic.y:ℝ)/L ∧
      1≤(Z^(Cycle61.Arithmetic.y:ℝ)/L)^2/lowPhysicalScale (calibrationForSet S hmax) (Z^(Cycle61.Arithmetic.x:ℝ)/L) (Z^(Cycle61.Arithmetic.y:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor (calibrationForSet S hmax) (Z^(Cycle61.Arithmetic.x:ℝ)/L) (Z^(Cycle61.Arithmetic.y:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm (calibrationForSet S hmax).generator/L)*Z^((Cycle61.Assembly.signal Cycle61.Arithmetic.theta)+((Cycle61.Arithmetic.y/2))*δ:ℝ) := by
  filter_upwards [eventually_original_slot_scales (calibrationForSet S hmax) ell hell hsum
    (max 1 b) (le_max_left _ _)] with Z hZ
  refine ⟨hZ.1,?_⟩
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ.1
  apply hZ.2
  · intro i n hn
    exact canonicalSlotSupport_nonzero _ (pool_supported R S hS a b _) n hn
  · intro i n hn
    apply (originalPool_element_norm R S hS a b (Z^(ell i)) ha hab (by positivity) n hn).trans
    calc
      _≤Z^(ell i)*max 1 b := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _=_ := mul_comm _ _

end SevenEighths.Cycle61ProbeLow
end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Low.Detector.LowOriginalPools -/

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Detector.LowNominalGeometry; sha256 2ba28ab58f64e5a6373fb90e1ad4b356160c3e9c14b8483c53e985a403a6fe6d -/
section
                                    
                                                              
                                                     
/-! Adapted from OpenAI/math family003, pinned original module Detector.LowNominalGeometry.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Cycle61ProbeLow
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowUnselectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i∈J,ell i

def lowSelectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i : SelectedSlot J,ell i.val

lemma lowLength_sum {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) :
    lowUnselectedLength ell J+lowSelectedLength ell J=∑i,ell i := by
  rw [lowUnselectedLength,lowSelectedLength,Finset.sum_coe_sort]
  exact Finset.sum_add_sum_compl J ell

lemma lowLength_bounds {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤Cycle61.Arithmetic.ell) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤Cycle61.Arithmetic.ell ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤Cycle61.Arithmetic.ell-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowUnselectedProduct_norm_lower {K : ℕ} (ell : Fin K→ℝ)
    (a Z : ℝ) (ha : 0<a) (hZ : 0<Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→a*Z^(ell i)≤elementNorm x)
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    (min 1 a)^K*Z^(lowUnselectedLength ell J)≤elementNorm (∏i : J,(p i).val) := by
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤a^J.card*Z^(lowUnselectedLength ell J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (pow_le_pow_of_le_one (le_of_lt (lt_min zero_lt_one ha)) (min_le_left _ _) hc).trans
        (pow_le_pow_left₀ (by positivity) (min_le_right _ _) _)
    _=∏i : J,a*Z^(ell i.val) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun i _=>hslots i.val _ (p i).property)

lemma originalPool_element_lower (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤a) (hab : a≤b) (hY : 0<Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : a*Y≤elementNorm n := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  simpa only [mul_comm] using (pool_norm_bounds R S ha hab hY P hP).1.le

lemma lowPhysicalScale_source (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(Cycle61.Arithmetic.x:ℝ)/L) (Z^(Cycle61.Arithmetic.y:ℝ)/L)=
      elementNorm C.generator*Z^((1-Cycle61.Arithmetic.ell):ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(Cycle61.Arithmetic.x:ℝ)*Z^(Cycle61.Arithmetic.y:ℝ)=Z^((1-Cycle61.Arithmetic.ell):ℝ) := by rw [←Real.rpow_add hZ,Cycle61.Arithmetic.x_add_y]
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(Cycle61.Arithmetic.x:ℝ)/L) (Z^(Cycle61.Arithmetic.y:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^((1-Cycle61.Arithmetic.ell)-2*d:ℝ) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^((1-Cycle61.Arithmetic.ell):ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ (1-Cycle61.Arithmetic.ell) (2*d)]
      ring

lemma lowSelectedScale_product {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0<Z) :
    (∏i∈Finset.univ\J,Z^(ell i))=Z^(lowSelectedLength ell J) := by
  rw [lowSelectedLength,Finset.sum_coe_sort,Real.rpow_sum_of_pos hZ]

lemma lowSelectedCaps_product {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (J : Finset (Fin K)) (Z b : ℝ) (hZ : 1≤Z) :
    (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤
      (max 1 b)^K*Z^(lowSelectedLength ell J) := by
  have hc : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  calc
    _≤∏i : SelectedSlot J,max 1 b*Z^(ell i.val) := by
      apply Finset.prod_le_prod₀ (fun _ _=>le_trans zero_le_one (le_max_left _ _))
      intro i hi
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i.val))
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _=(max 1 b)^(Fintype.card (SelectedSlot J))*Z^(lowSelectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

end SevenEighths.Cycle61ProbeLow
end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Low.Detector.LowNominalGeometry -/
