import Candidate.Target830.Physical.LowGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSlotScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
import Candidate.Target830.Physical.Low.Detector.LowSlotScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry

/- Original module: Candidate.Target830.Physical.Low.Detector.LowOriginalPools. -/
section
/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/
/-! Adapted from OpenAI/math family003, module Detector.LowOriginalPools at openai/math fd4aeeb2e
(the pruned source fork c388e88e6 no longer has it, so this file imports that module's own
imports). Changed physical geometry and explicit compensation bookkeeping.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Target830PhysicalProbeLow
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma originalPool_element_norm (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤ a) (hab : a≤ b) (hY : 0< Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : elementNorm n≤ Y*b := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  exact (pool_norm_bounds R S ha hab hY P hP).2

theorem originalPools_low_scales {K : ℕ} (R : Set Id) (S : Finset Id)
    (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Target830Physical.Arithmetic.ell)
    (a b : ℝ) (ha : 0≤ a) (hab : a≤ b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤ Z ∧
      let T := fun i=> canonicalSlotSupport (pool R S a b (Z^(ell i)))
      ∀(J : Finset (Fin K))(p : LowUnselectedTuple T J),
      let L := elementNorm (∏i : J,(p i).val)
      1≤ Z^(Target830Physical.Arithmetic.y:ℝ)/L ∧
      1≤(Z^(Target830Physical.Arithmetic.y:ℝ)/L)^2/lowPhysicalScale (calibrationForSet S hmax) (Z^(Target830Physical.Arithmetic.x:ℝ)/L) (Z^(Target830Physical.Arithmetic.y:ℝ)/L) ∧
      ∀δ : ℝ,0≤ δ→lowGramFactor (calibrationForSet S hmax) (Z^(Target830Physical.Arithmetic.x:ℝ)/L) (Z^(Target830Physical.Arithmetic.y:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm (calibrationForSet S hmax).generator/L)*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+((Target830Physical.Arithmetic.y/2))*δ:ℝ) := by
  filter_upwards [eventually_original_slot_scales (calibrationForSet S hmax) ell hell hsum
    (max 1 b) (le_max_left _ _)] with Z hZ
  refine ⟨hZ.1,?_⟩
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ.1
  apply hZ.2
  · intro i n hn
    exact canonicalSlotSupport_nonzero _ (pool_supported R S hS a b _) n hn
  · intro i n hn
    apply (originalPool_element_norm R S hS a b (Z^(ell i)) ha hab (by positivity) n hn).trans
    calc
      _≤ Z^(ell i)*max 1 b := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _=_ := mul_comm _ _

end SevenEighths.Target830PhysicalProbeLow
end

end OAI

#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.originalPool_element_norm
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.originalPools_low_scales
end

/- Original module: Candidate.Target830.Physical.Low.Detector.LowNominalGeometry. -/
section
/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/
/-! Adapted from OpenAI/math family003, pinned original module Detector.LowNominalGeometry.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Target830PhysicalProbeLow
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

lemma lowLength_bounds {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤ Target830Physical.Arithmetic.ell) (J : Finset (Fin K)) :
    0≤ lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤ Target830Physical.Arithmetic.ell ∧
    0≤ lowSelectedLength ell J ∧ lowSelectedLength ell J≤ Target830Physical.Arithmetic.ell-lowUnselectedLength ell J := by
  have hu : 0≤ lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=> hell i)
  have hs : 0≤ lowSelectedLength ell J := Finset.sum_nonneg (fun i _=> hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowUnselectedProduct_norm_lower {K : ℕ} (ell : Fin K→ℝ)
    (a Z : ℝ) (ha : 0< a) (hZ : 0< Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→a*Z^(ell i)≤ elementNorm x)
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    (min 1 a)^K*Z^(lowUnselectedLength ell J)≤ elementNorm (∏i : J,(p i).val) := by
  have hc : J.card≤ K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤ a^J.card*Z^(lowUnselectedLength ell J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (pow_le_pow_of_le_one (le_of_lt (lt_min zero_lt_one ha)) (min_le_left _ _) hc).trans
        (pow_le_pow_left₀ (by positivity) (min_le_right _ _) _)
    _=∏i : J,a*Z^(ell i.val) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤ _ := Finset.prod_le_prod₀ (fun _ _=> by positivity) (fun i _=> hslots i.val _ (p i).property)

lemma originalPool_element_lower (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤ a) (hab : a≤ b) (hY : 0< Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : a*Y≤ elementNorm n := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  simpa only [mul_comm] using (pool_norm_bounds R S ha hab hY P hP).1.le

lemma lowPhysicalScale_source (C : CalibrationData) (Z L : ℝ) (hZ : 0< Z) :
    lowPhysicalScale C (Z^(Target830Physical.Arithmetic.x:ℝ)/L) (Z^(Target830Physical.Arithmetic.y:ℝ)/L)=
      elementNorm C.generator*Z^((1-Target830Physical.Arithmetic.ell):ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(Target830Physical.Arithmetic.x:ℝ)*Z^(Target830Physical.Arithmetic.y:ℝ)=Z^((1-Target830Physical.Arithmetic.ell):ℝ) := by rw [←Real.rpow_add hZ,Target830Physical.Arithmetic.x_add_y]
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0< Z) (hc : 0< c) (hL : c*Z^d≤ L) :
    lowPhysicalScale C (Z^(Target830Physical.Arithmetic.x:ℝ)/L) (Z^(Target830Physical.Arithmetic.y:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^((1-Target830Physical.Arithmetic.ell)-2*d:ℝ) := by
  have hl : 0< L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source C Z L hZ]
  calc
    _≤ elementNorm C.generator*Z^((1-Target830Physical.Arithmetic.ell):ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ (1-Target830Physical.Arithmetic.ell) (2*d)]
      ring

lemma lowSelectedScale_product {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0< Z) :
    (∏i∈Finset.univ\J,Z^(ell i))=Z^(lowSelectedLength ell J) := by
  rw [lowSelectedLength,Finset.sum_coe_sort,Real.rpow_sum_of_pos hZ]

lemma lowSelectedCaps_product {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (J : Finset (Fin K)) (Z b : ℝ) (hZ : 1≤ Z) :
    (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤
      (max 1 b)^K*Z^(lowSelectedLength ell J) := by
  have hc : Fintype.card (SelectedSlot J)≤ K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  calc
    _≤∏i : SelectedSlot J,max 1 b*Z^(ell i.val) := by
      apply Finset.prod_le_prod₀ (fun _ _=> le_trans zero_le_one (le_max_left _ _))
      intro i hi
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i.val))
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _=(max 1 b)^(Fintype.card (SelectedSlot J))*Z^(lowSelectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
      rfl
    _≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

end SevenEighths.Target830PhysicalProbeLow
end

end OAI

#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.lowLength_sum
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.lowLength_bounds
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.lowUnselectedProduct_norm_lower
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.originalPool_element_lower
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.lowPhysicalScale_source
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.lowPhysicalScale_nominal_bound
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.lowSelectedScale_product
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.lowSelectedCaps_product
end
