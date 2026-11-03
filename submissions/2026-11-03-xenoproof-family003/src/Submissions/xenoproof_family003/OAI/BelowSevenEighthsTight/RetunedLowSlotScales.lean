import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSlotScales
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedLowSourceScales

/- Original compensated tuple scales with variable total length and source
   powers. This adapter does not assert a full physical-probe estimate. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.LowExtension
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ProbePhysical CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma lowUnselectedProduct_norm_bound (total : ℝ) {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤total)
    (b Z : ℝ) (hb : 1≤b) (hZ : 1≤Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤b^K*Z^(total:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤total :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)).trans hsum
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤b^K*Z^(total:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem eventually_original_slot_scales (ξ υ total : ℝ)
    (hgap : 0<υ-ξ) (hmargin : 0<2*ξ-υ-total) {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤total) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤Z^υ/L ∧
      1≤(Z^υ/L)^2/lowPhysicalScale C (Z^ξ/L) (Z^υ/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^ξ/L) (Z^υ/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^((5*ξ+υ)/12+(υ/2)*δ) := by
  filter_upwards [eventually_compensated_source_scales ξ υ total hgap hmargin C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (lowUnselectedProduct_norm_bound total ell hell hsum b Z hb hZ.1 slots hnorm J a)


#print axioms lowUnselectedProduct_norm_bound
#print axioms eventually_original_slot_scales
end
end BelowSevenEighthsTight.LowExtension
