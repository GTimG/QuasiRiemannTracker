/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.UniformReflection

/-! The initial squarefree selected bound follows from the proved reflection
and elementary finite energy/ideal counting. No additional additive sieve
estimate is assumed. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

/-- Trivial energy bound for the actual naturally zero-extended matrix. -/
theorem selectedNorm_card_bound (rows : Finset O) (sources : Finset (Ideal O)) :
    selectedNorm rows sources ≤ (rows.card : ℝ)*(sources.card : ℝ) := by
  apply selectedNorm_le_of_energy _ _ _ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  intro a
  have hpoint (I : sources) :
      ‖∑ r : rows, idealRowHom r.val I.val*a r‖^2 ≤ (rows.card : ℝ)*∑ r, ‖a r‖^2 := by
    have hnorm : ‖∑ r : rows, idealRowHom r.val I.val*a r‖ ≤ ∑ r, ‖a r‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)
    apply (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset rows) (fun _ => (1 : ℝ)) (fun r => ‖a r‖)
  unfold selectedDualEnergy selectedMatrix
  apply (Finset.sum_le_sum fun I _ => hpoint I).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  ring

/-- Supported ideal counting also holds for subunit cutoffs, when the
source set must be empty. -/
theorem supportedSources_card_le (S : Finset (Ideal O)) (Y : ℝ) (hY : 0 ≤ Y)
    (hS : ∀ I ∈ S, Supported I) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y := by
  by_cases h1 : 1 ≤ Y
  · exact DescentFiberCost.finite_ideal_count_real S Y h1 (fun I hI => (hS I hI).1) hN
  · have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      have hone : (1 : ℝ) ≤ Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (hS I hI).1 (Ideal.absNorm_eq_zero_iff.mp hz))
      exact h1 (hone.trans (hN I hI))
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem quotient_selectedNorm_trivial (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (D : Ideal O) (hD : D ≠ 0) (B Y : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B))
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (hSN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    selectedNorm (selectedQuotientRows F D) S ≤ 32768*(B/(Ideal.absNorm D : ℝ))*Y := by
  apply (selectedNorm_card_bound _ _).trans
  have hh := mul_le_mul (quotientRows_card_le F hF D hD B hB hN)
    (supportedSources_card_le S Y hY hS hSN) (Nat.cast_nonneg _)
    (show 0 ≤ 256*(B/(Ideal.absNorm D : ℝ)) by positivity)
  apply hh.trans_eq
  ring

/-- Substitution of the actual trivial descendant bound into every reflected
mode yields the genuine initial `L+B²` envelope. -/
theorem simpleReflectionProfile_trivial (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (L B H : ℝ) (hL : 1 ≤ L) (hB : 0 < B) (hH : 1 ≤ H)
    (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) :
    simpleReflectionProfile F L B H ≤ 131072*H*(L+B^2) := by
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := by linarith
  apply simpleReflectionProfile_le_of_modes F L B H _ (by positivity)
  intro k hk D hD e he
  have hd := selectedGcd_spec F hF (2*B) (fun I hI => (hN I hI).2) D hD
  have hDN : (1 : ℝ) ≤ Ideal.absNorm D := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hh => hd.1.1 (Ideal.absNorm_eq_zero_iff.mp hh))
  have hDN0 : 0 < (Ideal.absNorm D : ℝ) := by linarith
  have hR := (reflectedSourceRatio_range F hF L B hL (fun I hI => (hN I hI).2) D hD e he k hk).1
  have hR0 : 0 < reflectedSourceRatio e k := by linarith
  let Y := reflectedFrequencyCutoff L B H D e k
  have hY : 0 ≤ Y := by dsimp [Y,reflectedFrequencyCutoff]; positivity
  have hpool := reflectedFrequencyPool_spec L B H D e k hY
  have hnorm := quotient_selectedNorm_trivial F hF D hd.1.1 B Y hB.le hY hN
    (selectedFrequencyPool (reflectionFrequencies Y) Y) (fun I hI => (hpool I hI).1)
    (fun I hI => (hpool I hI).2)
  have hfactor : 0 ≤ L*(Ideal.absNorm D : ℝ)/(B*reflectedSourceRatio e k) := by positivity
  calc
    _ ≤ L/reflectedSourceRatio e k + (L*(Ideal.absNorm D : ℝ)/(B*reflectedSourceRatio e k))*
        (32768*(B/(Ideal.absNorm D : ℝ))*Y) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm hfactor)
    _ = L/reflectedSourceRatio e k + 131072*B^2*H/(Ideal.absNorm D : ℝ)^2 := by
      dsimp [Y,reflectedFrequencyCutoff]
      field_simp
      <;> ring
    _ ≤ L + 131072*B^2*H := by
      apply add_le_add (div_le_self hL0.le hR)
      exact div_le_self (by positivity) (one_le_pow₀ hDN)
    _ ≤ _ := by nlinarith [sq_nonneg B, mul_nonneg hL0.le (sub_nonneg.mpr hH)]

/-- Actual all-source initial bound, uniform over selected squarefree rows.
Its proof uses the completed reflection; no sextic additive-sieve input is
introduced. -/
theorem squarefree_selected_initial_bound (P loss : ℝ) (hP : 0 ≤ P) (hloss : 0 < loss) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ (Z L B : ℝ) (F S : Finset (Ideal O)),
      Z₀ ≤ Z → 1 ≤ L → L ≤ Z^P → 1 ≤ B → B ≤ Z^P →
      (∀ I ∈ F, Admissible I) →
      (∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈
        (Ideal.span {(36 : O)} : Ideal O)) →
      (∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) →
      selectedNorm (F.image primaryGenerator) S ≤ C*Z^loss*(L+B^2) := by
  obtain ⟨C,Z₀,s,hC,hs,hs1,hsloss,hreflection⟩ := squarefree_uniform_reflection P (loss/2) hP (by positivity)
  refine ⟨131072*C,max Z₀ 1,by positivity,?_⟩
  intro Z L B F S hZ hL hLU hB hBU hF hmod hN hS
  have hz1 : 1 ≤ Z := (le_max_right _ _).trans hZ
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
  have hprofile := simpleReflectionProfile_trivial F hF L B (Z^s) hL (by linarith)
    (Real.one_le_rpow hz1 hs.le) hN
  calc
    _ ≤ C*Z^(loss/2)*simpleReflectionProfile F L B (Z^s) :=
      hreflection Z L B F S ((le_max_left _ _).trans hZ) hL hLU hB hBU hF hmod hN hS
    _ ≤ C*Z^(loss/2)*(131072*Z^s*(L+B^2)) := mul_le_mul_of_nonneg_left hprofile (by positivity)
    _ = 131072*C*Z^(loss/2+s)*(L+B^2) := by rw [Real.rpow_add hz]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (by positivity)

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.squarefree_selected_initial_bound
