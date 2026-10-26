/- Adapted from PR63 gao-balanced-marked-20261017; Apache-2.0. Exact source provenance is in evidence/homogeneous-gain/upstream-provenance.json. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Upstream.DeletionCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceMask

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Record12518109GainDeletion
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentCommonMaskExpansion
open CenteredMomentNaturalRowSource
local notation "O" => HeckeFamily.O

theorem slotMass_le_card (R pool : Finset (Ideal O)) (β : Ideal O → ℂ)
    (P B : ℝ) (hB : 0 ≤ B) (hβ : ∀ I ∈ pool, ‖β I‖ ≤ B) :
    slotMass R pool β P ≤ (Real.sqrt P)⁻¹ * ((R.card : ℝ) * B) := by
  unfold slotMass
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  calc
    _ ≤ ∑ I ∈ pool ∩ R, B := Finset.sum_le_sum
      (fun I hI => hβ I (Finset.mem_inter.mp hI).1)
    _ = ((pool ∩ R).card : ℝ) * B := by simp
    _ ≤ (R.card : ℝ) * B := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : pool ∩ R ⊆ R)) hB

/-- Exact prime-slot deletion is an additive error. Existing natural row
zeros stay inside the character throughout the estimate. -/
theorem naturalSlot_excluded_sub_le_card (χ : Character) (R : Ideal O)
    (pool : Finset (Ideal O)) (hp : ∀ I ∈ pool, Prime I)
    (β : Ideal O → ℂ) (P B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ I ∈ pool, ‖β I‖ ≤ B) :
    ‖naturalSlot (excluded χ R) pool β P - naturalSlot χ pool β P‖ ≤
      (Real.sqrt P)⁻¹ * (((CompletedGauss.primeSupport R).card : ℝ) * B) := by
  have he : naturalSlot (excluded χ R) pool β P - naturalSlot χ pool β P =
      -naturalSlot χ (pool ∩ CompletedGauss.primeSupport R) β P := by
    rw [excluded,naturalSlot_delete χ _ (support_prime R) pool hp β P]
    abel
  rw [he,norm_neg]
  exact (naturalSlot_norm χ _ pool β P).trans
    (slotMass_le_card _ pool β P B hB hβ)

/-- Uniform error for deletion by an arbitrary nonzero polynomial-size
ideal. The slot coefficients and the natural row may vary freely. -/
theorem naturalSlot_excluded_sub_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character) (R : Ideal O), R ≠ 0 →
      ∀ (pool : Finset (Ideal O)), (∀ I ∈ pool, Prime I) →
      ∀ (β : Ideal O → ℂ) (P B : ℝ), 0 ≤ B →
        (∀ I ∈ pool, ‖β I‖ ≤ B) →
      ‖naturalSlot (excluded χ R) pool β P - naturalSlot χ pool β P‖ ≤
        (C*B)*(R.absNorm : ℝ)^ε*(Real.sqrt P)⁻¹ := by
  obtain ⟨C,hC,hcard⟩ := prime_support_card_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro χ R hR pool hp β P B hB hβ
  apply (naturalSlot_excluded_sub_le_card χ R pool hp β P B hB hβ).trans
  calc
    _ ≤ (Real.sqrt P)⁻¹ * ((C*(R.absNorm : ℝ)^ε)*B) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hcard R hR) hB)
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- A polynomial norm ceiling gives a power-saving additive slot error,
uniformly in the moving width. -/
theorem naturalSlot_excluded_polynomial (Bmask ε : ℝ) (hBmask : 0 ≤ Bmask)
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 1 ≤ U →
      ∀ (χ : Character) (R : Ideal O), R ≠ 0 → (R.absNorm : ℝ) ≤ U^Bmask →
      ∀ (pool : Finset (Ideal O)), (∀ I ∈ pool, Prime I) →
      ∀ (β : Ideal O → ℂ) (w B : ℝ), 0 ≤ B →
        (∀ I ∈ pool, ‖β I‖ ≤ B) →
      ‖naturalSlot (excluded χ R) pool β (U^w) - naturalSlot χ pool β (U^w)‖ ≤
        (C*B)*U^(-w/2+ε) := by
  let δ := ε/(Bmask+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨C,hC,hbound⟩ := naturalSlot_excluded_sub_subpower δ hδ
  refine ⟨C,hC,?_⟩
  intro U hU χ R hR hRN pool hp β w B hB hβ
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hnorm : (R.absNorm : ℝ)^δ ≤ U^ε := by
    calc
      _ ≤ (U^Bmask)^δ := Real.rpow_le_rpow (Nat.cast_nonneg _) hRN hδ.le
      _ = U^(Bmask*δ) := (Real.rpow_mul hUp.le _ _).symm
      _ ≤ U^ε := Real.rpow_le_rpow_of_exponent_le hU (by
        have he : (Bmask+1)*δ=ε := by dsimp [δ]; field_simp
        nlinarith)
  apply (hbound χ R hR pool hp β (U^w) B hB hβ).trans
  calc
    _ ≤ (C*B)*U^ε*(Real.sqrt (U^w))⁻¹ := by gcongr
    _ = (C*B)*U^(-w/2+ε) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hUp.le,←Real.rpow_neg hUp.le,
        mul_assoc,←Real.rpow_add hUp]
      congr 2
      ring

theorem half_amplitude_of_deletion_error {x y : ℂ} {e : ℝ}
    (herror : ‖x-y‖ ≤ e) (he : e ≤ 1/2) (hx : 1 ≤ ‖x‖) :
    ‖x‖/2 ≤ ‖y‖ := by
  have htriangle := norm_add_le (x-y) y
  rw [sub_add_cancel] at htriangle
  linarith

theorem max_amplitude_of_deletion_error {x y : ℂ}
    (herror : ‖x-y‖ ≤ 1/2) : max 1 ‖x‖ ≤ 2*max 1 ‖y‖ := by
  have htriangle := norm_add_le (x-y) y
  rw [sub_add_cancel] at htriangle
  have h1 := le_max_left (1 : ℝ) ‖y‖
  have hy := le_max_right (1 : ℝ) ‖y‖
  apply max_le
  · linarith
  · linarith

end
end OAI.SevenEighths.Record12518109GainDeletion
#print axioms OAI.SevenEighths.Record12518109GainDeletion.naturalSlot_excluded_polynomial
