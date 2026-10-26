import Candidate.Cycle63.Marked.DeletionSlots
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily HeckePrimeAnnular HeckeDyadic
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentSecondHeightFamily
open CanonicalRowCompletion
local notation "O" => HeckeFamily.O

theorem annular_coefficient_bounds (W : ℝ → ℂ) (a b lo hi : ℝ) (ha : 0<a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : Continuous W) :
    ∃ B : ℝ, 0 < B ∧ ∀ (ν : Character) (P σ v t : ℝ), 0<P → lo≤σ → σ≤hi →
      ∀ I : Ideal O, I≠0 →
      ‖heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I‖ ≤ B := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨B,hB,?_⟩
  intro ν P σ v t hP hσlo hσhi I hI
  rw [heightCoefficient_norm _ _ _ hI]
  apply (show ‖idealCoeff ν I*annularWeight W P σ v I‖ ≤ ‖annularWeight W P σ v I‖ by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one ν I)).trans
  by_cases hz : W ((I.absNorm : ℝ)/P)=0
  · simp [annularWeight,hz,hB.le]
  · have hs := hWs hz
    rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
    simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσlo,hσhi⟩ _ hs

/-- Deleting polynomially bounded holes from an actual annular prime slot
has power-saving additive cost. The bound is uniform in both imaginary
shifts, the row character, the auxiliary character and the prime pool. -/
theorem annular_slot_deletion (W : ℝ → ℂ) (a b lo hi Bmask ε : ℝ)
    (ha : 0<a) (hWs : Function.support W ⊆ Set.Icc a b) (hW : Continuous W)
    (hBmask : 0 ≤ Bmask) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      ∀ (χ ν : Character) (R : Ideal O), R ≠ 0 → (R.absNorm : ℝ) ≤ U^Bmask →
      ∀ (pool : Finset (Ideal O)), (∀ I ∈ pool, Prime I) →
      ∀ (w σ v t : ℝ), lo ≤ σ → σ ≤ hi →
      let β := heightCoefficient (fun I => idealCoeff ν I *
        annularWeight W (U^w) σ v I) t
      ‖naturalSlot (excluded χ R) pool β (U^w) -
        naturalSlot χ pool β (U^w)‖ ≤ C * U^(-w/2+ε) := by
  obtain ⟨B,hB,hβ⟩ := annular_coefficient_bounds W a b lo hi ha hWs hW
  obtain ⟨C,hC,hdel⟩ := naturalSlot_excluded_polynomial Bmask ε hBmask hε
  refine ⟨C*B,mul_pos hC hB,?_⟩
  intro U hU χ ν R hR hRN pool hp w σ v t hσlo hσhi β
  exact hdel U hU χ R hR hRN pool hp β w B hB.le (fun I hI =>
    hβ ν (U^w) σ v t (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)
      hσlo hσhi I (hp I hI).ne_zero)

/-- The natural slot really is the normalized slot of the retained row
with its puncture mask, including the full height character. -/
theorem masked_natural_slot_eq {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R ≠ 0) (pool : Finset (Ideal O))
    (β : Ideal O → ℂ) (P t : ℝ) :
    naturalSlot (excluded F.character R) pool (heightCoefficient β t) P =
      normalizedSlot η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z pool β t P := by
  unfold naturalSlot normalizedSlot rowSlot
  congr 1
  refine Finset.sum_congr rfl fun I hI => ?_
  rw [F.masked_ideal R hR]
  simp only [heightCoefficient,one_mul]
  ring

/-- A sixth power in a row numerator is exactly prime deletion by its
root. This identity preserves the complete ideal coefficient, including
zeros and the bad-prime convention. -/
theorem naturalRow_sixth_ideal {η : Character} {z : O}
    (F : NaturalRow η z) (r : O) (hr : r ≠ 0)
    (Fr : NaturalRow η (z*r^6)) (I : Ideal O) :
    idealCoeff Fr.character I =
      idealCoeff (excluded F.character (Ideal.span {r})) I := by
  have hm : idealCoeff (excluded F.character (Ideal.span {r})) I =
      idealCoeff η I * idealRowHom ((fixedBadMask*r)^6*z) I := by
    simpa only [one_pow,mul_one] using
      HeckeRowClosure.idealCoeff_eq_row η (excluded F.character (Ideal.span {r}))
        (fixedBadMask*r) 1 z (F.masked_element_span r hr) I
  have he : (fixedBadMask*r)^6*z = fixedBadMask^6*(z*r^6) := by ring
  rw [Fr.ideal,hm,he]

/-- Ideal-coefficient dictionaries transport the entire slot and its
height and annular coefficients, without changing any normalization. -/
theorem naturalSlot_congr_ideal (χ χ' : Character)
    (hχ : ∀ I : Ideal O, idealCoeff χ I = idealCoeff χ' I)
    (pool : Finset (Ideal O)) (β : Ideal O → ℂ) (P : ℝ) :
    naturalSlot χ pool β P = naturalSlot χ' pool β P := by
  unfold naturalSlot
  congr 1
  refine Finset.sum_congr rfl fun I hI => ?_
  rw [hχ I]

/-- Successive punctures are deletion by the product ideal. This lets
the exact arithmetic dictionary and a sixth-root mask share one uniform
norm budget. -/
theorem excluded_twice_ideal (χ : Character) (R A : Ideal O)
    (hR : R ≠ 0) (hA : A ≠ 0) (I : Ideal O) :
    idealCoeff (excluded (excluded χ R) A) I =
      idealCoeff (excluded χ (R*A)) I := by
  rw [excluded_ideal _ A hA,excluded_ideal _ R hR,
    excluded_ideal _ (R*A) (mul_ne_zero hR hA),IsCoprime.mul_right_iff]
  split_ifs <;> tauto

/-- The sixth-power row identity remains exact with every outer puncture.
No coprimality condition on the root and the puncture is needed. -/
theorem naturalRow_sixth_masked_ideal {η : Character} {z : O}
    (F : NaturalRow η z) (r : O) (hr : r ≠ 0)
    (Fr : NaturalRow η (z*r^6)) (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    idealCoeff (excluded Fr.character R) I =
      idealCoeff (excluded F.character ((Ideal.span {r})*R)) I := by
  calc
    _ = idealCoeff (excluded (excluded F.character (Ideal.span {r})) R) I := by
      rw [excluded_ideal _ R hR,excluded_ideal _ R hR,
        naturalRow_sixth_ideal F r hr Fr I]
    _ = _ := excluded_twice_ideal F.character (Ideal.span {r}) R
      (Ideal.span_singleton_eq_bot.not.mpr hr) hR I

end
end OAI.SevenEighths.Deletion26
