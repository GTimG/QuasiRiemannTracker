/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The prime polynomial, annular profile bound and normalized slot are the genuine
OpenAI definitions, with all original character and row phases preserved. -/
import Candidate.C092.transport.CofactorPrimeCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeSlot

set_option autoImplicit false
namespace QRH.Cycle092.CofactorPrime
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ProbePhysical
open HeckeFamily HeckeDyadic HeckePrimeAnnular
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
local notation "O" => ActualEisensteinCubic.O

def puncturedPool (S : Finset (Ideal O)) (B : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I=>¬I∣B)
def deletedPool (S : Finset (Ideal O)) (B : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I=>I∣B)
def activeDeleted (S : Finset (Ideal O)) (B : Ideal O) (W : ℝ→ℂ) (P : ℝ) : Finset (Ideal O) :=
  S.filter (fun I=>I∣B ∧ W ((I.absNorm : ℝ)/P) ≠ 0)
def slotCoefficient (χ : Character) (W : ℝ→ℂ) (P σ freq : ℝ) (I : Ideal O) : ℂ :=
  idealCoeff χ I*annularWeight W P σ freq I

/-- The clean prime pool is its genuine punctured pool plus the deleted terms. -/
theorem rowSlot_deletion (η : Character) (m A z : O) (S : Finset (Ideal O))
    (B : Ideal O) (β : Ideal O→ℂ) (t : ℝ) :
    rowSlot η m A z S β t-rowSlot η m A z (puncturedPool S B) β t =
      rowSlot η m A z (deletedPool S B) β t := by
  have h : rowSlot η m A z S β t = rowSlot η m A z (deletedPool S B) β t+
      rowSlot η m A z (puncturedPool S B) β t := by
    simp only [rowSlot,puncturedPool,deletedPool,Finset.sum_filter]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I _
    by_cases hI : I∣B <;> simp [hI]
  exact sub_eq_iff_eq_add.mpr h

/-- Zero profile terms are removed exactly, before applying an annular lower
norm. This keeps the smaller zero terms present in primePool from being counted. -/
theorem deleted_eq_active (η χ : Character) (m A z : O) (S : Finset (Ideal O))
    (B : Ideal O) (W : ℝ→ℂ) (P σ freq t : ℝ) :
    rowSlot η m A z (deletedPool S B) (slotCoefficient χ W P σ freq) t =
      rowSlot η m A z (activeDeleted S B W P) (slotCoefficient χ W P σ freq) t := by
  simp only [rowSlot,deletedPool,activeDeleted,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I _
  by_cases hI : I∣B <;> by_cases hw : W ((I.absNorm : ℝ)/P)=0 <;>
    simp [hI,hw,slotCoefficient,annularWeight]

/-- Exact normalized original prime polynomial deletion, retaining the actual
character, moving row, annular powers and independent heights. -/
theorem normalizedSlot_deletion (η χ : Character) (m A z : O) (S : Finset (Ideal O))
    (B : Ideal O) (W : ℝ→ℂ) (P σ freq t : ℝ) :
    normalizedSlot η m A z S (slotCoefficient χ W P σ freq) t P-
      normalizedSlot η m A z (puncturedPool S B) (slotCoefficient χ W P σ freq) t P =
      normalizedSlot η m A z (activeDeleted S B W P) (slotCoefficient χ W P σ freq) t P := by
  simp only [normalizedSlot,←mul_sub,rowSlot_deletion,deleted_eq_active]

/-- The fixed profile bound is a proved compactness estimate, uniform before
all characters, arithmetic cofactors, scales, and independent slot heights. -/
theorem coefficient_bound (W : ℝ→ℂ) (hW : Continuous W) {a b : ℝ}
    (ha : 0 < a) (hWs : Function.support W ⊆ Set.Icc a b) (lo hi : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character) (P σ freq : ℝ), σ∈Set.Icc lo hi →
      ∀ I : Ideal O, ‖slotCoefficient χ W P σ freq I‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨C,hC,?_⟩
  intro χ P σ freq hσ I
  have hw : ‖annularWeight W P σ freq I‖ ≤ C := by
    by_cases hz : W ((I.absNorm : ℝ)/P)=0
    · simpa [annularWeight,hz] using hC.le
    · have hs := hWs hz
      have hy : 0 < (I.absNorm : ℝ)/P := ha.trans_le hs.1
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simpa only [Complex.neg_re,shift_re] using hbound σ hσ _ hs
  rw [slotCoefficient,norm_mul]
  exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one χ I) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hw)

theorem rowSlot_card_bound (η : Character) (m A z : O) (E : Finset (Ideal O))
    (β : Ideal O→ℂ) (t C : ℝ) (hC : 0 ≤ C)
    (hprime : ∀ I∈E,Prime I) (hβ : ∀ I∈E,‖β I‖ ≤ C) :
    ‖rowSlot η m A z E β t‖ ≤ C*(E.card : ℝ) := by
  unfold rowSlot
  calc
    _ ≤ ∑ I∈E,‖β I*(idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
        (I.absNorm : ℂ)^(Complex.I*t)‖ := norm_sum_le _ _
    _ ≤ ∑ I∈E,C := by
      apply Finset.sum_le_sum
      intro I hI
      rw [mul_assoc,norm_mul]
      exact (mul_le_mul (hβ I hI)
        (row_twisted_coefficient_norm η m A z t I (hprime I hI).ne_zero)
        (norm_nonneg _) hC).trans_eq (mul_one C)
    _ = _ := by simp [mul_comm]

/-- K.3's genuine normalized deleted-prime bound. The constant is fixed before
the cofactor, original row, live scale and every frequency. No deleted-mask
smoothness or coefficient envelope is assumed. Positive scale is explicit;
zero-width pools are outside this asymptotic assertion. -/
theorem normalized_annular_deletion (W : ℝ→ℂ) (hW : Continuous W) {a b : ℝ}
    (ha : 0 < a) (hWs : Function.support W ⊆ Set.Icc a b) (lo hi : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η χ : Character) (m A z : O) (S : Finset (Ideal O))
      (B : Ideal O) (U P exponent σ freq t : ℝ),
      (∀ I∈S,Prime I) → B ≠ 0 → 0 < U → 1 < P → (a⁻¹)^2 ≤ P →
      (B.absNorm : ℝ) ≤ U^exponent → σ∈Set.Icc lo hi →
      ‖normalizedSlot η m A z S (slotCoefficient χ W P σ freq) t P-
        normalizedSlot η m A z (puncturedPool S B) (slotCoefficient χ W P σ freq) t P‖ ≤
        (C/Real.sqrt P)*(2*exponent*Real.log U/Real.log P) := by
  obtain ⟨C,hC,hcoef⟩ := coefficient_bound W hW ha hWs lo hi
  refine ⟨C,hC,?_⟩
  intro η χ m A z S B U P exponent σ freq t hprime hB hU hP hscale hBcap hσ
  let E := activeDeleted S B W P
  have hE (I : Ideal O) (hI : I∈E) : I∈S ∧ I∣B ∧ W ((I.absNorm : ℝ)/P) ≠ 0 :=
    Finset.mem_filter.mp hI
  have hp : ∀ I∈E,Prime I := fun I hI=>hprime I (hE I hI).1
  have hd : ∀ I∈E,I∣B := fun I hI=>(hE I hI).2.1
  have hl : ∀ I∈E,a*P ≤ (I.absNorm : ℝ) := by
    intro I hI
    have hs := hWs (hE I hI).2.2
    exact (le_div_iff₀ (zero_lt_one.trans hP)).mp hs.1
  have hcard := annular_card_log E hB ha hP hU hscale hBcap hp hd hl
  have hrow := rowSlot_card_bound η m A z E (slotCoefficient χ W P σ freq) t C hC.le hp
    (fun I _=>hcoef χ P σ freq hσ I)
  have hfactor : ‖(Real.sqrt P : ℂ)⁻¹‖=(Real.sqrt P)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg P)]
  rw [normalizedSlot_deletion,normalizedSlot,norm_mul,hfactor]
  calc
    _ ≤ (Real.sqrt P)⁻¹*(C*(E.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hrow (inv_nonneg.mpr (Real.sqrt_nonneg P))
    _ = (C/Real.sqrt P)*(E.card : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard (div_nonneg hC.le (Real.sqrt_nonneg P))

end
end QRH.Cycle092.CofactorPrime
#print axioms QRH.Cycle092.CofactorPrime.normalized_annular_deletion
