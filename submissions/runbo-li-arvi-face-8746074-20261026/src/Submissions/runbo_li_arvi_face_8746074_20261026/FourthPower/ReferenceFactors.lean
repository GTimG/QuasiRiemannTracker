/- Copyright (c) 2026 Sil. Apache-2.0.
Checked concrete factors for the common-column reference: actual smooth
Hecke polynomials, naturally normalized marked slots, and fixed twists.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.ReferenceCoefficients

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceFactors
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentCommonMaskExpansion
open ReferenceCoefficients
local notation "Id" => Ideal HeckeFamily.O

structure Factor where
  pool : Finset Id
  coefficient : Id → ℂ
  length : ℝ
  amplitude : ℝ
  length_nonneg : 0 ≤ length
  amplitude_nonneg : 0 ≤ amplitude
  support_bound : ∀ I ∈ pool, (Ideal.absNorm I : ℝ) ≤ length
  coefficient_bound : ∀ I ∈ pool,
    ‖coefficient I‖ ≤ amplitude/Real.sqrt (Ideal.absNorm I : ℝ)

namespace Factor
def value (F : Factor) (χ : Character) : ℂ := ∑ I ∈ F.pool, F.coefficient I*idealCoeff χ I

def smooth (W : ℝ → ℂ) (b B X v : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hX : 0 < X)
    (hW : ∀ x, ‖W x‖ ≤ B) : Factor where
  pool := idealBall (b*X)
  coefficient := phaseCoefficient W X v
  length := b*X
  amplitude := Real.sqrt b*B
  length_nonneg := mul_nonneg hb hX.le
  amplitude_nonneg := mul_nonneg (Real.sqrt_nonneg b) hB
  support_bound I hI := (mem_idealBall _ _ |>.mp hI).2
  coefficient_bound I hI := phase_coefficient_bound W X v b B hX hb hB I
    (mem_idealBall _ _ |>.mp hI).1 (mem_idealBall _ _ |>.mp hI).2 (hW _)

theorem smooth_value (W : ℝ → ℂ) (b B X v : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hX : 0 < X)
    (hW : ∀ x, ‖W x‖ ≤ B) (hs : Function.support W ⊆ Set.Iic b) (χ : Character) :
    (smooth W b B X v hb hB hX hW).value χ =
      HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*v) := by
  symm
  exact phase_polynomial_finite χ W X v hX (idealBall (b*X))
    (fun I hI => (mem_idealBall _ _ |>.mp hI).1)
    (fun I hI hw => (mem_idealBall _ _).mpr ⟨hI,(div_le_iff₀ hX).mp (hs hw)⟩)

def marked (pool : Finset Id) (β : Id → ℂ) (P B : ℝ) (hP : 0 < P) (hB : 0 ≤ B)
    (hp : ∀ I ∈ pool, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ 2*P)
    (hβ : ∀ I ∈ pool, ‖β I‖ ≤ B) : Factor where
  pool := pool
  coefficient I := (Real.sqrt P : ℂ)⁻¹*β I
  length := 2*P
  amplitude := Real.sqrt 2*B
  length_nonneg := by positivity
  amplitude_nonneg := mul_nonneg (Real.sqrt_nonneg 2) hB
  support_bound I hI := (hp I hI).2
  coefficient_bound I hI := by
    have hh := phase_coefficient_bound (fun _ => β I) P 0 2 B hP (by norm_num) hB I
      (hp I hI).1 (hp I hI).2 (hβ I hI)
    simpa only [phaseCoefficient,norm_mul,FourierBridge.logPhase_norm,mul_one] using hh

theorem marked_value (pool : Finset Id) (β : Id → ℂ) (P B : ℝ) (hP : 0 < P) (hB : 0 ≤ B)
    (hp : ∀ I ∈ pool, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ 2*P)
    (hβ : ∀ I ∈ pool, ‖β I‖ ≤ B) (χ : Character) :
    (marked pool β P B hP hB hp hβ).value χ = naturalSlot χ pool β P := by
  unfold value marked naturalSlot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

def twist (F : Factor) (τ : Id → ℂ) (hτ : ∀ I ∈ F.pool, ‖τ I‖ ≤ 1) : Factor where
  pool := F.pool
  coefficient I := F.coefficient I*τ I
  length := F.length
  amplitude := F.amplitude
  length_nonneg := F.length_nonneg
  amplitude_nonneg := F.amplitude_nonneg
  support_bound := F.support_bound
  coefficient_bound I hI := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hτ I hI)).trans (F.coefficient_bound I hI)

theorem twist_character_value (F : Factor) (η χ : Character) :
    (F.twist (idealCoeff η) (fun I _ => idealCoeff_norm_le_one η I)).value χ =
      F.value (η.product χ) := by
  unfold value twist
  apply Finset.sum_congr rfl
  intro I _
  rw [idealCoeff_product]
  ring

end Factor
end
end Candidate.FourthPower.ReferenceFactors
