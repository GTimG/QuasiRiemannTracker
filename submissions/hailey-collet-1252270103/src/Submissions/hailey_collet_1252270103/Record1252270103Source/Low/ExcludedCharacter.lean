/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceDictionary

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentFixedRowMask CenteredExceptionalProfile
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist
local notation "O" => HeckeFamily.O

/-- The literal ideal coefficient keeps every zero of the original character. -/
theorem excluded_character_ideal (χ : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I=idealCoeff χ I*(if IsCoprime I R then 1 else 0) := by
  rw [excluded_ideal χ R hR I]
  split_ifs <;> simp only [mul_one,mul_zero]

theorem excluded_character_element (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      elementCoeff χ n*(if IsCoprime (Ideal.span {n}) R then 1 else 0) := by
  rw [excluded_element χ hχ0 R hR n]
  split_ifs <;> simp only [mul_one,mul_zero]

/-- Enlarging the modulus by the exclusion radical preserves the SAME
inducing character. This does not assert equality of the two moduli. -/
theorem excluded_character_induced (χ ψ : Character) (R : Ideal O)
    (hind : InducedBy χ ψ) : InducedBy (excluded χ R) ψ := by
  intro I
  have hm : idealCoeff (excluded χ R) I=
      if IsCoprime I (excluded χ R).modulus then idealCoeff χ I else 0 :=
    excludePrimes_mask χ _ (support_prime R) I
  rw [hm]
  by_cases hc : IsCoprime I (excluded χ R).modulus
  · have hd : χ.modulus∣(excluded χ R).modulus :=
      ⟨∏P∈CompletedGauss.primeSupport R,P,rfl⟩
    have hcχ : IsCoprime I χ.modulus := hc.of_isCoprime_of_dvd_right hd
    simp only [ite_eq_left hc,hind I,ite_eq_left hcχ]
  · simp only [ite_eq_right hc]

theorem original_row_element_zero (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) :
    elementCoeff χ 0=0 := by
  rw [hrow]
  change elementHom η 0*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {(0:O)})=0
  rw [Ideal.span_singleton_zero]
  change elementHom η 0*idealRowHom (m^6*1^4*(A*z)) (0:Ideal O)=0
  rw [(idealRowHom (m^6*1^4*(A*z))).map_zero,mul_zero]

/-- Original row representation with only the literal mask m multiplied by
the chosen ideal generator. The base character, A and z are unchanged. -/
theorem excluded_character_row (η χ : Character) (m A z : O)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (R : Ideal O) (hR : R≠0) :
    ∀n,elementCoeff (excluded χ R) n=
      rowTwist (elementHom η) (m*idealGenerator R) 1 (A*z) n := by
  intro n
  rw [excluded_element_generator χ (original_row_element_zero η χ m A z hrow) R hR n,hrow]
  exact (row_mask_mul η m (idealGenerator R) A z n hml hm2).symm

theorem excluded_character_row_ideal (η χ : Character) (m A z : O)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I=
      idealCoeff η I*idealRowHom ((m*idealGenerator R)^6*(A*z)) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η (excluded χ R)
    (m*idealGenerator R) 1 (A*z) (excluded_character_row η χ m A z hml hm2 hrow R hR) I

theorem excluded_character_plain (η χ : Character) (m A z : O)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (t X : ℝ) :
    rowTwistedSum η (m*idealGenerator R) A z W t X=
      twistedIdealSum (excluded χ R) W t X :=
  rowTwistedSum_eq η (excluded χ R) (m*idealGenerator R) A z
    (excluded_character_row η χ m A z hml hm2 hrow R hR) W t X

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.excluded_character_ideal
#print axioms QRH.Record1252270103Low.excluded_character_element
#print axioms QRH.Record1252270103Low.excluded_character_induced
#print axioms QRH.Record1252270103Low.excluded_character_row
#print axioms QRH.Record1252270103Low.excluded_character_plain
