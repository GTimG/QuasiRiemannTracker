/- Copyright (c) 2026 Sil. Apache-2.0.
Fresh squarefree cubic parameters preserve the natural zeros and force the
fourth-power row divisor. This identifies the new parameter with the actual
baseline count, rather than assuming a saving from an abstract ledger.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.PrincipalExceptional

set_option autoImplicit false
namespace Candidate.FourthPower.PrincipalCubic
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge UniqueFactorizationMonoid CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem coefficient_cubic (η : Character) (m A d z : O) (I : Id) (hI : Supported I) :
    PrincipalPhysical.coefficient η m (A*d^2) z I =
      PrincipalPhysical.coefficient η m A z I*(idealRowHom d I)^2 := by
  unfold PrincipalPhysical.coefficient
  have he : m^6*((A*d^2)*z) = (m^6*(A*z))*d^2 := by ring
  rw [he,idealRowHom_argument_mul,idealRowHom_argument_pow d 2 I hI]
  ring

theorem fresh_valuation (F D : Id) (hF : F ≠ 0) (hD : Squarefree D)
    (hc : IsCoprime F D) (P : Id) (hP : P ∈ normalizedFactors D) :
    valuation (F*D^2) P = 2 := by
  have hp := prime_of_normalized_factor P hP
  have hz : valuation F P=0 := by
    apply Multiset.count_eq_zero.mpr
    intro hf
    exact hp.not_isUnit (hc.isRelPrime (dvd_of_mem_normalizedFactors hf)
      (dvd_of_mem_normalizedFactors hP))
  have hlow : 0 < valuation D P := Multiset.count_pos.mpr hP
  have hhigh : valuation D P ≤ 1 := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD) P
  have hone : valuation D P=1 := by omega
  rw [valuation_mul _ _ _ hF (pow_ne_zero _ hD.ne_zero),valuation_pow,hz,hone]

theorem fresh_element_valuation (A d : O) (hA : A ≠ 0)
    (hd : Squarefree (Ideal.span {d})) (hc : IsCoprime (Ideal.span {A}) (Ideal.span {d}))
    (P : Id) (hP : P ∈ normalizedFactors (Ideal.span {d})) :
    valuation (Ideal.span {A*d^2}) P % 6 = 2 := by
  rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    fresh_valuation _ _ (Ideal.span_singleton_eq_bot.not.mpr hA) hd hc P hP]

theorem forced_fourth_power (η : Character) (Q : Id) (hQ : Q ≠ ⊤)
    (hQ72 : Q ≤ Ideal.span {(72:O)}) (m A d z : O)
    (hm : m ≠ 0) (hA : A ≠ 0) (hd : d ≠ 0) (hz : z ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hD : Squarefree (Ideal.span {d})) (hc : IsCoprime (Ideal.span {A}) (Ideal.span {d}))
    (hgood : ∀ P ∈ normalizedFactors (Ideal.span {d}), goodLambda ∉ P ∧ (2:O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P)
    (hex : CenteredExceptionalProfile.FixedInducingRow η Q m (A*d^2) z) :
    (Ideal.span {d})^4 ∣ sixthRemainder (Ideal.span {z}) ∧
      (Ideal.absNorm (Ideal.span {d}) : ℝ)^4 ≤ Ideal.absNorm (sixthRemainder (Ideal.span {z})) := by
  obtain ⟨χ,ψ,_,hind,hQψ,hrow⟩ := hex
  apply CenteredExceptionalProfile.actual_forced_fourth_power η χ ψ hind Q hQ hQ72 hQψ
    m (A*d^2) z hm (mul_ne_zero hA (pow_ne_zero _ hd)) hz hmLam hm2 hrow
    (Ideal.span {d}) hD
  intro P hP
  obtain ⟨hlam,h2,hQP,hηP⟩ := hgood P hP
  exact ⟨hlam,h2,hQP,hηP,fresh_element_valuation A d hA hD hc P hP⟩

/-- The exponent is the literal M/6-(2/3)δ when N(d) >= Z^δ.
It comes from the original fixed-support count and the fresh-squarefree
calculation above, including all natural-zero coprimality conditions. -/
theorem fresh_count (η : Character) (Q : Id) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤)
    (hQ72 : Q ≤ Ideal.span {(72:O)}) (m A d : O)
    (hm : m ≠ 0) (hA : A ≠ 0) (hd : d ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hD : Squarefree (Ideal.span {d})) (hc : IsCoprime (Ideal.span {A}) (Ideal.span {d}))
    (hgood : ∀ P ∈ normalizedFactors (Ideal.span {d}), goodLambda ∉ P ∧ (2:O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow η Q m (A*d^2) z)
    (Z C M δ : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z^δ ≤ (Ideal.absNorm (Ideal.span {d}) : ℝ))
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C*Z^M) :
    (rows.card : ℝ) ≤ 768*(6:ℝ)^(normalizedFactors Q).toFinset.card*C^(1/6:ℝ)*
      Z^(M/6-(2/3)*δ) := by
  have hval (P : Id) (hP : P ∈ normalizedFactors (Ideal.span {d})) :=
    fresh_element_valuation A d hA hD hc P hP
  have h := CenteredExceptionalProfile.fixed_support_exceptional_count η Q hQ0 hQ hQ72
    m (A*d^2) hm (mul_ne_zero hA (pow_ne_zero _ hd)) hmLam hm2 rows hrows hex
    (Ideal.span {d}) hD (fun P hP =>
      ⟨(hgood P hP).1,(hgood P hP).2.1,(hgood P hP).2.2.1,(hgood P hP).2.2.2,hval P hP⟩)
    Z C M (2*δ) hZ hC (by simpa only [mul_div_cancel_left₀ δ (by norm_num : (2:ℝ)≠0)] using hDnorm) hN
  rw [show (M-2*(2*δ))/6=M/6-(2/3)*δ by ring] at h
  exact h

end
end Candidate.FourthPower.PrincipalCubic
