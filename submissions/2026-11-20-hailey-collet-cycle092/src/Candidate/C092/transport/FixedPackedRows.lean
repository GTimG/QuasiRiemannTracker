/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual packed fixed rows obey the sixth-power count. Pair it with the
unrestricted harmonic second-divisor mass before pricing the frame. -/
import Candidate.C092.transport.FixedPackingMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredExceptionalProfile ConcretePrimeRowBridge
open HeckeInverseAmplification IdealMobiusDivisorSum UniqueFactorizationMonoid
namespace QRH.Cycle092.FixedAllocationWeight
local notation "NZ" => HeckeInverseAmplification.NonzeroIdeal
local notation "O" => HeckeFamily.O

theorem packed_fixed_mass (Q : Ideal O) (hQ₀ : Q ≠ 0) (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (Mmax B ε : ℝ) (hMmax : 0 ≤ Mmax) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0<C ∧ ∀ U M : ℝ, 1 ≤ U → M ≤ Mmax →
      ∀ (η : Character) (m A : O), m ≠ 0 → A ≠ 0 → goodLambda ∣ m → (2:O) ∣ m →
      ∀ (rows : Finset O) (artificial : O → Finset NZ),
        (∀ y ∈ rows,y ≠ 0) → (∀ y ∈ rows,(Ideal.absNorm (Ideal.span {y}):ℝ) ≤ U^M) →
        (∀ y ∈ rows,FixedInducingRow η Q m A y) →
        (∀ y ∈ rows,∀ D ∈ artificial y,(D.val.absNorm:ℝ) ≤ U^B) →
        (∑ y ∈ rows, ((idealDivisors ((Ideal.span {y})^2)).card:ℝ)^3 *
          ∑ D ∈ artificial y,(D.val.absNorm:ℝ)⁻¹) ≤ C*U^(M/6+ε) := by
  obtain ⟨K,hK,hmass⟩ := original_H16 Mmax B ε hMmax hB hε
  let A₀ : ℝ := 768*(6:ℝ)^(normalizedFactors Q).toFinset.card
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  refine ⟨A₀*K,mul_pos hA₀ hK,?_⟩
  intro U M hU hM η m A hm hA hlam ht rows art hn hnorm hx hcap
  have hUp := zero_lt_one.trans_le hU
  have count := fixed_support_exceptional_count η Q hQ₀ hQt hQ72 m A hm hA hlam ht rows hn hx 1
    squarefree_one (by rw [normalizedFactors_one]; simp) U 1 M 0 hUp zero_le_one (by simp) (fun y hy => by simpa using hnorm y hy)
  have count' : (rows.card:ℝ) ≤ A₀*U^(M/6) := by simpa [A₀] using count
  calc
    _ ≤ ∑ _y ∈ rows,K*U^ε := by
      apply Finset.sum_le_sum; intro y hy
      exact hmass U hU y (hn y hy) ((hnorm y hy).trans (Real.rpow_le_rpow_of_exponent_le hU hM)) (art y) (hcap y hy)
    _ = (rows.card:ℝ)*(K*U^ε) := by simp
    _ ≤ (A₀*U^(M/6))*(K*U^ε) := mul_le_mul_of_nonneg_right count' (by positivity)
    _ = _ := by rw [Real.rpow_add hUp]; ring

/-- H.18 with the actual P.3 reference width and root cap. The additive
errors displayed in the frame relations can be budgeted before live rows. -/
theorem frame_excess {A₀ c u' a k M q l err : ℝ}
    (hA : A₀ ≤ 9179599/10000000) (hu : u' ≤ (QRH.SourceCertificate.u:ℝ))
    (ha : a ≤ A₀-c-u'+err) (hM : 2*a-k+q ≤ M+err)
    (hM' : M ≤ 2*a-k+q+err) (hmin : 1-6*u' ≤ M+err)
    (hl : max 0 (115/1000-c) ≤ l+err) :
    k+M/6-l-(a+q+u') ≤ -(3036/100000)+4*err := by
  have h := le_max_right 0 ((115/1000:ℝ)-c)
  norm_num [QRH.SourceCertificate.u] at hu
  linarith

#print axioms packed_fixed_mass
#print axioms frame_excess
end QRH.Cycle092.FixedAllocationWeight
