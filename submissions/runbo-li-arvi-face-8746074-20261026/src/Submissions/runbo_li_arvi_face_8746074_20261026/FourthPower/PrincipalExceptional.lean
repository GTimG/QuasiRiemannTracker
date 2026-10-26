/- Copyright (c) 2026 Sil. Apache-2.0.
The actual fixed-inducing family: combine the proved restricted marked
cancellation with the baseline's forced-fourth-power row count. No row
amplitude, family energy, or cardinality estimate is left as a hypothesis.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.PrincipalPhysical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.PrincipalExceptional
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CenteredMomentLattice
open ConcretePrimeRowBridge UniqueFactorizationMonoid CenteredExceptionalCount
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open PrincipalPhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

/-- The support and its common ordinary punctures may vary with the row.
The profiles, slot coefficients, physical lengths and normalizations are
the original ones. The prime valuations force the actual fourth-power
divisor in the sixth-free row remainder; they are not a counting axiom. -/
theorem uniform_energy (α B a b ε : ℝ) (hα : 0 ≤ α) (hα4 : α < 4/5)
    (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ (Q : Id), Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72:O)} →
      ∀ (W₁ W₂ : ℝ → ℂ),
      ∀ (hs₁ : Function.support W₁ ⊆ Set.Icc a b)
        (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
        (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂),
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ (η : Character) (m A : O), m ≠ 0 → A ≠ 0 →
      (goodLambda ∣ m) → ((2:O) ∣ m) → ∀ rows : Finset O,
      (∀ z ∈ rows, z ≠ 0) →
      (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow η Q m A z) →
      (∀ z ∈ rows, (HeckeRowClosure.rowConductorBound η m 1 (A*z) : ℝ) ≤ Z^B) →
      ∀ D : Id, Squarefree D →
      (∀ P ∈ normalizedFactors D, goodLambda ∉ P ∧ (2:O) ∉ P ∧
        IsCoprime Q P ∧ IsCoprime η.modulus P ∧ CenteredExceptionalCount.valuation (Ideal.span {A}) P % 6 = 2) →
      ∀ Cr R g : ℝ, 0 ≤ Cr → Z^(g/2) ≤ (Ideal.absNorm D : ℝ) →
      (∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr*Z^R) →
      ∀ (F : O → Id) (S : Finset PrimeIdeal) (H : O → Finset PrimeIdeal),
      (∀ z ∈ rows, F z ≠ 0 ∧ (Ideal.absNorm (F z) : ℝ) ≤ Z^B) →
      (∀ P ∈ S, Supported P.val) → (∀ z ∈ rows, ∀ P ∈ H z, P.val ∣ F z) →
      ∀ (pool : ι → Finset Id) (β : ι → Id → ℂ) (P M : ι → ℝ),
      (∀ i, 0 < P i) → (∀ i, 0 ≤ M i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ M i) → (∏ i, 2*P i) ≤ Z^B →
      ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ →
      X₁ ≤ U₁ → X₂ ≤ U₂ → Y₁ ≤ U₁ → Y₂ ≤ U₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∀ I, Supported I →
        ((Ideal.absNorm I : ℝ) ≤ b*U₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*U₂) →
        primeSupport I ⊆ primeValues S) →
      (∑ z ∈ rows, ‖row η m A z S (H z) pool β P
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) b X₁ X₂ -
        row η m A z S (H z) pool β P
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) b Y₁ Y₂‖^2) ≤
        (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*Z^((R-2*g)/6))*
          (C*Z^ε*(1+‖t₁‖+‖t₂‖)^J*(∏ i, 256*M i)*Real.sqrt (T*∏ i, P i)*L^(-α))^2 := by
  obtain ⟨n,hn⟩ := uniform_physical (ι := ι) α B a b ε hα hα4 hB ha hb hε
  refine ⟨n,?_⟩
  intro Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hn Q hQ0 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A hm hA hmLam hm2 rows hrows hex hcond D hD hgood Cr R g hCr hDnorm hN
    F S H hF hS hH pool β P M hP hM hp hβ hV
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  have hc := CenteredExceptionalProfile.fixed_support_exceptional_count η Q hQ0 hQ hQ72
    m A hm hA hmLam hm2 rows hrows hex D hD hgood Z Cr R g (zero_lt_one.trans_le hZ) hCr hDnorm hN
  let K := C*Z^ε*(1+‖t₁‖+‖t₂‖)^n*(∏ i, 256*M i)*Real.sqrt (T*∏ i, P i)*L^(-α)
  have hbound' (z : O) (hz : z ∈ rows) :
      ‖row η m A z S (H z) pool β P
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) b X₁ X₂ -
        row η m A z S (H z) pool β P
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) b Y₁ Y₂‖ ≤ K :=
    hbound Z hZ (F z) (hF z hz).1 (hF z hz).2 S (H z) hS (hH z hz)
      η m A z hm hA (hrows z hz) hmLam hm2 (hcond z hz) (hex z hz)
      pool β P M hP hM hp hβ hV
      t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  calc
    _ ≤ ∑ _z ∈ rows, K^2 := Finset.sum_le_sum (fun z hz =>
      pow_le_pow_left₀ (norm_nonneg _) (hbound' z hz) 2)
    _ = (rows.card : ℝ)*K^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg K)

end
end Candidate.FourthPower.PrincipalExceptional
