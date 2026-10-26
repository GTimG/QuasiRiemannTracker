/- Copyright (c) 2026 Sil. Apache-2.0.
Principal cancellation for the entire literal injective marked family.
Marked and ordinary factors retain their original annular normalizations,
natural character zeros, and common ordinary punctures.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.PrincipalMarkedMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.PrincipalMarked
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CenteredMomentLattice
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelRowProfiles KernelRowPools KernelRowExpansion KernelMarkedRows KernelLabelledSlots
open KernelAssignmentReindex KernelPunctureRows PrincipalMarkedMass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

def row (χ : Character) (S H : Finset PrimeIdeal) (pool : ι → Finset Id)
    (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  weightedSum (naturalCoefficients χ S pool β P)
    (fun slot => normalizedRow χ (supportedRectangle S b X₁ X₂)
      (restrictedValue S (augmented S H (marked S slot))) W₁ W₂ X₁ X₂)

theorem row_difference (χ : Character) (S H : Finset PrimeIdeal) (pool : ι → Finset Id)
    (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    row χ S H pool β P W₁ W₂ b X₁ X₂ - row χ S H pool β P W₁ W₂ b Y₁ Y₂ =
      weightedSum (naturalCoefficients χ S pool β P)
        (fun slot => normalizedRow χ (supportedRectangle S b X₁ X₂)
            (restrictedValue S (augmented S H (marked S slot))) W₁ W₂ X₁ X₂ -
          normalizedRow χ (supportedRectangle S b Y₁ Y₂)
            (restrictedValue S (augmented S H (marked S slot))) W₁ W₂ Y₁ Y₂) := by
  unfold row weightedSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro slot _
  split_ifs <;> ring

theorem uniform_marked (α B a b ε : ℝ) (hα : 0 ≤ α) (hα4 : α < 4/5)
    (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ (Q : Id), Q ≠ 0 → ∀ (W₁ W₂ : ℝ → ℂ),
      ∀ (hs₁ : Function.support W₁ ⊆ Set.Icc a b)
        (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
        (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂),
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ F : Id,
      F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^B → ∀ (S H : Finset PrimeIdeal),
      (∀ P ∈ S, Supported P.val) → (∀ P ∈ H, P.val ∣ F) →
      ∀ (η χ ψ : Character), (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B →
      Q ≤ ψ.modulus → CenteredExceptionalProfile.InducedBy χ ψ →
      (∀ I, ¬Supported I → idealCoeff χ I=0) →
      ∀ (m A₀ z : O), (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) →
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
      ‖row χ S H pool β P
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) b X₁ X₂ -
        row χ S H pool β P
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) b Y₁ Y₂‖ ≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖)^J*(∏ i, 256*M i)*Real.sqrt (T*∏ i, P i)*L^(-α) := by
  obtain ⟨n,hn⟩ := PrincipalUniform.uniform_rectangle α (2*B) a b ε hα hα4 (by positivity) ha hb hε
  refine ⟨n,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hn Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ F hF hcut S H hS hH η χ ψ hmod hQψ hind hχ m A₀ z hmLam hm2 hrow
    pool β P M hP hM hp hβ hV
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  let V₁ := normPowerProfile W₁ a b ha hs₁ hW₁ t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ hW₂ t₂
  let G (slot : ι → S) :=
    normalizedRow χ (supportedRectangle S b X₁ X₂)
        (restrictedValue S (augmented S H (marked S slot))) V₁ V₂ X₁ X₂ -
      normalizedRow χ (supportedRectangle S b Y₁ Y₂)
        (restrictedValue S (augmented S H (marked S slot))) V₁ V₂ Y₁ Y₂
  let K := C*Z^ε*(1+‖t₁‖+‖t₂‖)^n*Real.sqrt T*L^(-α)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hG (slot : ι → S) (_hi : Function.Injective slot)
      (hnz : (∏ i, naturalCoefficients χ S pool β P i (slot i)) ≠ 0) : ‖G slot‖ ≤ K := by
    have hpool := active_pool χ S pool β P slot hnz
    have hFslot := support_norm_bound F S slot P Z B hZ hcut
      (fun i => (hp i _ (hpool i)).2) hV
    have hm : (Ideal.absNorm χ.modulus : ℝ) ≤ Z^(2*B) :=
      hmod.trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
    exact hbound Z hZ (supportIdeal F S slot) (support_nonzero F hF S slot) hFslot
      S (augmented S H (marked S slot)) hS (support_divisor F S H slot hH)
      η χ ψ hm hQψ hind hχ m A₀ z hmLam hm2 hrow
      t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂
      hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  rw [row_difference]
  have hh := weighted_norm_le (naturalCoefficients χ S pool β P) G K hK hG
  apply hh.trans
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  calc
    _ ≤ K*∏ i, (256*M i)*Real.sqrt (P i) := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun p _ => norm_nonneg _))
        (fun i _ => prime_slot_mass χ S (pool i) (β i) (P i) (M i) (hP i) (hM i) (hp i) (hβ i))) hK
    _ = _ := by
      rw [Finset.prod_mul_distrib,Real.sqrt_mul hT.le,Real.sqrt_prod _ (fun i _ => (hP i).le)]
      dsimp only [K]
      ring

end
end Candidate.FourthPower.PrincipalMarked
