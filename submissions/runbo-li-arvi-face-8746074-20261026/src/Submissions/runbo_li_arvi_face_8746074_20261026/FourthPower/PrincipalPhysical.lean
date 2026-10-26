/- Copyright (c) 2026 Sil. Apache-2.0.
Principal cancellation for the literal physical row, with no auxiliary
character-existence or cancellation assumption. The fixed-inducing condition
is exactly the baseline's condition on the actual row parameter.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.PrincipalMarked

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.PrincipalPhysical
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CenteredMomentLattice
open CenteredMomentHeckeVolume ConcretePrimeRowBridge
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelRowProfiles KernelRowPools KernelRowExpansion KernelMarkedRows KernelLabelledSlots
open KernelAssignmentReindex KernelPunctureRows
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

def coefficient (η : Character) (m A z : O) (I : Id) : ℂ :=
  idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I

def row (η : Character) (m A z : O) (S H : Finset PrimeIdeal)
    (pool : ι → Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  weightedSum (fun i p => if p.val.val ∈ pool i then
    (Real.sqrt (P i) : ℂ)⁻¹*coefficient η m A z p.val.val*β i p.val.val else 0)
    (fun slot : ι → S => (Real.sqrt (X₁*X₂) : ℂ)⁻¹ *
      ∑ n ∈ supportedRectangle S b X₁ X₂,
        restrictedValue S (augmented S H (marked S slot)) n *
          coefficient η m A z (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n)

theorem character_coefficient (η χ : Character) (m A z : O)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A*z) n) (I : Id) :
    idealCoeff χ I=coefficient η m A z I := by
  simpa only [coefficient,one_pow,mul_one] using
    HeckeRowClosure.idealCoeff_eq_row η χ m 1 (A*z) hrow I

theorem character_off_supported (η χ : Character) (m A z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A*z) n) :
    ∀ I, ¬Supported I → idealCoeff χ I=0 := by
  intro I hI
  by_cases hz : I=0
  · simp only [hz,map_zero]
  have hn := idealGenerator_ne_zero I hz
  have hs : ¬Supported (Ideal.span {idealGenerator I}) := by
    simpa only [span_idealGenerator] using hI
  rw [← span_idealGenerator I,idealCoeff_span χ hn,hrow]
  exact CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hs

theorem row_eq_character (η χ : Character) (m A z : O)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A*z) n)
    (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (β : ι → Id → ℂ)
    (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    row η m A z S H pool β P W₁ W₂ b X₁ X₂ =
      PrincipalMarked.row χ S H pool β P W₁ W₂ b X₁ X₂ := by
  unfold row PrincipalMarked.row naturalCoefficients KernelNaturalSlots.slotTerm
    normalizedRow pairCharacter
  simp_rw [character_coefficient η χ m A z hrow]

theorem uniform_physical (α B a b ε : ℝ) (hα : 0 ≤ α) (hα4 : α < 4/5)
    (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ (Q : Id), Q ≠ 0 → ∀ (W₁ W₂ : ℝ → ℂ),
      ∀ (hs₁ : Function.support W₁ ⊆ Set.Icc a b)
        (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
        (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂),
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ F : Id,
      F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^B → ∀ (S H : Finset PrimeIdeal),
      (∀ P ∈ S, Supported P.val) → (∀ P ∈ H, P.val ∣ F) →
      ∀ (η : Character) (m A z : O), m ≠ 0 → A ≠ 0 → z ≠ 0 →
      (goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z) : ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
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
      ‖row η m A z S H pool β P
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) b X₁ X₂ -
        row η m A z S H pool β P
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) b Y₁ Y₂‖ ≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖)^J*(∏ i, 256*M i)*Real.sqrt (T*∏ i, P i)*L^(-α) := by
  obtain ⟨n,hn⟩ := PrincipalMarked.uniform_marked (ι := ι) α B a b ε hα hα4 hB ha hb hε
  refine ⟨n,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hn Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ F hF hcut S H hS hH η m A z hm hA hz hmLam hm2 hcond hex
    pool β P M hP hM hp hβ hV
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  obtain ⟨χ,ψ,hmod,_,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A z
    hm hA hz hmLam hm2 hex
  have hm' : (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B :=
    (show (Ideal.absNorm χ.modulus : ℝ) ≤
      (HeckeRowClosure.rowConductorBound η m 1 (A*z) : ℝ) by exact_mod_cast hmod).trans hcond
  rw [row_eq_character η χ m A z hrow,row_eq_character η χ m A z hrow]
  exact hbound Z hZ F hF hcut S H hS hH η χ ψ hm' hQψ hind
    (character_off_supported η χ m A z hmLam hm2 hrow) m A z hmLam hm2 hrow
    pool β P M hP hM hp hβ hV
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose

end
end Candidate.FourthPower.PrincipalPhysical
