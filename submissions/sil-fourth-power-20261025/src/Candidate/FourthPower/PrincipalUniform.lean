/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform principal cancellation for the actual fifth-free rows, with two
independent ordinary heights and all positive shortened scales. Only the
baseline's quantitative lattice-volume control is reused.
-/
import Candidate.FourthPower.PrincipalRestricted
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDegree

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.PrincipalUniform
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation CenteredMomentLattice CenteredMomentTwist
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelRowProfiles KernelRowPools KernelRowExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem profile_zero (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) :
    normPowerProfile W a b ha hs (W.smooth ⊤) 0=W := by
  ext x
  simp only [normPowerProfile_apply,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,one_mul]

/-- All constants precede the ambient scale, conductor, common support,
marked-prime choices, ordinary lengths, and both heights. -/
theorem uniform_rectangle (α B a b ε : ℝ) (hα : 0 ≤ α) (hα4 : α < 4/5)
    (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ (Q : Id), Q ≠ 0 → ∀ (W₁ W₂ : ℝ → ℂ),
      ∀ (hs₁ : Function.support W₁ ⊆ Set.Icc a b)
        (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
        (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂),
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ F : Id,
      F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^B →
      ∀ (S : Finset PrimeIdeal) (live : S → Bool),
      (∀ P ∈ S, Supported P.val) → (∀ P : S, live P=true → P.val.val ∣ F) →
      ∀ (η χ ψ : Character), (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B →
      Q ≤ ψ.modulus → CenteredExceptionalProfile.InducedBy χ ψ →
      (∀ I, ¬Supported I → idealCoeff χ I=0) →
      ∀ (m A₀ z : O), (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) →
      ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ →
      X₁ ≤ U₁ → X₂ ≤ U₂ → Y₁ ≤ U₁ → Y₂ ≤ U₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∀ I, Supported I →
        ((Ideal.absNorm I : ℝ) ≤ b*U₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*U₂) →
        primeSupport I ⊆ primeValues S) →
      ‖normalizedRow χ (supportedRectangle S b X₁ X₂) (restrictedValue S live)
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) X₁ X₂ -
        normalizedRow χ (supportedRectangle S b Y₁ Y₂) (restrictedValue S live)
          (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) Y₁ Y₂‖ ≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*L^(-α) := by
  obtain ⟨n,hn⟩ := CenteredMomentNaturalFixedRaySource.volumeControl_uniform_degree
    a b (ε/2) B ha (half_pos hε) hB
  obtain ⟨Cm,hCm,hmain⟩ := PrincipalRestricted.restricted_rectangle α B (ε/2) hα hα4 hB (half_pos hε)
  refine ⟨n,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁,hD₁,hcontrol₁⟩ := hn Q W₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hcontrol₂⟩ := hn Q W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a b ha hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a b ha hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (t y : ℝ) : ‖normPowerProfile W₁ a b ha hs₁ hW₁ t y‖ ≤ M₁ := by
    rw [normPowerProfile_norm,← normPowerProfile_norm W₁ a b ha hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (t y : ℝ) : ‖normPowerProfile W₂ a b ha hs₂ hW₂ t y‖ ≤ M₂ := by
    rw [normPowerProfile_norm,← normPowerProfile_norm W₂ a b ha hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128*(b*M₁+b*M₂)
  let A := 2*(128*b*M₁)*(128*b*M₂)
  let K := 1+4*(D₁+D₂)*V+A
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Cm*K,mul_pos hCm hK,?_⟩
  intro Z hZ F hF hcut S live hS hlive η χ ψ hmod hQψ hind hχ m A₀ z hmLam hm2 hrow
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  let P₁ := normPowerProfile W₁ a b ha hs₁ hW₁ t₁
  let P₂ := normPowerProfile W₂ a b ha hs₂ hW₂ t₂
  have hp₁ : Function.support (P₁ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₁ a b ha hs₁ hW₁ t₁).trans hs₁
  have hp₂ : Function.support (P₂ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₂ a b ha hs₂ hW₂ t₂).trans hs₂
  let H := 1+‖t₁‖+‖t₂‖
  let R := Z^(ε/2)*H^n
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hR : 1 ≤ R := by
    have hh : 1 ≤ H^n := one_le_pow₀ (by
      change 1 ≤ 1+‖t₁‖+‖t₂‖
      exact (le_add_of_nonneg_right (norm_nonneg t₁)).trans (le_add_of_nonneg_right (norm_nonneg t₂)))
    simpa only [one_mul] using mul_le_mul (Real.one_le_rpow hZ (half_pos hε).le)
      hh (by norm_num : (0:ℝ)≤1) (Real.rpow_nonneg hZ0.le _)
  have he₁ : volumeControl Q χ P₁ ≤ D₁*R := by
    apply (hcontrol₁ Z hZ χ hmod t₁).trans
    dsimp only [R,H]
    have hh : (1+‖t₁‖)^n ≤ (1+‖t₁‖+‖t₂‖)^n :=
      pow_le_pow_left₀ (by positivity) (le_add_of_nonneg_right (norm_nonneg _)) _
    calc
      _ ≤ D₁*Z^(ε/2)*(1+‖t₁‖+‖t₂‖)^n := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  have he₂ : volumeControl Q χ P₂ ≤ D₂*R := by
    apply (hcontrol₂ Z hZ χ hmod t₂).trans
    dsimp only [R,H]
    have hh : (1+‖t₂‖)^n ≤ (1+‖t₁‖+‖t₂‖)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₁]) _
    calc
      _ ≤ D₂*Z^(ε/2)*(1+‖t₁‖+‖t₂‖)^n := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  have hcoef : 4*(volumeControl Q χ P₁+volumeControl Q χ P₂)*V+A ≤ K*R := by
    have he := add_le_add he₁ he₂
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤4)) hV
    have hAR : A ≤ A*R := le_mul_of_one_le_right hA hR
    dsimp only [K]
    nlinarith
  have h := hmain Z hZ F hF hcut S live hS hlive η χ ψ Q hQ hQψ hind hχ m A₀ z hmLam hm2 hrow
    P₁ P₂ a b M₁ M₂ ha hb hM₁ hM₂ hp₁ hp₂ (P₁.smooth ⊤) (P₂.smooth ⊤)
    (hbound₁ t₁) (hbound₂ t₂) X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂
    hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  dsimp only at h
  rw [profile_zero P₁ a b ha hp₁,profile_zero P₂ a b ha hp₂] at h
  apply h.trans
  calc
    _ ≤ Cm*Z^(ε/2)*(K*R)*Real.sqrt T*L^(-α) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef (by positivity)) (Real.sqrt_nonneg _)) (by positivity)
    _ = (Cm*K)*(Z^(ε/2)*Z^(ε/2))*H^n*Real.sqrt T*L^(-α) := by dsimp [R]; ring
    _ = _ := by rw [← Real.rpow_add hZ0,show ε/2+ε/2=ε by ring]

end
end Candidate.FourthPower.PrincipalUniform
