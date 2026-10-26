/- Copyright (c) 2026 Sil. Apache-2.0.
Literal fifth-free principal cancellation with a common finite puncture.
The displayed volume controls are the baseline's explicit lattice errors;
there is no residual analytic-energy assumption in this theorem.
-/
import Candidate.FourthPower.PrincipalRows
import Candidate.FourthPower.PrincipalRectangle
import Candidate.FourthPower.PrincipalExtraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.PrincipalRestricted
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceMass
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation CenteredMomentLattice
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelRowProfiles KernelRowPools KernelRowExpansion KernelAllocationIdentity
open ReferencePrimeEnclosure PrincipalKernel
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem polynomial_zero (χ : Character) (W : ℝ → ℂ) (b X : ℝ)
    (hX : 0 < X) (hW : Function.support W ⊆ Set.Iic b) :
    HeckeDyadic.polynomial χ false W X 0 0 =
      (Real.sqrt X : ℂ)⁻¹*twistedIdealSum χ W 0 X := by
  rw [natural_polynomial_finite χ W b X hX hW]
  congr 1
  symm
  simp only [twistedIdealSum,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  apply tsum_eq_sum
  intro I hi
  by_cases hz : I=0
  · subst I
    rw [map_zero,zero_mul]
  · have hw : W ((Ideal.absNorm I : ℝ)/X)=0 := by
      by_contra h
      exact hi ((mem_idealBall _ _).mpr ⟨hz,(div_le_iff₀ hX).mp (hW h)⟩)
    rw [hw,mul_zero]

theorem plain_pair (χ : Character) (S : Finset PrimeIdeal) (W₁ W₂ : ℝ → ℂ)
    (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b) (hW₂ : Function.support W₂ ⊆ Set.Iic b)
    (hχ : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I, Supported I →
      ((Ideal.absNorm I : ℝ) ≤ b*X₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*X₂) →
      primeSupport I ⊆ primeValues S) :
    normalizedRow χ (supportedRectangle S b X₁ X₂) (fun _ => 1) W₁ W₂ X₁ X₂ =
      (Real.sqrt (X₁*X₂) : ℂ)⁻¹*
        (twistedIdealSum χ W₁ 0 X₁*twistedIdealSum χ W₂ 0 X₂) := by
  rw [enclosed_row χ S b X₁ X₂ W₁ W₂ (fun _ => 1) hχ henclose,
    natural_pair_row χ W₁ W₂ b X₁ X₂ hX₁ hX₂ hW₁ hW₂,
    polynomial_zero χ W₁ b X₁ hX₁ hW₁,polynomial_zero χ W₂ b X₂ hX₂ hW₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

/-- The constant is chosen before all supports, profiles, characters and
lengths. The remaining lattice control is displayed explicitly on the RHS. -/
theorem restricted_rectangle (α B ε : ℝ)
    (hα : 0 ≤ α) (hα4 : α < 4/5) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ F : Id,
      F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^B →
      ∀ (S : Finset PrimeIdeal) (live : S → Bool),
      (∀ P ∈ S, Supported P.val) → (∀ P : S, live P=true → P.val.val ∣ F) →
      ∀ (η χ ψ : Character) (Q : Id) (hQ : Q ≠ 0),
      (Q ≤ ψ.modulus) → CenteredExceptionalProfile.InducedBy χ ψ →
      (∀ I, ¬Supported I → idealCoeff χ I=0) →
      ∀ (m A₀ z : O), (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) →
      ∀ (W₁ W₂ : ℝ → ℂ) (a b M₁ M₂ : ℝ) (ha : 0 < a),
      0 ≤ b → 0 ≤ M₁ → 0 ≤ M₂ →
      ∀ (hs₁ : Function.support W₁ ⊆ Set.Icc a b)
        (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
        (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂),
      (∀ y, ‖W₁ y‖ ≤ M₁) → (∀ y, ‖W₂ y‖ ≤ M₂) →
      ∀ X₁ X₂ Y₁ Y₂ U₁ U₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ →
      X₁ ≤ U₁ → X₂ ≤ U₂ → Y₁ ≤ U₁ → Y₂ ≤ U₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∀ I, Supported I →
        ((Ideal.absNorm I : ℝ) ≤ b*U₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*U₂) →
        primeSupport I ⊆ primeValues S) →
      let E := volumeControl Q χ (normPowerProfile W₁ a b ha hs₁ hW₁ 0) +
        volumeControl Q χ (normPowerProfile W₂ a b ha hs₂ hW₂ 0)
      let K := 4*E*(128*(b*M₁+b*M₂))+2*(128*b*M₁)*(128*b*M₂)
      ‖normalizedRow χ (supportedRectangle S b X₁ X₂) (restrictedValue S live) W₁ W₂ X₁ X₂ -
        normalizedRow χ (supportedRectangle S b Y₁ Y₂) (restrictedValue S live) W₁ W₂ Y₁ Y₂‖ ≤
        C*Z^ε*K*Real.sqrt T*L^(-α) := by
  obtain ⟨C,hC,hmass⟩ := PrincipalKernel.ideal_mass (1-α) B ε (by linarith) hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ F hF hcut S live hS hlive η χ ψ Q hQ hQψ hind hχ
    m A₀ z hmLam hm2 hrow W₁ W₂ a b M₁ M₂ ha hb hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  let E := volumeControl Q χ (normPowerProfile W₁ a b ha hs₁ hW₁ 0) +
    volumeControl Q χ (normPowerProfile W₂ a b ha hs₂ hW₂ 0)
  let K := 4*E*(128*(b*M₁+b*M₂))+2*(128*b*M₁)*(128*b*M₂)
  have hK : 0 ≤ K := by
    have he : 0 ≤ E := add_nonneg (volumeControl_nonneg _ _ _) (volumeControl_nonneg _ _ _)
    dsimp only [K]
    positivity
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hw₁ : Function.support W₁ ⊆ Set.Iic b := fun _ h => (hs₁ h).2
  have hw₂ : Function.support W₂ ⊆ Set.Iic b := fun _ h => (hs₂ h).2
  let D := divisorPool (supportedRectangle S b U₁ U₂)
  let G (d : Id × Id) :=
    normalizedRow χ (supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
        (fun _ => 1) W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) -
      normalizedRow χ (supportedRectangle S b (Y₁/Ideal.absNorm d.1) (Y₂/Ideal.absNorm d.2))
        (fun _ => 1) W₁ W₂ (Y₁/Ideal.absNorm d.1) (Y₂/Ideal.absNorm d.2)
  have hd (d : Id × Id) (h : d ∈ D) := divisor_supported h
  have hG (d : Id × Id) (h : d ∈ D) :
      ‖G d‖ ≤ K*Real.sqrt (T/pairNorm d)*(L/pairNorm d)^(-α) := by
    have hdz := hd d h
    have hn := pairNorm_pos hdz.1 hdz.2.1
    have hn₁ := ideal_norm_one_le hdz.1
    have hn₂ := ideal_norm_one_le hdz.2.1
    have hc (V₁ V₂ : ℝ) (hv₁ : 0 < V₁) (hv₂ : 0 < V₂)
        (hu₁ : V₁ ≤ U₁) (hu₂ : V₂ ≤ U₂) :
        normalizedRow χ (supportedRectangle S b (V₁/Ideal.absNorm d.1) (V₂/Ideal.absNorm d.2))
            (fun _ => 1) W₁ W₂ (V₁/Ideal.absNorm d.1) (V₂/Ideal.absNorm d.2) =
          (Real.sqrt ((V₁/Ideal.absNorm d.1)*(V₂/Ideal.absNorm d.2)) : ℂ)⁻¹*
            (twistedIdealSum χ W₁ 0 (V₁/Ideal.absNorm d.1)*
              twistedIdealSum χ W₂ 0 (V₂/Ideal.absNorm d.2)) := by
      apply plain_pair χ S W₁ W₂ b _ _
        (shortened_positive_le hv₁ hdz.1).1 (shortened_positive_le hv₂ hdz.2.1).1 hw₁ hw₂ hχ
      intro I hI hlen
      apply henclose I hI
      exact hlen.elim
        (fun hh => Or.inl (hh.trans (mul_le_mul_of_nonneg_left
          ((shortened_positive_le hv₁ hdz.1).2.trans hu₁) hb)))
        (fun hh => Or.inr (hh.trans (mul_le_mul_of_nonneg_left
          ((shortened_positive_le hv₂ hdz.2.1).2.trans hu₂) hb)))
    have hp (V₁ V₂ : ℝ) (hv : V₁*V₂=T) :
        (V₁/(Ideal.absNorm d.1 : ℝ))*(V₂/(Ideal.absNorm d.2 : ℝ))=T/pairNorm d := by
      rw [pairNorm,← hv]
      ring
    dsimp only [G]
    rw [hc X₁ X₂ (hL.trans_le hX₁) (hL.trans_le hX₂) hXU₁ hXU₂,
      hc Y₁ Y₂ (hL.trans_le hY₁) (hL.trans_le hY₂) hYU₁ hYU₂,
      hp X₁ X₂ hpX,hp Y₁ Y₂ hpY,← mul_sub]
    apply PrincipalRectangle.normalized_fractional_rectangle
      η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ W₂ a b a b M₁ M₂
      ha ha hb hb hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
      0 _ _ _ _ (T/pairNorm d) (L/pairNorm d) α (div_pos hL hn) hα (by linarith)
    · exact PrincipalExtraction.shorter_lower_bound L X₁ _ _ hL.le hX₁ hn₁ hn₂
    · simpa only [pairNorm,mul_comm] using
        PrincipalExtraction.shorter_lower_bound L X₂ _ _ hL.le hX₂ hn₂ hn₁
    · exact PrincipalExtraction.shorter_lower_bound L Y₁ _ _ hL.le hY₁ hn₁ hn₂
    · simpa only [pairNorm,mul_comm] using
        PrincipalExtraction.shorter_lower_bound L Y₂ _ _ hL.le hY₂ hn₂ hn₁
    · exact hp X₁ X₂ hpX
    · exact hp Y₁ Y₂ hpY
  rw [PrincipalRows.centered_expansion S live χ W₁ W₂ b X₁ X₂ Y₁ Y₂ U₁ U₂ hb
    (hL.trans_le hX₁) (hL.trans_le hX₂) (hL.trans_le hY₁) (hL.trans_le hY₂)
    hXU₁ hXU₂ hYU₁ hYU₂ hw₁ hw₂]
  have h := PrincipalExtraction.sum_bound χ S (fun P => localSeries (live P)) D
    (fun d h => ⟨(hd d h).1,(hd d h).2.1⟩) G T L α K (C*Z^ε) hT.le hL hK
    (hmass Z hZ F hF hcut S live hS hlive D
      (fun d h => ⟨(hd d h).1,(hd d h).2.1⟩) (fun d h => (hd d h).2.2)) hG
  exact h.trans_eq (by dsimp only [K,E]; ring)

end
end Candidate.FourthPower.PrincipalRestricted
