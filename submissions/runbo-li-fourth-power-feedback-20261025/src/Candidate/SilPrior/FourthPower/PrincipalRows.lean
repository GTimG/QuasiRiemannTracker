/- Copyright (c) 2026 Sil. Apache-2.0.
Exact fixed-puncture centered rows. A common finite outer rectangle makes
the divisor set identical on both sides before any norm is taken.
-/
import Candidate.SilPrior.FourthPower.PrincipalKernel
import Candidate.SilPrior.FourthPower.ReferencePrimeEnclosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.SilPrior.FourthPower.PrincipalRows
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceMass
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelRestrictedState KernelRowExpansion
open KernelRowProfiles KernelRowPools PrincipalKernel ReferencePrimeEnclosure
open OAI.IdealMobiusDivisorSum (idealDivisors)
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem row_expansion (S : Finset PrimeIdeal) (live : S → Bool) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (f : IdealPair → ℂ) :
    (∑ n ∈ D, restrictedValue S live n*pairCharacter χ n*f n) =
      ∑ d ∈ divisorPool D,
        (kernelOn S (fun P => localSeries (live P)) d.1 d.2 : ℂ)*pairCharacter χ d*
          ∑ a ∈ residualPool D d, pairCharacter χ a*f (multiplyPair d a) := by
  have hp (n : IdealPair) (hn : n ∈ D) : restrictedValue S live n =
      ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (kernelOn S (fun P => localSeries (live P)) d.1 d.2 : ℂ) := by
    have h := congrArg (fun z : ℤ => (z : ℂ))
      (PrincipalKernel.divisor_identity S live (hnz n hn).1 (hnz n hn).2 (hs n hn))
    push_cast at h
    exact h.symm
  calc
    _ = ∑ n ∈ D, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (kernelOn S (fun P => localSeries (live P)) d.1 d.2 : ℂ)*pairCharacter χ n*f n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hp n hn]
      simp only [Finset.sum_mul]
    _ = _ := by
      simpa only [mul_one,one_mul] using finite_row_reindex D hnz χ f
        (fun d => (kernelOn S (fun P => localSeries (live P)) d.1 d.2 : ℂ)) (fun _ => 1)

theorem normalized_expansion (S : Finset PrimeIdeal) (live : S → Bool) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    normalizedRow χ D (restrictedValue S live) W₁ W₂ X₁ X₂ =
      ∑ d ∈ divisorPool D,
        extractedScalar χ (fun e => (kernelOn S (fun P => localSeries (live P)) e.1 e.2 : ℂ)) d*
          normalizedRow χ (residualPool D d) (fun _ => 1) W₁ W₂
            (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  unfold normalizedRow
  rw [row_expansion S live D hnz hs χ (pairProfile W₁ W₂ X₁ X₂),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simpa only [normalizedRow,one_mul,Finset.mul_sum] using
    normalized_extraction χ d (divisorPool_nonzero D hnz hd) (residualPool D d)
      (fun e => (kernelOn S (fun P => localSeries (live P)) e.1 e.2 : ℂ))
      (fun _ => 1) W₁ W₂ X₁ X₂ hX₁ hX₂

/-- Only the enclosing finite cutoff changes; the physical scales, phases,
character and arbitrary restriction r are unchanged. -/
theorem cutoff_invariance (χ : Character) (S : Finset PrimeIdeal) (r : IdealPair → ℂ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ U₁ U₂ : ℝ)
    (hb : 0 ≤ b) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hU₁ : X₁ ≤ U₁) (hU₂ : X₂ ≤ U₂)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b) (hW₂ : Function.support W₂ ⊆ Set.Iic b) :
    normalizedRow χ (supportedRectangle S b U₁ U₂) r W₁ W₂ X₁ X₂ =
      normalizedRow χ (supportedRectangle S b X₁ X₂) r W₁ W₂ X₁ X₂ := by
  have hsub : supportedRectangle S b X₁ X₂ ⊆ supportedRectangle S b U₁ U₂ := by
    intro n hn
    obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hn
    obtain ⟨hiz,hin⟩ := (mem_idealBall _ _).mp hi
    obtain ⟨hjz,hjn⟩ := (mem_idealBall _ _).mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_idealBall _ _).mpr ⟨hiz,hin.trans (mul_le_mul_of_nonneg_left hU₁ hb)⟩,
        (mem_idealBall _ _).mpr ⟨hjz,hjn.trans (mul_le_mul_of_nonneg_left hU₂ hb)⟩⟩,hs⟩
  unfold normalizedRow
  congr 1
  symm
  apply Finset.sum_subset hsub
  intro n hn hnot
  have hz : pairProfile W₁ W₂ X₁ X₂ n=0 := by
    by_contra h
    obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp h
    have hnz := supportedRectangle_nonzero hn
    apply hnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_idealBall _ _).mpr ⟨hnz.1,(div_le_iff₀ hX₁).mp (hW₁ h₁)⟩,
        (mem_idealBall _ _).mpr ⟨hnz.2,(div_le_iff₀ hX₂).mp (hW₂ h₂)⟩⟩,
        (Finset.mem_filter.mp hn).2⟩
  rw [hz,mul_zero]

/-- Both rectangles use exactly the same coefficient and divisor set. -/
theorem centered_expansion (S : Finset PrimeIdeal) (live : S → Bool)
    (χ : Character) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ U₁ U₂ : ℝ)
    (hb : 0 ≤ b) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hXU₁ : X₁ ≤ U₁) (hXU₂ : X₂ ≤ U₂) (hYU₁ : Y₁ ≤ U₁) (hYU₂ : Y₂ ≤ U₂)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b) (hW₂ : Function.support W₂ ⊆ Set.Iic b) :
    normalizedRow χ (supportedRectangle S b X₁ X₂) (restrictedValue S live) W₁ W₂ X₁ X₂ -
      normalizedRow χ (supportedRectangle S b Y₁ Y₂) (restrictedValue S live) W₁ W₂ Y₁ Y₂ =
      ∑ d ∈ divisorPool (supportedRectangle S b U₁ U₂),
        extractedScalar χ (fun e => (kernelOn S (fun P => localSeries (live P)) e.1 e.2 : ℂ)) d*
          (normalizedRow χ (supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
              (fun _ => 1) W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) -
            normalizedRow χ (supportedRectangle S b (Y₁/Ideal.absNorm d.1) (Y₂/Ideal.absNorm d.2))
              (fun _ => 1) W₁ W₂ (Y₁/Ideal.absNorm d.1) (Y₂/Ideal.absNorm d.2)) := by
  rw [← cutoff_invariance χ S (restrictedValue S live) W₁ W₂ b X₁ X₂ U₁ U₂
    hb hX₁ hX₂ hXU₁ hXU₂ hW₁ hW₂,
    ← cutoff_invariance χ S (restrictedValue S live) W₁ W₂ b Y₁ Y₂ U₁ U₂
      hb hY₁ hY₂ hYU₁ hYU₂ hW₁ hW₂]
  rw [normalized_expansion S live _ (fun _ h => supportedRectangle_nonzero h)
      (fun _ h => (Finset.mem_filter.mp h).2) χ W₁ W₂ X₁ X₂ hX₁ hX₂,
    normalized_expansion S live _ (fun _ h => supportedRectangle_nonzero h)
      (fun _ h => (Finset.mem_filter.mp h).2) χ W₁ W₂ Y₁ Y₂ hY₁ hY₂,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← mul_sub,residual_rectangle hd]
  have hd0 := divisor_supported hd
  have hn₁ := ideal_norm_one_le hd0.1
  have hn₂ := ideal_norm_one_le hd0.2.1
  rw [cutoff_invariance χ S (fun _ => 1) W₁ W₂ b
    (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) _ _ hb
    (shortened_positive_le hX₁ hd0.1).1 (shortened_positive_le hX₂ hd0.2.1).1
    (div_le_div_of_nonneg_right hXU₁ (zero_le_one.trans hn₁))
    (div_le_div_of_nonneg_right hXU₂ (zero_le_one.trans hn₂)) hW₁ hW₂,
    cutoff_invariance χ S (fun _ => 1) W₁ W₂ b
      (Y₁/Ideal.absNorm d.1) (Y₂/Ideal.absNorm d.2) _ _ hb
      (shortened_positive_le hY₁ hd0.1).1 (shortened_positive_le hY₂ hd0.2.1).1
      (div_le_div_of_nonneg_right hYU₁ (zero_le_one.trans hn₁))
      (div_le_div_of_nonneg_right hYU₂ (zero_le_one.trans hn₂)) hW₁ hW₂]

end
end Candidate.SilPrior.FourthPower.PrincipalRows
