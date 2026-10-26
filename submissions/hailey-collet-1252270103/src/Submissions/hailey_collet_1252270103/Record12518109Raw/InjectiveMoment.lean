/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Raw.CanonicalMaskedMoment

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentEnergySlotHeight
open CenteredMomentEnergyProfiles CenteredMomentEnergyAllocatedChildren
open CenteredMomentInductionEnergy CenteredMomentDetectorEnergyInitialState
open CenteredMomentSecondHeightFamily CenteredMomentScaleSupremum
local notation "O" => HeckeFamily.O

/-- Reindex an injective finite family before applying the literal radial
energy. The injection is used once; no arithmetic multiplicity is hidden. -/
theorem finite_injective_positive_le_energy {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ)
    (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b)
    (pool : α → Finset (Ideal O)) (β : α → Ideal O → ℂ) (P : α → ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (row : ι → O) (hinj : Function.Injective row)
    (hkeep : ∀ i, keep (row i))
    (hcover : ∀ i, 1 ≤ (Φ (‖eisEmbedding (row i)‖^2 / K)).re) :
    (∑ i, ‖CenteredMomentRetainedEnergy.positiveSlotRow η m A (row i)
      W₁ W₂ pool β P t X₁ X₂‖^2) ≤
      energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K := by
  have he := finite_positive_le_energy η m A W₁ W₂ a b hs₁ hs₂ pool β P t X₁ X₂
    hX₁ hX₂ keep Φ K hK hΦ (Finset.univ.image row)
    (by intro z hz; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hkeep i)
    (by intro z hz; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hcover i)
  rwa [Finset.sum_image (fun i _ j _ h => hinj h)] at he

/-- This is the exact analytic input used after fixing the surviving original
slot set and missing radical. Each deletion branch is the literal unpunctured
initial energy, with the inherited relative-slot height shifted to `t + freq`.
The source bound can come from the previous face or the proved natural branch;
no density assumption or row-dependent coefficient family is introduced. -/
theorem canonical_masked_injective_rowwise_from_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (bslot Mslot : α → ℝ) (hM : ∀ j ∈ F, 0 ≤ Mslot j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : Character) (Q R : Ideal O), R ≠ 0 →
      ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ), 0 ≤ b →
      Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b →
      ∀ (pool : α → Finset (Ideal O)) (ν : α → Character)
        (Wslot : α → ℝ → ℂ) (P σ freq : α → ℝ) (t : ℝ),
      (∀ j ∈ F, ∀ I ∈ pool j, Prime I) → (∀ j ∈ F, 0 < P j) →
      (∀ j ∈ F, ∀ I ∈ pool j,
        ‖idealCoeff (ν j) I * HeckePrimeAnnular.annularWeight (Wslot j) (P j) (σ j) (freq j) I‖ ≤ Mslot j) →
      (∀ j ∈ F, ∀ I ∈ pool j,
        idealCoeff (ν j) I * HeckePrimeAnnular.annularWeight (Wslot j) (P j) (σ j) (freq j) I ≠ 0 →
        (I.absNorm : ℝ) ≤ bslot j * P j) →
      ∀ (ι : Type) [Fintype ι] (row : ι → O), Function.Injective row →
      (∀ z, initialKeep η Q (row z)) →
      ∀ (N : ∀ z, NaturalRow η (row z))
        (Φ : 𝓢(ℝ,ℂ)) (K E lo hi low high : ℝ) (lx ly : ι → ℝ),
      0 < K → (∀ x, 0 ≤ (Φ x).re) →
      (∀ z, 1 ≤ (Φ (‖eisEmbedding (row z)‖^2 / K)).re) →
      0 ≤ E → lo ≤ hi → low ≤ high →
      (∀ z, lx z ∈ Set.Icc lo hi) → (∀ z, ly z ∈ Set.Icc low high) →
      (∀ D₁ ∈ (CompletedGauss.primeSupport R).powerset,
        ∀ D₂ ∈ (CompletedGauss.primeSupport R).powerset, ∀ J ∈ F.powerset,
        ∀ j k : Fin 2,
        ∀ x ∈ Set.Icc (lo - Real.log ((∏ I ∈ D₁, I).absNorm : ℝ))
          (hi - Real.log ((∏ I ∈ D₁, I).absNorm : ℝ)),
        ∀ y ∈ Set.Icc (low - Real.log ((∏ I ∈ D₂, I).absNorm : ℝ))
          (high - Real.log ((∏ I ∈ D₂, I).absNorm : ℝ)),
        energy η (fixedBadMask * idealGenerator 1) 1 0
          (derivativeChoice W₁ j) (derivativeChoice W₂ k)
          (fun i : ↥(F \ J) => pool i)
          (fun (i : ↥(F \ J)) I => idealCoeff (ν i) I *
            HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (t + freq i) I)
          (fun i : ↥(F \ J) => P i) (Real.exp x) (Real.exp y) (initialKeep η Q) Φ K ≤ E) →
      (∑ z : ι, ‖polynomial (excluded (N z).character R) false W₁ (Real.exp (lx z)) 0 0 *
        polynomial (excluded (N z).character R) false W₂ (Real.exp (ly z)) 0 0 *
        ∏ i ∈ F, naturalSlot (excluded (N z).character R) (pool i)
          (heightCoefficient (fun I => idealCoeff (ν i) I *
            HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (freq i) I) t) (P i)‖^2) ≤
        C * ((∏ I ∈ CompletedGauss.primeSupport R, I).absNorm : ℝ)^ε *
          ((1 + 2 * (hi - lo)) * ((1 + 2 * (high - low)) * E)) := by
  obtain ⟨C, hC, hbound⟩ := punctured_paired_rowwise_scales F bslot Mslot hM ε hε
  refine ⟨C, hC, ?_⟩
  intro η Q R hR W₁ W₂ a b hb hs₁ hs₂ pool ν Wslot P σ freq t hp hP hβ hsupport
    ι _ row hinj hkeep N Φ K E lo hi low high lx ly hK hΦ hcover hE hlo hlow hlx hly hsource
  let β := fun i I => idealCoeff (ν i) I *
    HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (freq i) I
  apply hbound (CompletedGauss.primeSupport R) (support_prime R)
    (fun z : ι => (N z).character) W₁ W₂ a b a b hb hb hs₁ hs₂
    (fun _ => pool) (fun _ i => heightCoefficient (β i) t) (fun _ => P)
    (fun _ => hp) (fun _ => hP)
    (fun _ i hi I hI => by
      rw [heightCoefficient_norm _ _ _ (hp i hi I hI).ne_zero]
      exact hβ i hi I hI)
    (fun _ i hi I hI hn => hsupport i hi I hI (left_ne_zero_of_mul hn))
    lo hi low high E lx ly hlo hlow hE hlx hly
  intro D₁ hD₁ D₂ hD₂ J hJ j k x hx y hy
  have hP' : ∀ i : ↥(F \ J), 0 < P i := fun i => hP i (Finset.mem_sdiff.mp i.property).1
  have he := finite_injective_positive_le_energy η (fixedBadMask * idealGenerator 1) 1
    (derivativeChoice W₁ j) (derivativeChoice W₂ k) a b
    (derivativeChoice_support a b W₁ hs₁ j) (derivativeChoice_support a b W₂ hs₂ k)
    (fun i : ↥(F \ J) => pool i) (fun i : ↥(F \ J) => heightCoefficient (β i) t)
    (fun i : ↥(F \ J) => P i) 0 (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
    (initialKeep η Q) Φ K hK hΦ row hinj hkeep hcover
  have hheight := inherited_height_energy η (fixedBadMask * idealGenerator 1) 1
    (derivativeChoice W₁ j) (derivativeChoice W₂ k)
    (fun i : ↥(F \ J) => pool i) (fun (i : ↥(F \ J)) I => idealCoeff (ν i) I)
    (fun i : ↥(F \ J) => Wslot i) (fun i : ↥(F \ J) => P i)
    (fun i : ↥(F \ J) => σ i) (fun i : ↥(F \ J) => freq i) hP'
    (fun i I hI => (hp i (Finset.mem_sdiff.mp i.property).1 I hI).ne_zero)
    t 0 (Real.exp x) (Real.exp y) (initialKeep η Q) Φ K
  have hg := he.trans (hheight.le.trans (hsource D₁ hD₁ D₂ hD₂ J hJ j k x hx y hy))
  apply le_trans ?_ hg
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro z _
  have hz := natural_product_eq_positive (N z)
    (derivativeChoice W₁ j) (derivativeChoice W₂ k)
    (fun i : ↥(F \ J) => pool i) (fun i : ↥(F \ J) => heightCoefficient (β i) t)
    (fun i : ↥(F \ J) => P i) (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _) hP'
  rw [Finset.prod_coe_sort (s := F \ J) (f := fun i =>
    naturalSlot (N z).character (pool i) (heightCoefficient (β i) t) (P i))] at hz
  simpa only [derivativeChoice_apply] using congrArg (fun v : ℂ => ‖v‖^2) hz

end
end OAI.SevenEighths.Record12518109Raw

#print axioms OAI.SevenEighths.Record12518109Raw.finite_injective_positive_le_energy
#print axioms OAI.SevenEighths.Record12518109Raw.canonical_masked_injective_rowwise_from_energy
