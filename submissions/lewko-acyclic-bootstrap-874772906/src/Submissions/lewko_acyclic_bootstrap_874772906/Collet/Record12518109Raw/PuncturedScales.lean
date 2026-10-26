/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentFrequencyScaleSupremum CenteredMomentScaleSupremum
local notation "O" => HeckeFamily.O

/-- Common-puncture deletion followed by two independent rowwise scale
selections. The constant is chosen before the puncture and the row family.

The premise concerns every shortened unpunctured branch and all four common
derivative profiles on its translated scale rectangle. It must be supplied
by a previous moment and its domain admission; this theorem asserts neither
that admission nor an initial moment. The original normalized polynomials
and `naturalSlot` factors are unchanged. -/
theorem punctured_paired_rowwise_scales {α : Type*} [DecidableEq α]
    (F : Finset α) (b M : α → ℝ) (hM : ∀ j ∈ F, 0 ≤ M j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι],
      ∀ (R : Finset (Ideal O)) (hR : ∀ I ∈ R, Prime I)
        (χ : ι → Character) (W V : 𝓢(ℝ, ℂ))
        (a₁ b₁ a₂ b₂ : ℝ),
      0 ≤ b₁ → 0 ≤ b₂ →
      Function.support (W : ℝ → ℂ) ⊆ Set.Icc a₁ b₁ →
      Function.support (V : ℝ → ℂ) ⊆ Set.Icc a₂ b₂ →
      ∀ (pool : ι → α → Finset (Ideal O))
        (β : ι → α → Ideal O → ℂ) (P : ι → α → ℝ),
      (∀ i j, j ∈ F → ∀ I ∈ pool i j, Prime I) →
      (∀ i j, j ∈ F → 0 < P i j) →
      (∀ i j, j ∈ F → ∀ I ∈ pool i j, ‖β i j I‖ ≤ M j) →
      (∀ i j, j ∈ F → ∀ I ∈ pool i j, β i j I ≠ 0 →
        (I.absNorm : ℝ) ≤ b j * P i j) →
      ∀ (lo hi low high E : ℝ) (lx ly : ι → ℝ),
      lo ≤ hi → low ≤ high → 0 ≤ E →
      (∀ i, lx i ∈ Set.Icc lo hi) →
      (∀ i, ly i ∈ Set.Icc low high) →
      (∀ D₁ ∈ R.powerset, ∀ D₂ ∈ R.powerset, ∀ J ∈ F.powerset,
        ∀ j k : Fin 2,
        ∀ x ∈ Set.Icc (lo - Real.log ((∏ I ∈ D₁, I).absNorm : ℝ))
          (hi - Real.log ((∏ I ∈ D₁, I).absNorm : ℝ)),
        ∀ y ∈ Set.Icc (low - Real.log ((∏ I ∈ D₂, I).absNorm : ℝ))
          (high - Real.log ((∏ I ∈ D₂, I).absNorm : ℝ)),
        (∑ i, ‖polynomial (χ i) false (scaleTest (W : ℝ → ℂ) j)
            (Real.exp x) 0 0 *
          polynomial (χ i) false (scaleTest (V : ℝ → ℂ) k)
            (Real.exp y) 0 0 *
          ∏ h ∈ F \ J, naturalSlot (χ i) (pool i h) (β i h) (P i h)‖ ^ 2) ≤ E) →
      (∑ i, ‖polynomial ((χ i).excludePrimes R hR) false W (Real.exp (lx i)) 0 0 *
          polynomial ((χ i).excludePrimes R hR) false V (Real.exp (ly i)) 0 0 *
          ∏ h ∈ F, naturalSlot ((χ i).excludePrimes R hR) (pool i h) (β i h) (P i h)‖ ^ 2) ≤
        C * ((∏ I ∈ R, I).absNorm : ℝ) ^ ε *
          ((1 + 2 * (hi - lo)) * ((1 + 2 * (high - low)) * E)) := by
  obtain ⟨C, hC, hdelete⟩ := actual_shared_energy F b M hM ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ R hR χ W V a₁ b₁ a₂ b₂ hb₁ hb₂ hW hV pool β P hp hP hβ hs
    lo hi low high E lx ly hlh hlw hE hlx hly henergy
  have hdx : 0 ≤ 1 + 2 * (hi - lo) := by linarith
  have hdy : 0 ≤ 1 + 2 * (high - low) := by linarith
  apply hdelete R hR χ (fun _ => W) (fun _ => V)
    (fun i => Real.exp (lx i)) (fun i => Real.exp (ly i)) pool β P
    (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _) hp hP hβ hs
    ((1 + 2 * (hi - lo)) * ((1 + 2 * (high - low)) * E))
    (mul_nonneg hdx (mul_nonneg hdy hE))
  intro D₁ hD₁ D₂ hD₂ J hJ
  have hN₁ : 0 < ((∏ I ∈ D₁, I).absNorm : ℝ) :=
    CenteredMomentReflectionDeletion.subset_product_norm_pos D₁
      (fun I hI => hR I (Finset.mem_powerset.mp hD₁ hI))
  have hN₂ : 0 < ((∏ I ∈ D₂, I).absNorm : ℝ) :=
    CenteredMomentReflectionDeletion.subset_product_norm_pos D₂
      (fun I hI => hR I (Finset.mem_powerset.mp hD₂ hI))
  let d₁ := Real.log ((∏ I ∈ D₁, I).absNorm : ℝ)
  let d₂ := Real.log ((∏ I ∈ D₂, I).absNorm : ℝ)
  have hb := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
    χ χ (fun _ => 0) (fun _ => 0)
    (fun i => ∏ h ∈ F \ J, naturalSlot (χ i) (pool i h) (β i h) (P i h))
    (W : ℝ → ℂ) (V : ℝ → ℂ) a₁ b₁ a₂ b₂ hb₁ hb₂ hW hV
    (W.smooth ⊤) (V.smooth ⊤)
    (lo - d₁) (hi - d₁) (low - d₂) (high - d₂) E
    (by linarith) (by linarith) (fun i => lx i - d₁) (fun i => ly i - d₂)
    (fun i _ => ⟨sub_le_sub_right (hlx i).1 _, sub_le_sub_right (hlx i).2 _⟩)
    (fun i _ => ⟨sub_le_sub_right (hly i).1 _, sub_le_sub_right (hly i).2 _⟩)
    (henergy D₁ hD₁ D₂ hD₂ J hJ)
  have hd₁ : (hi - d₁) - (lo - d₁) = hi - lo := by ring
  have hd₂ : (high - d₂) - (low - d₂) = high - low := by ring
  rw [hd₁, hd₂] at hb
  simpa only [d₁, d₂, Real.exp_sub, Real.exp_log hN₁,
    Real.exp_log hN₂] using hb

end
end OAI.SevenEighths.Record12518109Raw

#print axioms OAI.SevenEighths.Record12518109Raw.punctured_paired_rowwise_scales
