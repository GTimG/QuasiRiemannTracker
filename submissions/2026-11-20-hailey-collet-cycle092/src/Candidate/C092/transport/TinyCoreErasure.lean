/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.TinyCoreUnmarked

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentCoreFloor CenteredMomentInductionEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentEnergyBands
open QRH.Cycle092.WholeSlot QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
local notation "O" => HeckeFamily.O

/-- Honest deletion of all original marks on the positive low-response class. -/
theorem erase_all_low_energy {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (η : Character) (mask A : O) (t U e pay : ℝ) (w : Slot → ℝ)
    (W₁ W₂ : ℝ → ℂ) (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ b₁ b₂ : ℝ) (r : CenteredMomentRadialEligibleEnergy.Radial)
    (hΦ : ∀ x, 0 ≤ (r.profile x).re)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) (hU : 0 < U) (hpay : 0 ≤ pay) (hP : ∀ i, 0 ≤ P i) :
    energy η mask A t W₁ W₂ pool coeff P X₁ X₂
      (fun z => r.keep z ∧ LowRows Finset.univ η mask A t U e pay w pool coeff P z) r.profile r.scale ≤
      (pay^(Fintype.card Slot)*U^(e*∑ i, w i))*zeroEnergy η mask A t W₁ W₂ X₁ X₂ r := by
  have h := low_energy_erasure Finset.univ ∅ (Finset.empty_subset _)
    η mask A t U e pay w W₁ W₂ pool coeff P X₁ X₂ b₁ b₂ hX₁ hX₂ hs₁ hs₂
    r.keep r.profile hΦ r.scale r.scale_pos hU hpay hP
  rw [subsetEnergy_univ η mask A t W₁ W₂ pool coeff P X₁ X₂ _ r.profile r.scale (mul_pos hX₁ hX₂).le hP,
    empty_subset_energy η mask A t W₁ W₂ pool coeff P X₁ X₂ r (mul_pos hX₁ hX₂).le hP] at h
  simpa using h

/-- A source-backed bound considerably sharper than the earlier coarse .141. -/
theorem original_width_cap_sharp {n y : ℝ} (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY)
    (hn : y ≤ n) : sourceWidth n y-(u : ℝ) ≤ 134/1000 := by
  have hg := sourceGain_antitone hy0 hy1
  have hcorner : sourceGain sourceY0 < (3/1000 : ℝ) := by
    norm_num [sourceGain,sourceY0,sourceSeam,sourceY,lowerGain,QRH.Cycle090.upperGain]
  unfold sourceWidth
  norm_num [sourceY0,u] at hy0 ⊢
  linarith

/-- Original U-based cap exponents below one give the real individual
ordinary length bounds required by the incumbent ZeroAt supplier. -/
theorem ordinary_lengths_below_U {N Y U X₁ X₂ : ℝ}
    (hU : 1 < U) (hN : N ≤ 1) (hY : Y ≤ 1)
    (hbox : QRH.Cycle092.NativeStrip.Box N Y 0 (length U X₁) (length U X₂) 0) :
    X₁ ≤ U ∧ X₂ ≤ U := by
  have hlen1 : length U X₁ ≤ 1 := by rcases hbox.2.2.1 with h | h; exact h.1.trans hN; exact h.1.trans hY
  have hlen2 : length U X₂ ≤ 1 := by rcases hbox.2.2.1 with h | h; exact h.2.trans hY; exact h.2.trans hN
  have hlen {X : ℝ} (h : length U X ≤ 1) : X ≤ U := by
    have hm : max 1 X ≤ U^((1 : ℝ)) := (Real.logb_le_iff_le_rpow hU (zero_lt_one.trans_le (le_max_left _ _))).1 h
    simpa using (le_max_right (1 : ℝ) X).trans hm
  exact ⟨hlen hlen1,hlen hlen2⟩

/-- The unmarked estimate plus the exact .75 prime response is paid through
7/8; all fixed character and slot error exponents remain charged. -/
theorem unmarked_middle_paid {V e width buffer : ℝ} {K : ℕ}
    (hV : V ≤ 7/8) (he : e ≤ 3/4) (hw0 : 0 ≤ width) (hw : width ≤ 134/1000)
    (hb : buffer*(K : ℝ) ≤ 1/10000) :
    V+1/10000+buffer*(K : ℝ)+e*width ≤
      V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V) := by
  have hew := mul_le_mul_of_nonneg_right he hw0
  have hVH : 0 ≤ (H : ℝ)-V := by norm_num [H,u] at *; linarith only [hV]
  rw [max_eq_right hVH]
  norm_num [H,u,rho] at *
  linarith

end
end QRH.Cycle092.TinyCore
