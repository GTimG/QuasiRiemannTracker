/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Zero-width original marks are calibrated before every measured response split. -/
import Candidate.C092.transport.StrongPairRegularTerminalRows

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentWholeSlotDeletion ConcretePrimeRowBridge
open HeckePrimeAnnular HeckeDyadic CenteredMomentHeckeSlots CenteredMomentCoreFloor
open QRH.Cycle092.WholeSlot QRH.Cycle092.TinyCore
local notation "O" => HeckeFamily.O

theorem terminal_original_zero_bound (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) :
    ∃ F : ℝ,0 < F ∧
    ∀ {Slot : Type*} (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
      (hH : RayOrthogonality.globalUnits M ≤ H)
      (U : ℝ) (η η₀ : Character) (mask A z : O) (t : ℝ)
      (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ) (j : Slot),
      0 ≤ σ j → w j=0 →
      ‖normalizedSlot η mask A z (originalPools M H 2 U w j)
        (originalCoefficients M H hH η₀ θ W U w σ v j) t (U^(w j))‖^2 ≤ F := by
  obtain ⟨B,hB,hcoeff⟩ := original_slot_coefficient_bound W hW hWs
  refine ⟨(256*B)^2,by positivity,?_⟩
  intro Slot M _ H hH U η η₀ mask A z t θ w σ v j hσ hw
  have hcap I (hI : originalCoefficients M H hH η₀ θ W U w σ v j I ≠ 0) : (I.absNorm:ℝ) ≤ 2 := by
    simpa only [hw,Real.rpow_zero,mul_one] using
      original_slot_norm_cap W hWs _ (U^(w j)) (σ j) (v j) I (by rw [hw,Real.rpow_zero];norm_num) hI
  have h := rowSlot_bound η mask A z (originalPools M H 2 U w j)
    (originalCoefficients M H hH η₀ θ W U w σ v j) t 2 B (by norm_num) hB.le
    (fun I _=>hcoeff _ _ _ _ I (by rw [hw,Real.rpow_zero];norm_num) hσ)
    (fun I _ hI=>hcap I hI)
  change ‖(Real.sqrt (U^(w j)):ℂ)⁻¹*rowSlot η mask A z _ _ t‖^2 ≤ _
  rw [hw,Real.rpow_zero,Real.sqrt_one]
  norm_num only [Complex.ofReal_one,inv_one,one_mul]
  norm_num only at h
  convert pow_le_pow_left₀ (norm_nonneg _) h 2 using 1 <;> ring

#print axioms terminal_original_zero_bound
end
end QRH.Cycle092.StrongPair
