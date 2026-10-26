import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle151RetainedF
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentAllocatedChildCapacity
open CenteredMomentEligibleEnergy CenteredMomentDivisorExtraction
open CenteredMomentAllocatedNaturalSource

local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Keep the full residual formal reduction in the total-length estimate
of an actual surviving positive retained row. In particular, the frozen-slot
loss remains a genuine capacity credit after plain clipping. -/
theorem supported_residual_total_length_retained
    (s : Data ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (Z : ℝ) (hZ : 1 < Z)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁ * X₂ = s.X₁ * s.X₂) (z : O)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P L a
      s.W₁ s.W₂ X₁ X₂ ≠ 0) :
    plainLogs L a Z X₁ X₂ + remainingLogs L a Z s.P ≤
      Real.logb Z (preVolume s) - Real.logb Z (formalReductionFactor L a s.P) +
        Real.logb Z (max 1 s.b₁ * max 1 s.b₂) := by
  obtain ⟨hs₁, hs₂⟩ := allocated_survives s L a z X₁ X₂ hX₁ hX₂ hne
  have hc := (clipping_loss_bound Z _ _ s.b₁ s.b₂ hZ
    (rawScale_pos L a X₁ hX₁ 0)
    (rawScale_pos L a X₂ hX₂ 1) hs₁ hs₂).2
  have he := affine_exact L a Z X₁ X₂ (1 / 6) 0 hZ hX₁ hX₂ s.P s.P_pos
  rw [hprod] at he
  norm_num at he
  change plainLogs L a Z X₁ X₂ + remainingLogs L a Z s.P =
    Real.logb Z (preVolume s) - Real.logb Z (formalReductionFactor L a s.P) +
      clippingLoss Z (rawScale L a X₁ 0) (rawScale L a X₂ 1) at he
  linarith only [he, hc]

end
end OAI.SevenEighths.Cycle151RetainedF

#print axioms OAI.SevenEighths.Cycle151RetainedF.supported_residual_total_length_retained
