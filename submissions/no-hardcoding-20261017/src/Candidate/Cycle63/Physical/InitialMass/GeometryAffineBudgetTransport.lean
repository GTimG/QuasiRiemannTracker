/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryBudgetCardinality

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput

/-- Unit slot lower bounds make the support constant independent of the
number of original slots. -/
theorem geometry_affine_support_constant (N : ℕ) :
    geometrySupportConstant N 1 (1/4) (1/4) = 64 := by
  norm_num [geometrySupportConstant]

/-- The exceptional shell is exactly the compensator used by the full
geometry budget, for either orientation. -/
theorem geometry_affine_exceptional_shell_eq (N : ℕ) (Z : ℝ) (hZ : 1 < Z)
    (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)) :
    geometryAffineExceptionalShell reflected Z key =
      geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) key := by
  have hpow : Z ^ ((key.2 1 : ℝ) * Real.logb Z 2) = geometryDCompensator key := by
    rw [mul_comm, Real.rpow_mul (zero_lt_one.trans hZ).le,
      Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by norm_num : (0:ℝ)<2)]
    rfl
  rw [geometry_affine_support_constant]
  unfold geometryAffineExceptionalShell
  rw [hpow]
  cases reflected <;> norm_num [geometryHighFactor, one_div]

/-- Only the external allocation prefactor changes when passing from the
actual slot count to the ambient dictionary. The original Fourier cutoffs
remain inside the already-proved actual-count bound. -/
theorem geometry_affine_budget_to_ambient {α : Type} [Fintype α] [DecidableEq α]
    (T : Finset α) (s : Input T) (Z ξ height E : ℝ) (hZ : 1 < Z)
    (Ψ : 𝓢(ℝ,ℂ)) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)) (hE : 0 ≤ E)
    (hbound : geometryLiveBudget reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
      (fun q => normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
      (Fintype.card T) (9/4) height ≤ E) :
    geometryLiveBudget reflected s 1 1 Z Z ξ 1 (Real.logb Z (volume s))
      (zero_lt_one.trans hZ) key (fun q => normPhase (coordinateBlock s 1 1 Ψ Z Z ξ q))
      (Fintype.card α) (9/4) height ≤ (9/4:ℝ)^(Fintype.card α)*E := by
  let budget (r : {r : ℝ // 0 < r}) (n : ℕ) :=
    geometryLiveBudget reflected s 1 1 r.val Z ξ 1 (Real.logb Z (volume s)) r.property key
      (fun q => normPhase (coordinateBlock s 1 1 Ψ r.val Z ξ q)) n (9/4) height
  have hrad : (⟨Z^(1:ℝ), Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)⟩ :
      {r : ℝ // 0 < r}) = ⟨Z, zero_lt_one.trans hZ⟩ := Subtype.ext (Real.rpow_one Z)
  have hboundZ : budget ⟨Z, zero_lt_one.trans hZ⟩ (Fintype.card T) ≤ E := by
    rw [←hrad]
    exact hbound
  have hn : Fintype.card T ≤ Fintype.card α :=
    Fintype.card_le_of_injective (fun i : T => i.val) Subtype.val_injective
  have hb := geometry_live_budget_card_bound (ι := T) reflected s 1 1 Z Z ξ 1
    (Real.logb Z (volume s)) (zero_lt_one.trans hZ) key
    (fun q => normPhase (coordinateBlock s 1 1 Ψ Z Z ξ q))
    (Fintype.card T) (Fintype.card α) hn (9/4) height E hE hboundZ
  exact hb.trans_eq (by rw [max_eq_right (by norm_num : (1:ℝ) ≤ 9/4)])

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_support_constant
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_exceptional_shell_eq
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_budget_to_ambient
