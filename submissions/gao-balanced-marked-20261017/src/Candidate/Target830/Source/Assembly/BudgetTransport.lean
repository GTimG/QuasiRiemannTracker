import Candidate.Target830.Source.Assembly.BudgetCardinality
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineBudgetTransport
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open scoped Classical SchwartzMap
open Cycle63InitialMass CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
/-- Only the external allocation prefactor changes when passing from the
actual slot count to the ambient dictionary. The original Fourier cutoffs
remain inside the already-proved actual-count bound. -/
theorem geometry_affine_budget_to_ambient {α : Type} [Fintype α] [DecidableEq α]
    (T : Finset α) (s : Input T) (Z ξ height E : ℝ) (hZ : 1 < Z)
    (Ψ : 𝓢(ℝ,ℂ)) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)) (hE : 0 ≤ E)
    (hbound : balancedLiveBudget reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
      (fun q => normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
      (Fintype.card T) (9/4) height ≤ E) :
    balancedLiveBudget reflected s 1 1 Z Z ξ 1 (Real.logb Z (volume s))
      (zero_lt_one.trans hZ) key (fun q => normPhase (coordinateBlock s 1 1 Ψ Z Z ξ q))
      (Fintype.card α) (9/4) height ≤ (9/4:ℝ)^(Fintype.card α)*E := by
  let budget (r : {r : ℝ // 0 < r}) (n : ℕ) :=
    balancedLiveBudget reflected s 1 1 r.val Z ξ 1 (Real.logb Z (volume s)) r.property key
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
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.geometry_affine_budget_to_ambient
