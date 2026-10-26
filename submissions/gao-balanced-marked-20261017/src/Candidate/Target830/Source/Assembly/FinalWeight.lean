import Candidate.Target830.Source.Assembly.BudgetTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalWeight
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open scoped Classical SchwartzMap
open Cycle63InitialMass CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
/-- Convert an actual-slot budget to the ambient budget and the reciprocal
side convention used in the literal affine assembly. The analytic branch
bound remains explicit. -/
theorem geometry_affine_final_budget_weight {α : Type} [Fintype α] [DecidableEq α]
    (T : Finset α) (s : Input T) (Z ξ ε C control height : ℝ) (hZ : 1<Z)
    (J K : ℕ) (Ψ : 𝓢(ℝ,ℂ)) (reflected : Bool) (key : ℤ×(Fin 5→ℤ))
    (t u : ℝ) (hC : 0≤C) (hc : 0≤control) (hh : 0≤height)
    (hbound : balancedLiveBudget reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
      (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
      (Fintype.card T) (9/4) (s.t+2*Real.pi*(u-(if reflected then -t else t))) ≤
      C*geometryHighFactor reflected 64 key*control*(1+|s.t|+height)^J*
        (1+‖s.t+2*Real.pi*(u-(if reflected then -t else t))‖)^K*Z^ε) :
    let E := (9/4:ℝ)^(Fintype.card α)*C*(1+2*(64:ℝ)^2)*(1+|2*Real.pi|)^K*
      control*(1+|s.t|+height)^(J+K)*Z^ε
    balancedLiveBudget reflected s 1 1 Z Z ξ 1 (Real.logb Z (volume s))
      (zero_lt_one.trans hZ) key (fun q=>normPhase (coordinateBlock s 1 1 Ψ Z Z ξ q))
      (Fintype.card α) (9/4) (s.t+2*Real.pi*(u-(if reflected then -t else t))) ≤
      ((if reflected then E/geometryDCompensator key else E*geometryDCompensator key)*
        (1+‖t‖)^K)*(1+‖u‖)^(2*K) := by
  intro E
  have hs : 0≤geometryHighFactor reflected 64 key :=
    (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  have hz : 0≤Z^ε := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hw := geometry_affine_final_height_weight J K s.t height t u reflected hh
  have hpaid := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw (mul_nonneg (mul_nonneg hC hs) hc)) hz
  have hactual := hbound.trans (by convert hpaid using 1; ring)
  have hnonneg : 0≤C*geometryHighFactor reflected 64 key*control*
      ((1+|2*Real.pi|)^K*(1+|s.t|+height)^(J+K)*(1+‖t‖)^K*(1+‖u‖)^(2*K))*Z^ε := by
    positivity
  have hambient := geometry_affine_budget_to_ambient T s Z ξ
    (s.t+2*Real.pi*(u-(if reflected then -t else t))) _ hZ Ψ reflected key hnonneg hactual
  have hside := geometry_physical_side_join reflected 64
    ((9/4:ℝ)^(Fintype.card α)*C) ((1+|2*Real.pi|)^K*control*
      (1+|s.t|+height)^(J+K)*Z^ε*(1+‖t‖)^K*(1+‖u‖)^(2*K)) _ key
      (by positivity) (by positivity) (by convert hambient using 1; ring)
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hside ⊢
  · convert hside using 1
    dsimp only [E]
    ring
  · convert hside using 1
    dsimp only [E]
    ring

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.geometry_affine_final_budget_weight
