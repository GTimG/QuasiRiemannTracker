import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineBudgetTransport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryBudgetJoin
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical SchwartzMap HeckeNotation
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput

/-- The shifted first height contributes independent original and Mellin
weights. The second Mellin exponent is rounded up to an even degree. -/
theorem geometry_affine_final_height_weight (J K : ℕ)
    (base height t u : ℝ) (reflected : Bool) (hh : 0≤height) :
    (1+|base|+height)^J*
      (1+‖base+2*Real.pi*(u-(if reflected then -t else t))‖)^K ≤
    (1+|2*Real.pi|)^K*(1+|base|+height)^(J+K)*
      (1+‖t‖)^K*(1+‖u‖)^(2*K) := by
  have h := geometry_affine_exceptional_mellin_weight K base height t u reflected hh
  have hu : (1+‖u‖)^K≤(1+‖u‖)^(2*K) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg u]) (by omega)
  have hbase : 0≤1+|base|+height := by positivity
  have h₁ := mul_le_mul_of_nonneg_left h (pow_nonneg hbase J)
  have h₂ := mul_le_mul_of_nonneg_left hu
    (show 0≤(1+|2*Real.pi|)^K*(1+|base|+height)^(J+K)*(1+‖t‖)^K by positivity)
  apply h₁.trans
  convert h₂ using 1
  rw [pow_add]
  ring

/-- Convert an actual-slot budget to the ambient budget and the reciprocal
side convention used in the literal affine assembly. The analytic branch
bound remains explicit. -/
theorem geometry_affine_final_budget_weight {α : Type} [Fintype α] [DecidableEq α]
    (T : Finset α) (s : Input T) (Z ξ ε C control height : ℝ) (hZ : 1<Z)
    (J K : ℕ) (Ψ : 𝓢(ℝ,ℂ)) (reflected : Bool) (key : ℤ×(Fin 5→ℤ))
    (t u : ℝ) (hC : 0≤C) (hc : 0≤ control) (hh : 0≤height)
    (hbound : geometryLiveBudget reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
      (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
      (Fintype.card T) (9/4) (s.t+2*Real.pi*(u-(if reflected then -t else t))) ≤
      C*geometryHighFactor reflected 64 key*control*(1+|s.t|+height)^J*
        (1+‖s.t+2*Real.pi*(u-(if reflected then -t else t))‖)^K*Z^ε) :
    let E := (9/4:ℝ)^(Fintype.card α)*C*(1+2*(64:ℝ)^2)*(1+|2*Real.pi|)^K*
      control*(1+|s.t|+height)^(J+K)*Z^ε
    geometryLiveBudget reflected s 1 1 Z Z ξ 1 (Real.logb Z (volume s))
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

/-- Convert an actual-slot budget of a parent with puncture `R`, seed `seed` and radial scale `Z^Mrow` to the ambient budget and the
reciprocal side convention used in the literal affine assembly. The analytic branch bound remains explicit, with the real factor
`Y` standing for the scale power and any linear term. -/
theorem geometry_affine_parent_final_budget_weight {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (s : Input T) (R seed : Ideal O) (Z Mrow ξ C control height Y : ℝ) (hZ : 1<Z)
    (J K : ℕ) (Ψ : 𝓢(ℝ,ℂ)) (reflected : Bool) (key : ℤ×(Fin 5→ℤ))
    (t u : ℝ) (hC : 0≤C) (hc : 0≤ control) (hh : 0≤height) (hY : 0≤Y)
    (hbound : geometryLiveBudget reflected s R seed (Z^Mrow) Z ξ Mrow (Real.logb Z (volume s))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key
      (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q))
      (Fintype.card T) (9/4) (s.t+2*Real.pi*(u-(if reflected then -t else t))) ≤
      C*geometryHighFactor reflected 64 key*control*(1+|s.t|+height)^J*
        (1+‖s.t+2*Real.pi*(u-(if reflected then -t else t))‖)^K*Y) :
    let E := (9/4:ℝ)^(Fintype.card α)*C*(1+2*(64:ℝ)^2)*(1+|2*Real.pi|)^K*
      control*(1+|s.t|+height)^(J+K)*Y
    geometryLiveBudget reflected s R seed (Z^Mrow) Z ξ Mrow (Real.logb Z (volume s))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key
      (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q))
      (Fintype.card α) (9/4) (s.t+2*Real.pi*(u-(if reflected then -t else t))) ≤
      ((if reflected then E/geometryDCompensator key else E*geometryDCompensator key)*(1+‖t‖)^K)*
        (1+‖u‖)^(2*K) := by
  intro E
  have hs : 0≤geometryHighFactor reflected 64 key :=
    (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  have hw := geometry_affine_final_height_weight J K s.t height t u reflected hh
  have hpaid := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw (mul_nonneg (mul_nonneg hC hs) hc)) hY
  have hactual := hbound.trans (by convert hpaid using 1; ring)
  have hnonneg : 0≤C*geometryHighFactor reflected 64 key*control*
      ((1+|2*Real.pi|)^K*(1+|s.t|+height)^(J+K)*(1+‖t‖)^K*(1+‖u‖)^(2*K))*Y := by
    positivity
  have hambient := geometry_affine_parent_budget_to_ambient T s R seed Z Mrow ξ
    (s.t+2*Real.pi*(u-(if reflected then -t else t))) _ hZ Ψ reflected key hnonneg hactual
  have hside := geometry_physical_side_join reflected 64
    ((9/4:ℝ)^(Fintype.card α)*C) ((1+|2*Real.pi|)^K*control*
      (1+|s.t|+height)^(J+K)*Y*(1+‖t‖)^K*(1+‖u‖)^(2*K)) _ key
      (by positivity) (by positivity) (by convert hambient using 1; ring)
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hside ⊢
  · convert hside using 1
    dsimp only [E]
    ring
  · convert hside using 1
    dsimp only [E]
    ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
