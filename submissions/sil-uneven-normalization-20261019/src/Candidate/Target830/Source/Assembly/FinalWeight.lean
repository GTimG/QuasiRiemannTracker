import Candidate.Target830.Source.BalancedColumns
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineBudgetTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalWeight

/- Original module: Candidate.Target830.Source.Assembly.BudgetCardinality. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentLogDyadic
open Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

/-- The outer cardinality parameter is only a fixed prefactor. Analytic
families can use their actual slot cardinality without changing any Fourier
scale, then pay the ambient-cardinality factor outside the estimate. -/
theorem geometry_live_budget_card_scale (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (n N : ℕ) (hn : n≤ N) (b t : ℝ) :
    balancedLiveBudget reflected s R seed K Z ξ M A hK key weight N b t=
      (max 1 b)^(N-n)*balancedLiveBudget reflected s R seed K Z ξ M A hK key weight n b t := by
  have hp : (max 1 b)^N=(max 1 b)^(N-n)*(max 1 b)^n := by
    rw [←pow_add,Nat.sub_add_cancel hn]
  unfold balancedLiveBudget
  simp only [Finset.mul_sum,hp]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A nonnegative actual-cardinality budget pays the fixed ambient budget
with a source-independent factor. -/
theorem geometry_live_budget_card_bound (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (n N : ℕ) (hn : n≤ N) (b t E : ℝ) (hE : 0≤ E)
    (hbound : balancedLiveBudget reflected s R seed K Z ξ M A hK key weight n b t≤ E) :
    balancedLiveBudget reflected s R seed K Z ξ M A hK key weight N b t≤(max 1 b)^N*E := by
  rw [geometry_live_budget_card_scale reflected s R seed K Z ξ M A hK key weight n N hn b t]
  apply (mul_le_mul_of_nonneg_left hbound (pow_nonneg (le_trans (by norm_num) (le_max_left 1 b)) _)).trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left 1 b) (Nat.sub_le N n)) hE

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.geometry_live_budget_card_scale
#print axioms OAI.SevenEighths.Target830.Source.Assembly.geometry_live_budget_card_bound
end

/- Original module: Candidate.Target830.Source.Assembly.BudgetTransport. -/
section
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
end

/- Original module: Candidate.Target830.Source.Assembly.FinalWeight. -/
section
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
    (T : Finset α) (s : Input T) (Z ξ ε C control height : ℝ) (hZ : 1< Z)
    (J K : ℕ) (Ψ : 𝓢(ℝ,ℂ)) (reflected : Bool) (key : ℤ×(Fin 5→ℤ))
    (t u : ℝ) (hC : 0≤ C) (hc : 0≤ control) (hh : 0≤ height)
    (hbound : balancedLiveBudget reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
      (fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
      (Fintype.card T) (9/4) (s.t+2*Real.pi*(u-(if reflected then -t else t))) ≤
      C*geometryHighFactor reflected 64 key*control*(1+|s.t|+height)^J*
        (1+‖s.t+2*Real.pi*(u-(if reflected then -t else t))‖)^K*Z^ε) :
    let E := (9/4:ℝ)^(Fintype.card α)*C*(1+2*(64:ℝ)^2)*(1+|2*Real.pi|)^K*
      control*(1+|s.t|+height)^(J+K)*Z^ε
    balancedLiveBudget reflected s 1 1 Z Z ξ 1 (Real.logb Z (volume s))
      (zero_lt_one.trans hZ) key (fun q=> normPhase (coordinateBlock s 1 1 Ψ Z Z ξ q))
      (Fintype.card α) (9/4) (s.t+2*Real.pi*(u-(if reflected then -t else t))) ≤
      ((if reflected then E/geometryDCompensator key else E*geometryDCompensator key)*
        (1+‖t‖)^K)*(1+‖u‖)^(2*K) := by
  intro E
  have hs : 0≤ geometryHighFactor reflected 64 key :=
    (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  have hz : 0≤ Z^ε := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hw := geometry_affine_final_height_weight J K s.t height t u reflected hh
  have hpaid := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw (mul_nonneg (mul_nonneg hC hs) hc)) hz
  have hactual := hbound.trans (by convert hpaid using 1; ring)
  have hnonneg : 0≤ C*geometryHighFactor reflected 64 key*control*
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
end
