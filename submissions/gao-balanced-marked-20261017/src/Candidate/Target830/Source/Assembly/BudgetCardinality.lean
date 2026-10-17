/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target830.Source.BalancedColumns

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
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (n N : ℕ) (hn : n≤N) (b t : ℝ) :
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
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (n N : ℕ) (hn : n≤N) (b t E : ℝ) (hE : 0≤E)
    (hbound : balancedLiveBudget reflected s R seed K Z ξ M A hK key weight n b t≤E) :
    balancedLiveBudget reflected s R seed K Z ξ M A hK key weight N b t≤(max 1 b)^N*E := by
  rw [geometry_live_budget_card_scale reflected s R seed K Z ξ M A hK key weight n N hn b t]
  apply (mul_le_mul_of_nonneg_left hbound (pow_nonneg (le_trans (by norm_num) (le_max_left 1 b)) _)).trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left 1 b) (Nat.sub_le N n)) hE

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.geometry_live_budget_card_scale
#print axioms OAI.SevenEighths.Target830.Source.Assembly.geometry_live_budget_card_bound
