/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Collecting bounds on the actual modified children with the exact finite
allocation cardinality and frozen coefficient weights. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.CoupledAllocation

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def allocationBudget (s : Input ι) (C R : Ideal O)
    (E : actualAllocations s.pools C→ℝ) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*∑B : actualAllocations s.pools C,
    ‖frozenCoefficient B C R s.ν s.W s.P‖^2*E B

theorem allocationBudget_nonneg (s : Input ι) (C R : Ideal O)
    (E : actualAllocations s.pools C→ℝ) (hE : ∀B,0≤E B) :
    0≤allocationBudget s C R E := by
  unfold allocationBudget
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun B _=>mul_nonneg (sq_nonneg _) (hE B)))

theorem allocatedDivisorEnergy_le (s : Input ι) (modifier : Tuple ι→ℂ) (C R L : Ideal O)
    (τ : Character) (t : ℝ) (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K q : ℝ)
    (E : actualAllocations s.pools C→ℝ)
    (h : ∀B : actualAllocations s.pools C,frozenCoefficient B C R s.ν s.W s.P≠0 →
      childDivisorEnergy s modifier C R L B τ t keep W K≤E B*q) :
    allocatedDivisorEnergy s modifier C R L τ t keep W K≤allocationBudget s C R E*q := by
  unfold allocatedDivisorEnergy allocationBudget
  calc
    _≤((actualAllocations s.pools C).card:ℝ)*∑B : actualAllocations s.pools C,
        ‖frozenCoefficient B C R s.ν s.W s.P‖^2*(E B*q) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      by_cases hn : frozenCoefficient B C R s.ν s.W s.P=0
      · simp only [hn,norm_zero,zero_pow (by decide : 2≠0),zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (h B hn) (sq_nonneg _)
    _=_ := by simp only [mul_assoc,Finset.sum_mul]

theorem allocatedDivisorEnergy_divisor_bound (s : Input ι) (modifier : Tuple ι→ℂ)
    (C R L : Ideal O) (τ : Character) (t : ℝ) (keep : O→Prop)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (J : ℕ) (E : actualAllocations s.pools C→ℝ)
    (h : ∀B : actualAllocations s.pools C,frozenCoefficient B C R s.ν s.W s.P≠0 →
      childDivisorEnergy s modifier C R L B τ t keep W K≤
        (E B/(L.absNorm:ℝ))*(1+‖t‖)^(2*J)) :
    allocatedDivisorEnergy s modifier C R L τ t keep W K≤
      (allocationBudget s C R E/(L.absNorm:ℝ))*(1+‖t‖)^(2*J) := by
  have hh := allocatedDivisorEnergy_le s modifier C R L τ t keep W K
    ((1/(L.absNorm:ℝ))*(1+‖t‖)^(2*J)) E (by
      intro B hn
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using h B hn)
  convert hh using 1 <;> ring

end
end OAI.SevenEighths.Record1252270103Second

#print axioms OAI.SevenEighths.Record1252270103Second.allocatedDivisorEnergy_divisor_bound
