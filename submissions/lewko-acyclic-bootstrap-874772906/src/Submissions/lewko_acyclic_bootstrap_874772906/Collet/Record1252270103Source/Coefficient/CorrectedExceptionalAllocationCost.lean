/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual frozen allocation weights pay the common norm after the centered
ordinary-factor contraction. No equality between raw scale and ideal norm is used. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedAllocatedNormCaps
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentCanonicalFirst CenteredMomentFiniteProfileExceptional
open QRH.Record1252270103Source.ForcedCost
open Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance correctedExceptionalAllocationCostDecidable : DecidableEq ι := Classical.decEq _

lemma child_forcedProfileCost (s : Input ι) (X R : Ideal O) (B : actualAllocations s.pools X)
    (τ : Character) (t : ℝ) : forcedProfileCost (child s X R B τ t)≤forcedProfileCost s := by
  have hp : (∏i:liveIndices B.val,s.M i.val)≤∏i,s.M i := by
    rw [Finset.prod_coe_sort]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  have hc : Fintype.card (liveIndices B.val)≤Fintype.card ι := by
    rw [Fintype.card_coe]
    exact Finset.card_le_univ _
  unfold forcedProfileCost
  change (∏i:liveIndices B.val,s.M i.val)^2*(max 1 s.upper)^Fintype.card (liveIndices B.val)≤_
  exact mul_le_mul
    (pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i.val))) hp 2)
    (pow_le_pow_right₀ (le_max_left _ _) hc)
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (sq_nonneg _)

lemma frozen_child_volume_cost (s : Input ι) (X R : Ideal O) (hX : X≠0)
    (B : actualAllocations s.pools X) (τ : Character) (t : ℝ) :
    ‖frozenCoefficient B X R s.ν s.W s.P‖^2*volume (child s X R B τ t)≤
      (forcedProfileCost s/(X.absNorm:ℝ))*volume s := by
  have hb:=alloc_ne s X B
  have hprod : finiteTupleProduct B.val=X := (Finset.mem_filter.mp B.property).2
  have hc:=frozen_normalized_cost B.val hb X R hX hprod s.ν s.W s.P s.M
    s.P_pos s.ν_bound s.W_bound s.M_ge_one s.lower s.upper s.lower_pos s.slot_support
  have hr : volume (child s X R B τ t)*rawReduction B.val s.P=volume s := by
    rw [child_volume_remaining]
    exact raw_scale_identity B.val hb (s.X₁*s.X₂) s.P
  have hred:=rawReduction_pos B.val hb s.P s.P_pos
  have he : ‖frozenCoefficient B X R s.ν s.W s.P‖^2*volume (child s X R B τ t)=
      (‖frozenCoefficient B X R s.ν s.W s.P‖^2/rawReduction B.val s.P)*volume s := by
    rw [←hr]
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right hc (volume_pos s).le

lemma frozen_child_centered_factor (s : Input ι) (X R : Ideal O) (hX : X≠0)
    (B : actualAllocations s.pools X) (τ : Character) (t L α A : ℝ)
    (hP : ∀i,1≤s.P i) (hα0 : 0≤α) (hα : α<1/2) :
    ‖frozenCoefficient B X R s.ν s.W s.P‖^2*
      (A*(max 1 (L/ordinaryNorm B.val))^(-α)*slotControl (child s X R B τ t).toData)^2*
        volume (child s X R B τ t)^2≤
    (forcedProfileCost s/(X.absNorm:ℝ))*(A*(max 1 L)^(-α)*slotControl s.toData)^2*(volume s)^2 := by
  have hf:=child_centered_energy_factor s X R B τ t L α A hP hα0 hα
  have hv:=frozen_child_volume_cost s X R hX B τ t
  have hn : 0≤‖frozenCoefficient B X R s.ν s.W s.P‖^2*volume (child s X R B τ t) :=
    mul_nonneg (sq_nonneg _) (volume_pos _).le
  have hF : 0≤(A*(max 1 L)^(-α)*slotControl s.toData)^2*volume s :=
    mul_nonneg (sq_nonneg _) (volume_pos s).le
  have h₁:=mul_le_mul_of_nonneg_left hf hn
  have h₂:=mul_le_mul_of_nonneg_right hv hF
  exact (le_of_eq (by ring)).trans (h₁.trans (h₂.trans_eq (by ring)))

lemma corrected_allocated_weighted_budget (s : Input ι) (X R : Ideal O) (hX : X≠0)
    (B : actualAllocations s.pools X) (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ))
    (Q C D seed : Ideal O) (U : Finset (CommonIndex C D))
    (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ)
    (hP : ∀i,1≤s.P i) (hα0 : 0≤α) (hα : α<1/2)
    (hZ : 0≤Z) (hCr : 0≤Cr) (hK₀ : 0≤K₀) :
    ‖frozenCoefficient B X R s.ν s.W s.P‖^2*
      correctedAllocatedBudget s X R B S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀≤
    (forcedProfileCost s/(X.absNorm:ℝ))*
      correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ := by
  let A:=C₀*(sourceControl S W₁*sourceControl S W₂)*Z^ε
  let G:=K₀*(seed.absNorm:ℝ)^εL*exceptionalRowCost Q C D U Z Cr Mrow*
    SchwartzMap.seminorm ℝ 0 0 Φ/(seed.absNorm:ℝ)
  have hcost:=exceptionalRowCost_nonneg Q C D U Z Cr Mrow hZ hCr
  have hsemi : 0≤SchwartzMap.seminorm ℝ 0 0 Φ := apply_nonneg _ _
  have hG : 0≤G := by dsimp [G];positivity
  have hf:=frozen_child_centered_factor s X R hX B s.η 0 Lraw α A hP hα0 hα
  have hp:=child_forcedProfileCost s X R B s.η 0
  have hn : 0≤‖frozenCoefficient B X R s.ν s.W s.P‖^2*
      (A*(max 1 (Lraw/ordinaryNorm B.val))^(-α)*slotControl (child s X R B s.η 0).toData)^2*
        volume (child s X R B s.η 0)^2 := by positivity
  have hh:=mul_le_mul_of_nonneg_left (mul_le_mul hp hf hn (forcedProfileCost_nonneg s)) hG
  unfold correctedAllocatedBudget correctedExceptionalBudget
  dsimp only [A,G] at hh
  convert hh using 1 <;> ring

theorem corrected_allocation_budget_bound (s : Input ι) (X R : Ideal O) (hX : X≠0)
    (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q C D seed : Ideal O)
    (U : Finset (CommonIndex C D)) (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ)
    (hP : ∀i,1≤s.P i) (hα0 : 0≤α) (hα : α<1/2)
    (hZ : 0≤Z) (hCr : 0≤Cr) (hK₀ : 0≤K₀) :
    allocationBudget s X R (fun B=>correctedAllocatedBudget s X R B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀)≤
      ((actualAllocations s.pools X).card:ℝ)^2*(forcedProfileCost s/(X.absNorm:ℝ))*
        correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ := by
  unfold allocationBudget
  calc
    _≤((actualAllocations s.pools X).card:ℝ)*∑_B : actualAllocations s.pools X,
      (forcedProfileCost s/(X.absNorm:ℝ))*
        correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun B _=>corrected_allocated_weighted_budget s X R hX B S W₁ W₂ Φ
        Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ hP hα0 hα hZ hCr hK₀)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_allocation_budget_bound
