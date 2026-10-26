/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform small-power payment for both full allocation cardinalities. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.ExceptionalWindow.Pair
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocationCost
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile CenteredMomentSecondWindowBudget
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentCanonicalFirst
open Record1252270103Second
local notation "O" => ActualEisensteinCubic.O
local notation "frozenCost" => CenteredMomentCommonExceptionalCost.frozenProfile

theorem paired_allocation_cardinality (N : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ A : ℝ, 0<A ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (s : Input ι) (C D : Ideal O), C≠0 → D≠0 → ∀ α : ℝ,
      ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
        ((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1) ≤
      A*((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1+η) := by
  obtain ⟨A,hA,hcard⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) η hη
  refine ⟨A^2,by positivity,?_⟩
  intro ι inst hι s C D hC hD α
  have hn : Fintype.card (ι⊕Fin 2)≤N+2 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hc := hcard hn s.pools C hC
  have hd := hcard hn s.pools D hD
  have hNC : (0:ℝ)<C.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hND : (0:ℝ)<D.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hp := mul_le_mul hc hd (Nat.cast_nonneg _) (by positivity)
  calc
    _≤(A*(C.absNorm:ℝ)^η)*(A*(D.absNorm:ℝ)^η)*
      ((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (mul_nonneg hNC.le hND.le) _)
    _=A^2*((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1+η) := by
      rw [Real.rpow_add (mul_pos hNC hND)]
      simp only [Real.mul_rpow hNC.le hND.le]
      ring

/-- The cardinality constant depends only on the ambient slot cap and its loss. -/
theorem corrected_paired_window_slot_cap (N : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ A : ℝ, 0<A ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
    ∀ (s : Input ι) (C D RC RD : Ideal O), C≠0 → D≠0 →
    ∀ (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q seed : Ideal O)
      (U : Finset (CommonIndex C D)) (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ) (J : ℕ) (t : ℝ),
    0≤α → 0≤Z → 0≤Cr → 0≤K₀ →
    windowBudget J t (allocationBudget s C RC
      (fun B => correctedAllocatedBudget s C RC B S W₁ W₂ Φ Q C D seed U
        Z ε εL α Lraw Cr Mrow C₀ K₀)) *
    windowBudget J t (allocationBudget s D RD
      (fun B => correctedAllocatedBudget s D RD B S W₁ W₂ Φ Q C D seed U
        Z ε εL α Lraw Cr Mrow C₀ K₀)) ≤
    A*((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1+η)*(frozenCost s)^2*
      correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀*
      (heightEnvelope t^J*profileMoment J)^2 := by
  obtain ⟨A,hA,hcard⟩ := paired_allocation_cardinality N η hη
  refine ⟨A,hA,?_⟩
  intro ι inst hι s C D RC RD hC hD S W₁ W₂ Φ Q seed U Z ε εL α Lraw Cr Mrow C₀ K₀
    J t hα hZ hCr hK₀
  have hE := correctedExceptionalBudget_nonneg s S W₁ W₂ Φ Q C D seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀ hZ hCr hK₀
  exact (corrected_paired_window s C D RC RD hC hD S W₁ W₂ Φ Q seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀ J t hα hZ hCr hK₀).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcard hι s C D hC hD α) (sq_nonneg _)) hE)
      (sq_nonneg _))
end
end OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.paired_allocation_cardinality
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.corrected_paired_window_slot_cap
