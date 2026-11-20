/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Bound a punctured positive product by a sum over retained complete prime slots. -/
import Candidate.C092.transport.CofactorCleanEnergy
import Candidate.C092.transport.WholeSlotSelection

namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ConcretePrimeRowBridge ActualEisensteinCubic
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource QRH.Cycle092.WholeSlot QRH.Cycle092.OrdinaryColumn
local notation "O" => ActualEisensteinCubic.O

theorem product_error_square {ι : Type} [Fintype ι] [DecidableEq ι]
    (z c : ι → ℂ) (E : ℝ) (hE : 1 ≤ E) (h : ∀ i, ‖z i-c i‖ ≤ E) :
    (∏ i, ‖z i‖^2) ≤ (2*E^2)^Fintype.card ι *
      ∑ T ∈ (Finset.univ : Finset ι).powerset, ∏ i ∈ T, ‖c i‖^2 := by
  have ht (i : ι) : ‖z i‖^2 ≤ (2*E^2)*(1+‖c i‖^2) := by
    have hz := (norm_add_le (z i-c i) (c i))
    rw [sub_add_cancel] at hz
    have hb : ‖z i‖ ≤ E+‖c i‖ := by linarith only [hz,h i]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hE2 : 1 ≤ E^2 := one_le_pow₀ hE
    nlinarith only [hsq,sq_nonneg (E-‖c i‖),mul_nonneg (sub_nonneg.mpr hE2) (sq_nonneg ‖c i‖)]
  calc
    _ ≤ ∏ i, (2*E^2)*(1+‖c i‖^2) := Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun i _ => ht i)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_one_add]; simp

/-- The weighted error expansion can use any true bound for each retained
subset, including the empty subset. Its cardinal factor depends only on the
fixed slot family. No complete prime annulus is assigned a deletion mask. -/
theorem weighted_marked_subsets {ι α : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (z c : α → ι → ℂ) (w : α → ℝ) (E K : ℝ)
    (hE : 1 ≤ E) (hw : ∀ u ∈ s, 0 ≤ w u) (herr : ∀ u ∈ s, ∀ i, ‖z u i-c u i‖ ≤ E)
    (hsub : ∀ T : Finset ι, (∑ u ∈ s,(∏ i ∈ T, ‖c u i‖^2)*w u) ≤ K) :
    (∑ u ∈ s, (∏ i, ‖z u i‖^2)*w u) ≤ (2*E^2)^Fintype.card ι * 2^Fintype.card ι * K := by
  let p := (Finset.univ : Finset ι).powerset
  let A := (2*E^2)^Fintype.card ι
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ u ∈ s, (A * ∑ T ∈ p, ∏ i ∈ T, ‖c u i‖^2)*w u :=
      Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_right (product_error_square _ _ E hE (herr u hu)) (hw u hu))
    _ = A * ∑ T ∈ p, ∑ u ∈ s, (∏ i ∈ T, ‖c u i‖^2)*w u := by
      simp_rw [mul_assoc,Finset.sum_mul]; rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ A * ∑ _T ∈ p, K := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun T _ => hsub T)) hA
    _ = _ := by simp [p,A,mul_assoc]

#print axioms weighted_marked_subsets
end
end QRH.Cycle092.CofactorOrdinary
