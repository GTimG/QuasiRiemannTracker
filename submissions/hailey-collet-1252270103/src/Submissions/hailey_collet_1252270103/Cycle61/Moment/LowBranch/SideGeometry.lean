import Submissions.hailey_collet_1252270103.Cycle61.Moment.LowBranch.FinalDictionary
import Submissions.hailey_collet_1252270103.Cycle61.Physical.AllocationClipping
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation
open CenteredMomentDivisorRectangle CenteredMomentDivisorRaw CenteredMomentDivisorExtraction
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem source_plain_positive (s : Data α) (second : Bool) (j : Fin 2) :
    0 < Cycle61.Physical.sourcePlainScales s.toSource second j := by
  cases second <;> fin_cases j
  · exact s.X₁_pos
  · exact s.X₂_pos
  · exact s.Y₁_pos
  · exact s.Y₂_pos

/-- Selected-plain quotients are applied exactly once; clipping is the
positive part of their exact logarithmic reduction. -/
theorem final_plain_length (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (j : Fin 2) :
    length Z (finalPlain s second L a j) =
      max 0 (Real.logb Z (Cycle61.Physical.sourcePlainScales s.toSource second j)-
        Cycle61.Physical.actualPlainReduction Z L a j) := by
  have hn : (0:ℝ) < (Ideal.absNorm (selectedPlain L a j):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  have hx := source_plain_positive s second j
  change Real.logb Z (max 1 (max 1 (_/_))) = _
  rw [max_eq_right (le_max_left 1 (_/_))]
  change length Z (Cycle61.Physical.sourcePlainScales s.toSource second j/
    (Ideal.absNorm (selectedPlain L a j):ℝ)) = _
  rw [length_eq_max_log Z _ hZ (div_pos hx hn),Real.logb_div hx.ne' hn.ne']
  rfl

/-- The genuine retained cutoff never enlarges a clamped plain length. -/
theorem final_plain_length_le (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (j : Fin 2) :
    length Z (finalPlain s second L a j) ≤
      length Z (Cycle61.Physical.sourcePlainScales s.toSource second j) := by
  have hn : (1:ℝ) ≤ (Ideal.absNorm (selectedPlain L a j):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  have hx := source_plain_positive s second j
  have hdiv : Cycle61.Physical.sourcePlainScales s.toSource second j/
      (Ideal.absNorm (selectedPlain L a j):ℝ) ≤
      Cycle61.Physical.sourcePlainScales s.toSource second j :=
    (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr
      (le_mul_of_one_le_right hx.le hn)
  apply Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 _))
  change max 1 (max 1 (_/_)) ≤ max 1 _
  rw [max_eq_right (le_max_left 1 (_/_))]
  exact max_le_max_left 1 hdiv

/-- The actual residual slot family loses widths only. -/
theorem final_total_le (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (w : α → ℝ) (hw : ∀ j, 0 ≤ w j) :
    length Z (finalPlain s second L a 0)+length Z (finalPlain s second L a 1)+
        (9/2)*(∑ j ∈ liveIndices L a, w j) ≤
      length Z (Cycle61.Physical.sourcePlainScales s.toSource second 0)+
        length Z (Cycle61.Physical.sourcePlainScales s.toSource second 1)+
        (9/2)*(∑ j, w j) := by
  have hsum : (∑ j ∈ liveIndices L a, w j) ≤ ∑ j, w j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hw j)
  linarith [final_plain_length_le s second L a Z hZ 0,
    final_plain_length_le s second L a Z hZ 1]

#print axioms final_plain_length
#print axioms final_plain_length_le
#print axioms final_total_le
end
end OAI.SevenEighths.Cycle61Moment.LowBranch
