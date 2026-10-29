/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ActualFiber
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDynamicSelection

/-! Summation of the actual detector's finite dictionary and dyadic fibers.
The cutoff is arbitrary in the original detector range; it is not fixed to1. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI.SevenEighths HeckeFamily HeckeDetectorWitnessRows

/-- Each row has exactly one actual label and dyadic length pair. The
finite summation retains all dictionary labels and both witness lengths. -/
theorem count_of_dictionary_fibers {Row Label : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row → Label → Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (witness : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (bound : ℝ)
    (h : ∀ (j : Label) (J K : Fin (dyadicLength U)),
      ((HeckeDetectorDynamicSelection.fiber rows χ U a ε tstar T allowance i witness j J K).card:ℝ)
        ≤ bound) :
    (rows.card:ℝ) ≤ (Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*bound := by
  have hcard := congrArg (Nat.cast : ℕ → ℝ)
    (HeckeDetectorDynamicSelection.card_eq_sum_fibers rows χ U a ε tstar T allowance i witness)
  simp only [Nat.cast_sum] at hcard
  rw [hcard]
  calc _ ≤ ∑ _j : Label, ∑ _J : Fin (dyadicLength U), ∑ _K : Fin (dyadicLength U), bound := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro J hJ
        exact Finset.sum_le_sum (fun K _ => h j J K)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end
end Qrh.JointDetector.RepeatedMarks
