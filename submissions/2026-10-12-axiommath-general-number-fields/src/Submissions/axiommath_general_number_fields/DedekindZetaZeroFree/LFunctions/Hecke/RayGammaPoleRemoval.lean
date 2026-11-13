/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Hecke/RayGammaPoleRemoval.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Analysis.EntireDividedDifference
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Profiles.RayParityFourierMellin

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.AbelianQuotient.RayGammaPoleRemoval

def completedEntirePart (h E : ℂ → ℂ) (A B : ℂ) : ℂ → ℂ :=
  fun s ↦ h s * E s + A * entireDividedDifference h 1 s -
    B * entireDividedDifference h 0 s

theorem completed_pole_decomposition (h E : ℂ → ℂ) (h0 : h 0 = 0)
    (A B s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    h s * (E s + A / (s - 1) - B / s) =
      completedEntirePart h E A B s + (A * h 1) / (s - 1) := by
  rw [completedEntirePart, entireDividedDifference_of_ne h 1 s hs1,
    entireDividedDifference_of_zero h 0 s h0 hs0]
  field_simp
  ring

end DedekindZetaZeroFree.AbelianQuotient.RayGammaPoleRemoval

end
