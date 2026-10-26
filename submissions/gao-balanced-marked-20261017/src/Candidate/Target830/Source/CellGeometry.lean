import Candidate.Target830.Source.Schedule

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source
noncomputable section

/-- The finite mesh is fixed before any ambient dictionary is chosen. -/
def widthCellAtIndex (j : ℤ) : ℝ := widthLower+sourceWidthMesh*(j:ℝ)

theorem widthCellAtIndex_bounds {j : ℤ}
    (hj : j ∈ Finset.Icc (0:ℤ) 600000) :
    widthCellAtIndex j ∈ Set.Icc widthLower widthUpper := by
  rcases Finset.mem_Icc.mp hj with ⟨hlo,hhi⟩
  have hlo' : (0:ℝ)≤(j:ℝ) := by exact_mod_cast hlo
  have hhi' : (j:ℝ)≤600000 := by exact_mod_cast hhi
  unfold widthCellAtIndex
  norm_num [widthLower,widthUpper,sourceWidthMesh] at *
  constructor <;> linarith

theorem widthCellIndex_mem (s : ℝ) :
    widthCellIndex s ∈ Finset.Icc (0:ℤ) 600000 :=
  Finset.mem_Icc.mpr (widthCellIndex_bounds s)

theorem widthCellUpper_eq (s : ℝ) :
    widthCellUpper s=widthCellAtIndex (widthCellIndex s) := rfl

theorem amplifier_pos (P : SourcePlane) {b : ℝ}
    (hb : b ∈ Set.Icc widthLower widthUpper) : 0<P.amp b :=
  lt_of_lt_of_le (source_guards P hb).2.1 (source_guards P hb).2.2.1

/-- The cell volume is computed from the original width, before extraction. -/
theorem normalized_cell_volume (P : SourcePlane) {n₁ n₂ slots : ℝ}
    (hslots : slots ∈ Set.Icc widthLower widthUpper)
    (hcone : n₁+n₂+P.lambda*slots≤P.B) :
    n₁+n₂+slots≤P.total (widthCellUpper slots) := by
  have hs := widthCellUpper_bounds hslots
  have hl : 1<P.lambda := by cases P <;> norm_num [SourcePlane.lambda]
  have hm : 0≤P.lambda-1 := by linarith
  have hp := mul_le_mul_of_nonneg_left (show widthCellUpper slots-sourceWidthMesh≤slots by linarith [hs.2.2]) hm
  unfold SourcePlane.total
  nlinarith

end
end OAI.SevenEighths.Target830.Source
#print axioms OAI.SevenEighths.Target830.Source.widthCellAtIndex_bounds
#print axioms OAI.SevenEighths.Target830.Source.widthCellIndex_mem
#print axioms OAI.SevenEighths.Target830.Source.amplifier_pos
#print axioms OAI.SevenEighths.Target830.Source.normalized_cell_volume
