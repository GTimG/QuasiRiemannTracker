/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryGuards

set_option autoImplicit false
namespace Sil.Uneven.AuxiliarySource
noncomputable section

def widthCellAtIndex (j : ℤ) : ℝ := widthLo+widthMesh*(j:ℝ)

theorem widthCellAtIndex_bounds {j : ℤ}
    (hj : j ∈ Finset.Icc (0:ℤ) 800000) :
    widthCellAtIndex j ∈ Set.Icc widthLo widthHi := by
  rcases Finset.mem_Icc.mp hj with ⟨hlo,hhi⟩
  have hlo' : (0:ℝ) ≤ (j:ℝ) := by exact_mod_cast hlo
  have hhi' : (j:ℝ) ≤ 800000 := by exact_mod_cast hhi
  unfold widthCellAtIndex
  norm_num [widthLo,widthHi,widthMesh] at *
  constructor <;> linarith

theorem widthCellIndex_mem (s : ℝ) :
    widthCellIndex s ∈ Finset.Icc (0:ℤ) 800000 :=
  Finset.mem_Icc.mpr (widthCellIndex_bounds s)


theorem amplifier_pos {b : ℝ} (hb : b ∈ Set.Icc widthLo widthHi) : 0 < amp b :=
  lt_of_lt_of_le (scheduling_guards hb).2.1 (scheduling_guards hb).2.2.1

theorem amplifier_bounds {b : ℝ} (hb : b ∈ Set.Icc widthLo widthHi) :
    amplifierMinimum ≤ amp b ∧ amp b ≤ 1/75 :=
  ⟨(scheduling_guards hb).2.2.1,(scheduling_guards hb).2.2.2.1⟩

theorem normalized_cell_volume {n₁ n₂ slots : ℝ}
    (hslots : slots ∈ Set.Icc widthLo widthHi)
    (hcone : n₁+n₂+lambda*slots ≤ B) :
    n₁+n₂+slots ≤ total (widthCellUpper slots) := by
  have hs := widthCellUpper_bounds hslots
  have hl : 1 < lambda := by norm_num [lambda]
  have hm : 0 ≤ lambda-1 := by linarith
  have hp := mul_le_mul_of_nonneg_left
    (show widthCellUpper slots-widthMesh ≤ slots by linarith [hs.2.2]) hm
  unfold total
  nlinarith

end
end Sil.Uneven.AuxiliarySource
