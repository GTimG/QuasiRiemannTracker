/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliarySchedule

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Sil.Uneven.AuxiliarySource
noncomputable section

/-- A fixed, actually refined width partition, independent of moving
sources and of the ambient slot cardinality. -/
def widthCellIndex (s : ℝ) : ℤ :=
  max 0 (min 800000 (Int.ceil ((s-widthLo)/widthMesh)))

def widthCellUpper (s : ℝ) : ℝ :=
  widthLo+widthMesh*(widthCellIndex s:ℝ)

theorem widthCellIndex_bounds (s : ℝ) :
    0 ≤ widthCellIndex s ∧ widthCellIndex s ≤ 800000 := by
  unfold widthCellIndex
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem widthCellUpper_bounds {s : ℝ} (hs : s ∈ Set.Icc widthLo widthHi) :
    widthCellUpper s ∈ Set.Icc widthLo widthHi ∧
      s ≤ widthCellUpper s ∧ widthCellUpper s-s ≤ widthMesh := by
  have hm : (0:ℝ)<widthMesh := by norm_num [widthMesh]
  have hlo : 0 ≤ (s-widthLo)/widthMesh := div_nonneg (by linarith [hs.1]) hm.le
  have hhi : (s-widthLo)/widthMesh ≤ (800000:ℤ) := by
    apply (div_le_iff₀ hm).mpr
    norm_num [widthMesh,widthLo,widthHi] at *
    linarith [hs.2]
  have hc0 : 0 ≤ Int.ceil ((s-widthLo)/widthMesh) := Int.ceil_nonneg hlo
  have hc1 : Int.ceil ((s-widthLo)/widthMesh) ≤ 800000 := Int.ceil_le.mpr hhi
  have he : widthCellIndex s=Int.ceil ((s-widthLo)/widthMesh) := by
    unfold widthCellIndex
    rw [min_eq_right hc1,max_eq_right hc0]
  have hb := Int.le_ceil ((s-widthLo)/widthMesh)
  have ht := Int.ceil_lt_add_one ((s-widthLo)/widthMesh)
  have hp := mul_le_mul_of_nonneg_left hb hm.le
  have hq := mul_lt_mul_of_pos_left ht hm
  have ci0 : (0:ℝ) ≤ (widthCellIndex s:ℝ) := by exact_mod_cast (widthCellIndex_bounds s).1
  have ci1 : (widthCellIndex s:ℝ) ≤ 800000 := by exact_mod_cast (widthCellIndex_bounds s).2
  have hlo' := mul_nonneg hm.le ci0
  have hhi' := mul_le_mul_of_nonneg_left ci1 hm.le
  rw [←he] at hp hq
  rw [mul_div_cancel₀ _ hm.ne'] at hp
  rw [mul_add,mul_div_cancel₀ _ hm.ne'] at hq
  unfold widthCellUpper
  norm_num [widthMesh,widthLo,widthHi] at *
  constructor
  · constructor <;> linarith
  · constructor <;> linarith


end
end Sil.Uneven.AuxiliarySource
