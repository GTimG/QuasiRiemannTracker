import Candidate.Uneven.MainParameters

/- Original module: Candidate.Uneven.MainWidthGrid. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Sil.Uneven.MainSource
noncomputable section

/-- A fixed, actually refined width partition, independent of moving
sources and of the ambient slot cardinality. -/
def widthCellIndex (s : ℝ) : ℤ :=
  max 0 (min 600000000 (Int.ceil ((s-widthLo)/widthMesh)))

def widthCellUpper (s : ℝ) : ℝ :=
  widthLo+widthMesh*(widthCellIndex s:ℝ)

theorem widthCellIndex_bounds (s : ℝ) :
    0 ≤ widthCellIndex s ∧ widthCellIndex s ≤ 600000000 := by
  unfold widthCellIndex
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem widthCellUpper_bounds {s : ℝ} (hs : s ∈ Set.Icc widthLo widthHi) :
    widthCellUpper s ∈ Set.Icc widthLo widthHi ∧
      s ≤ widthCellUpper s ∧ widthCellUpper s-s ≤ widthMesh := by
  have hm : (0:ℝ)<widthMesh := by norm_num [widthMesh]
  have hlo : 0 ≤ (s-widthLo)/widthMesh := div_nonneg (by linarith [hs.1]) hm.le
  have hhi : (s-widthLo)/widthMesh ≤ (600000000:ℤ) := by
    apply (div_le_iff₀ hm).mpr
    norm_num [widthMesh,widthLo,widthHi] at *
    linarith [hs.2]
  have hc0 : 0 ≤ Int.ceil ((s-widthLo)/widthMesh) := Int.ceil_nonneg hlo
  have hc1 : Int.ceil ((s-widthLo)/widthMesh) ≤ 600000000 := Int.ceil_le.mpr hhi
  have he : widthCellIndex s=Int.ceil ((s-widthLo)/widthMesh) := by
    unfold widthCellIndex
    rw [min_eq_right hc1,max_eq_right hc0]
  have hb := Int.le_ceil ((s-widthLo)/widthMesh)
  have ht := Int.ceil_lt_add_one ((s-widthLo)/widthMesh)
  have hp := mul_le_mul_of_nonneg_left hb hm.le
  have hq := mul_lt_mul_of_pos_left ht hm
  have ci0 : (0:ℝ) ≤ (widthCellIndex s:ℝ) := by exact_mod_cast (widthCellIndex_bounds s).1
  have ci1 : (widthCellIndex s:ℝ) ≤ 600000000 := by exact_mod_cast (widthCellIndex_bounds s).2
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
end Sil.Uneven.MainSource
end

/- Original module: Candidate.Uneven.MainCellGeometry. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace Sil.Uneven.MainSource
noncomputable section

def widthCellAtIndex (j : ℤ) : ℝ := widthLo+widthMesh*(j:ℝ)

theorem widthCellAtIndex_bounds {j : ℤ}
    (hj : j ∈ Finset.Icc (0:ℤ) 600000000) :
    widthCellAtIndex j ∈ Set.Icc widthLo widthHi := by
  rcases Finset.mem_Icc.mp hj with ⟨hlo,hhi⟩
  have hlo' : (0:ℝ) ≤ (j:ℝ) := by exact_mod_cast hlo
  have hhi' : (j:ℝ) ≤ 600000000 := by exact_mod_cast hhi
  unfold widthCellAtIndex
  norm_num [widthLo,widthHi,widthMesh] at *
  constructor <;> linarith

theorem widthCellIndex_mem (s : ℝ) :
    widthCellIndex s ∈ Finset.Icc (0:ℤ) 600000000 :=
  Finset.mem_Icc.mpr (widthCellIndex_bounds s)


theorem amplifier_pos (P : Plane) {b : ℝ} (hb : b ∈ Set.Icc widthLo widthHi) : 0 < amp P b :=
  lt_of_lt_of_le (scheduling_guards P hb).2.1 (scheduling_guards P hb).2.2.1


theorem normalized_cell_volume (P : Plane) {n₁ n₂ slots : ℝ}
    (hslots : slots ∈ Set.Icc widthLo widthHi)
    (hcone : n₁+n₂+P.lambda*slots ≤ P.B) :
    n₁+n₂+slots ≤ total P (widthCellUpper slots) := by
  have hs := widthCellUpper_bounds hslots
  have hl : 1 < P.lambda := (parameter_gates P).2.2.2.1
  have hm : 0 ≤ P.lambda-1 := by linarith
  have hp := mul_le_mul_of_nonneg_left
    (show widthCellUpper slots-widthMesh ≤ slots by linarith [hs.2.2]) hm
  unfold total
  nlinarith

end
end Sil.Uneven.MainSource
end
