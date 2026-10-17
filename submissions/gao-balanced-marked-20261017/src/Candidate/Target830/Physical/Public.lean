import Candidate.Target830.Physical.Active
import Candidate.Target830.Physical.ActualBin
import Candidate.Target830.Physical.Selection

noncomputable section
set_option autoImplicit false

namespace OAI.SevenEighths.Target830.Physical

/-- The original positive physical slot dictionary is fine enough after every
allowed row-scale rescaling. No total-width or cardinality loss is added. -/
theorem rescaled_slot_mesh {n : ℕ} (lengths : Fin n → ℝ) (mesh d : ℝ)
    (hd : (1 / 200 : ℝ) ≤ d) (hmesh : 0 ≤ mesh)
    (hfine : ∀ j, lengths j ≤ mesh / 200) :
    ∀ j, lengths j / d ≤ mesh := by
  have hp : 0 < d := by linarith
  intro j
  apply (div_le_iff₀ hp).mpr
  have hm := mul_le_mul_of_nonneg_left hd hmesh
  linarith [hfine j]

theorem source_slot_power (Z d width : ℝ) (hZ : 0 < Z) (hd : d ≠ 0) :
    (Z ^ d) ^ (width / d) = Z ^ width := by
  rw [← Real.rpow_mul hZ.le, mul_div_cancel₀ width hd]

end OAI.SevenEighths.Target830.Physical

#print axioms OAI.SevenEighths.Target830.Physical.affine_active_box_fourth
#print axioms OAI.SevenEighths.Target830.Physical.Packet.actual_label_packet_bin_bound
#print axioms OAI.SevenEighths.Target830.Physical.scheduled_whole_slots
#print axioms OAI.SevenEighths.Target830.Physical.rescaled_slot_mesh
