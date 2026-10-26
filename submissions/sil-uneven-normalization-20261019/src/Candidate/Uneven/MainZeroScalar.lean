/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCellGeometry
import Candidate.Cycle63.Physical.TerminalLedger
set_option autoImplicit false
namespace OAI.SevenEighths.MainReconstruction
noncomputable section
open Sil.Uneven.MainSource
variable {plane : Plane}

theorem second_zero_reserve {b : ℝ} (hb : widthLo≤b ∧ b≤1/25) :
    (227876729/3446640000:ℝ)≤1-Sil.Uneven.MainSource.total plane b-5*Sil.Uneven.MainSource.amp plane b := by
  rcases hb with ⟨hlo,hhi⟩
  cases plane <;>
    norm_num [Sil.Uneven.MainSource.total,Sil.Uneven.MainSource.amp,Sil.Uneven.MainSource.gap,Plane.B,
      Plane.lambda,Plane.q,Plane.incumbent,lowReserve,widthMesh,widthLo] at *
  all_goals linarith

theorem second_zero_excess_bound {b M A a c d Bc : ℝ}
    (hb : widthLo≤b ∧ b≤1/25) (hM : 0≤M)
    (hA : A≤M*Sil.Uneven.MainSource.total plane b) (ha : a≤M*Sil.Uneven.MainSource.amp plane b)
    (hc : 0≤c) (hd : 0≤d) (hBc : 0≤Bc) :
    A-M-min c d-Bc+5*a≤-M*(227876729/3446640000) := by
  have hreserve := mul_le_mul_of_nonneg_left (second_zero_reserve (plane:=plane) hb) hM
  have hmin : 0 ≤ min c d := le_min hc hd
  nlinarith
end
end OAI.SevenEighths.MainReconstruction
