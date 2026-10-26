import Candidate.Target830.Source.Schedule
import Candidate.Cycle63.Physical.TerminalLedger
set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Reconstruction
noncomputable section
variable {plane : SourcePlane}

theorem second_zero_reserve {b : ℝ} (hb : widthLower≤b ∧ b≤1/25) :
    (227876729/3446640000:ℝ)≤1-plane.total b-5*plane.amp b := by
  rcases hb with ⟨hlo,hhi⟩
  cases plane <;>
    norm_num [SourcePlane.total,SourcePlane.amp,SourcePlane.gap,SourcePlane.B,
      SourcePlane.lambda,SourcePlane.q,kappa0,lowReserve,sourceWidthMesh,widthLower] at *
  all_goals linarith

theorem second_zero_excess_bound {b M A a c d Bc : ℝ}
    (hb : widthLower≤b ∧ b≤1/25) (hM : 0≤M)
    (hA : A≤M*plane.total b) (ha : a≤M*plane.amp b)
    (hc : 0≤c) (hd : 0≤d) (hBc : 0≤Bc) :
    A-M-min c d-Bc+5*a≤-M*(227876729/3446640000) := by
  have hreserve := mul_le_mul_of_nonneg_left (second_zero_reserve (plane:=plane) hb) hM
  have hmin : 0≤min c d := le_min hc hd
  nlinarith
end
end OAI.SevenEighths.Target830.Source.Reconstruction
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.second_zero_reserve
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.second_zero_excess_bound
