/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryGuards
import Candidate.Cycle63.Physical.TerminalLedger
set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryReconstruction
noncomputable section

theorem second_zero_reserve {b : ℝ} (hb : Sil.Uneven.AuxiliarySource.widthLo≤b ∧ b≤7/250) :
    (3/50:ℝ)≤1-Sil.Uneven.AuxiliarySource.total b-5*Sil.Uneven.AuxiliarySource.amp b := by
  rcases hb with ⟨hlo,hhi⟩
  norm_num [Sil.Uneven.AuxiliarySource.total,Sil.Uneven.AuxiliarySource.amp,Sil.Uneven.AuxiliarySource.gap,Sil.Uneven.AuxiliarySource.B,
    Sil.Uneven.AuxiliarySource.lambda,Sil.Uneven.AuxiliarySource.q,Sil.Uneven.AuxiliarySource.kappa,Sil.Uneven.AuxiliarySource.lowReserve,
    Sil.Uneven.AuxiliarySource.widthMesh,Sil.Uneven.AuxiliarySource.widthLo] at *
  linarith only [hlo,hhi]

theorem auxiliary_amplifier_upper {b : ℝ}
    (hb : Sil.Uneven.AuxiliarySource.widthLo ≤ b ∧ b ≤ Sil.Uneven.AuxiliarySource.widthHi) :
    Sil.Uneven.AuxiliarySource.amp b ≤ (7/1000:ℝ) := by
  rcases hb with ⟨hlo,hhi⟩
  norm_num [Sil.Uneven.AuxiliarySource.amp,Sil.Uneven.AuxiliarySource.gap,Sil.Uneven.AuxiliarySource.B,Sil.Uneven.AuxiliarySource.lambda,
    Sil.Uneven.AuxiliarySource.q,Sil.Uneven.AuxiliarySource.kappa,Sil.Uneven.AuxiliarySource.lowReserve,Sil.Uneven.AuxiliarySource.widthLo,Sil.Uneven.AuxiliarySource.widthHi] at *
  linarith only [hlo,hhi]

theorem second_zero_excess_bound {b M A a c d Bc : ℝ}
    (hb : Sil.Uneven.AuxiliarySource.widthLo≤b ∧ b≤7/250) (hM : 0≤M)
    (hA : A≤M*Sil.Uneven.AuxiliarySource.total b) (ha : a≤M*Sil.Uneven.AuxiliarySource.amp b)
    (hc : 0≤c) (hd : 0≤d) (hBc : 0≤Bc) :
    A-M-min c d-Bc+5*a≤-M*(3/50) := by
  have hreserve := mul_le_mul_of_nonneg_left (second_zero_reserve  hb) hM
  have hmin : 0 ≤ min c d := le_min hc hd
  nlinarith
end
end OAI.SevenEighths.AuxiliaryReconstruction
