/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryGuards
import Candidate.Uneven.FineSchedule

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.AuxiliaryHigh
open SaturatedPlain

/-- The marked count fee is paid explicitly before the source is assembled. -/
def auxiliaryHighReserve : ℝ := Sil.Uneven.AuxiliarySource.highReserve-fineHighRawFee


theorem auxiliary_high_reserve_paid :
    auxiliaryHighReserve+fineHighRawFee=Sil.Uneven.AuxiliarySource.highReserve := by
  unfold auxiliaryHighReserve
  ring

end OAI.SevenEighths.AuxiliaryHigh
