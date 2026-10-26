/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainParameters
import Candidate.Uneven.FineSchedule

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.MainHigh
open SaturatedPlain

/-- The marked count fee is paid explicitly before the source is assembled. -/
def mainHighReserve : ℝ := Sil.Uneven.MainSource.highReserve-fineHighRawFee


theorem main_high_reserve_paid :
    mainHighReserve+fineHighRawFee=Sil.Uneven.MainSource.highReserve := by
  unfold mainHighReserve
  ring

end OAI.SevenEighths.MainHigh
