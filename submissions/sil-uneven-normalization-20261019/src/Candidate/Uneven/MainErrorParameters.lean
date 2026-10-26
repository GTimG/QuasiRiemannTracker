/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCellGeometry

set_option autoImplicit false
namespace OAI.SevenEighths.MainErrorReconstruction
noncomputable section
open Sil.Uneven.MainSource

theorem amplifier_bounds (P : Plane) {b : ℝ}
    (hb : b ∈ Set.Icc widthLo widthHi) :
    Sil.Uneven.MainSource.amplifierMinimum≤Sil.Uneven.MainSource.amp P b ∧ Sil.Uneven.MainSource.amp P b≤1/75 := by
  have hh := Sil.Uneven.MainSource.scheduling_guards P hb
  exact ⟨hh.2.2.1,hh.2.2.2.1.le⟩

end
end OAI.SevenEighths.MainErrorReconstruction
