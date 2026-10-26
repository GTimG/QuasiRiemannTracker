/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.SaturatedGain

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.Saturated
open PR63Adaptation

theorem physicalGain_monotone {d : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 3/4) (S : ℝ) :
    Monotone (physicalGain d S) := by
  intro D D' hD
  apply fourGain_lower
  intro i
  exact (fourGain_le (slope d) (offset d) S D i).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hD ((coefficient_bounds hd0 hd).2.1 i)))

end Sil.Uneven.Saturated
