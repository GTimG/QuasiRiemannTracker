/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.AuxiliaryWidthGrid

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.AuxiliarySource

def amplifierMinimum : ℝ := 1/100000

/-- The source scheduler's full guard list, including the four-amplifier gate. -/
theorem scheduling_guards {b : ℝ} (hb : b ∈ Set.Icc widthLo widthHi) :
    0 < gap b ∧ 0 < amplifierMinimum ∧ amplifierMinimum ≤ amp b ∧
    amp b ≤ 1/75 ∧ total b+9*amp b < 1 ∧
    total b+4*amp b < 49/50 ∧ total b+(9/2)*amp b < 49/50 ∧
    0 < supplied b ∧ supplied b ≤ 1/25 ∧
    2*supplied b < frequency b ∧ frequency b < 1 := by
  obtain ⟨hg,ha0,ha1,ht9,ht45,hS0,hS1,hF0,hF1⟩ := source_guards hb
  refine ⟨hg,by norm_num [amplifierMinimum],ha0,ha1.le,ht9,?_,ht45,hS0,hS1.le,hF0,hF1⟩
  linarith

theorem q_range : 31/50 ≤ q ∧ q ≤ 3/4 := by norm_num [q]

end Sil.Uneven.AuxiliarySource
