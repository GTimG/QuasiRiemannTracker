/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.MainLowTarget
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule

set_option autoImplicit false
namespace OAI.SevenEighths.MainPhysical
noncomputable section
open Cycle63InitialMass
open Sil.Uneven.MainSource

/-- The actual finite-dictionary schedule pays both new source branches.
The requested source error has already been capped before this step. -/
theorem final_branch_exponents_of_schedule (P : Plane) (g : GeometryAffineLowSchedule)
    (εaffine : ℝ) (hεcap : εaffine ≤ 1/10000000000000000000000000000)
    (hμ : g.μ=geometryLossUnit 1 εaffine) (n N : ℕ) (hn : n≤N)
    (B L amp omega mesh : ℝ)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)
    (hω : omega≤33*g.μ/128) (hmesh : mesh≤g.μ/8) :
    lowTarget P g n amp omega mesh+3*g.δ-amp≤-(1/2000000000:ℝ) ∧
      (amp+(-MainHigh.mainHighReserve+4*g.μ-3*g.δ))+3*g.δ-amp≤
        -(1/2000000000:ℝ) := by
  have hc := min_le_right (geometryCommonDictionaryRate g.μ 31 3 4 3 B L N)
    (g.μ/(64*(31+1)*((N:ℝ)+1)))
  change geometryFinalDictionaryRate g.μ 31 3 4 3 B L N ≤ _ at hc
  rw [←hδ] at hc
  have hp := (le_div_iff₀ (show (0:ℝ)<64*(31+1)*((N:ℝ)+1) by positivity)).mp hc
  have hbudget : g.δ*((N:ℝ)+1)≤g.μ/2048 := by nlinarith only [hp]
  have hcap : g.μ≤εaffine/128 := by
    rw [hμ]
    exact min_le_left _ _
  exact final_branch_exponents P g n N hn amp omega mesh hbudget hω hmesh
    (by linarith only [hcap,hεcap])

end
end OAI.SevenEighths.MainPhysical
