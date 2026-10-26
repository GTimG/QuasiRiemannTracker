/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- This rate is chosen after the fixed dictionary and source caps. The
mesh, width padding and old-moment loss can still be fixed before them. -/
def geometryLowDictionaryRate (μ d Bmass Bnorm U : ℝ) (N : ℕ) : ℝ :=
  μ/(2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U+16)

theorem geometry_low_dictionary_rate_budget
    (μ d Bmass Bnorm U : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm) (hU : 0≤U) :
    let δ:=geometryLowDictionaryRate μ d Bmass Bnorm U N
    0<δ ∧ δ≤μ/16 ∧
      2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ := by
  intro δ
  have hp : 0<δ := by dsimp [δ,geometryLowDictionaryRate];positivity
  have he : δ*(2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U+16)=μ :=
    div_mul_cancel₀ _ (by positivity)
  have hc : 0≤2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U := by positivity
  have hprod:=mul_nonneg hp.le hc
  refine ⟨hp,?_,?_⟩ <;> nlinarith

end
end OAI.SevenEighths.Cycle63InitialMass
