/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalLossParameters

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The full high exponent retains the twice-fiber loss. Both projector
shell powers and the remaining partitions are charged separately. -/
theorem geometry_final_high_loss_budget
    (μ d Bmass Bnorm U B Lproj omega rawError allowance fees : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤Lproj)
    (hω : omega≤33*μ/128) (hraw : rawError≤μ/4)
    (ha : allowance≤μ/4)
    (hf : fees≤8*geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N) :
    let δ := geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    let massRate := geometryFinalMassRate μ δ B
    omega+μ/8+μ/8+4*(μ/32)+μ/8+rawError+allowance+
      B*massRate+μ/8+B*δ+3*Lproj*δ+δ+fees+2*(μ/8)≤4*μ := by
  intro δ massRate
  have rates := geometry_final_dictionary_budgets μ d Bmass Bnorm U B Lproj N
    hμ hd hm hn hU hB hL
  have hdict := rates.2.2.2.2.2.1
  have hmass := geometry_final_mass_dictionary_budget μ δ B hμ rates.1 hB
  change B*δ+3*Lproj*δ+δ+8*δ≤μ at hdict
  change fees≤8*δ at hf
  have hmass' : B*massRate≤μ/8 := hmass.2.2
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass
