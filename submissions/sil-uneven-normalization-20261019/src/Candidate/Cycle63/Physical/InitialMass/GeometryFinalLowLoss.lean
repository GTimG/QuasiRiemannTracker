/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalLossParameters

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The shared final dictionary rate pays the literal low consumer and its
remaining finite fees. The mesh and old-moment rate precede the dictionary. -/
theorem geometry_final_low_loss_budget
    (μ d Bmass Bnorm U B Lproj omega mesh fees : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤Lproj)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8)
    (hfees : fees≤8*geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N) :
    let δ:=geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    μ/8+μ/128+μ/8+2*δ*d*N+
      (2*Cycle63.Arithmetic.q0/9)*(omega+μ/8)+Cycle63.Arithmetic.q0*mesh+
      μ/8+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+fees≤2*μ := by
  intro δ
  have rates:=geometry_final_dictionary_budgets μ d Bmass Bnorm U B Lproj N
    hμ hd hm hn hU hB hL
  have hb:=rates.2.2.2.2.1
  change 2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ at hb
  change fees≤8*δ at hfees
  norm_num only [Cycle63.Arithmetic.q0]
  linarith

/-- Width one and the actual common rate: the five low-consumer unit fees
leave three more unit fees for physical selection, ratio bins and prime
averaging. The amplifier exponent cancels exactly once. -/
theorem geometry_final_main_low_consumer_ledger
    (μ d Bmass Bnorm U B Lproj omega mesh amp : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤Lproj)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8) :
    let δ:=geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    let error:=μ/8+μ/128-(7/30000000:ℝ)+μ/8+2*δ*d*N+
      (2*Cycle63.Arithmetic.q0/9)*(omega+μ/8)+Cycle63.Arithmetic.q0*mesh+μ/8
    let target:=Bmass*δ+amp+error+δ+Bnorm*δ+δ+δ+
      (δ+3*(((N:ℝ)+2)*U)*δ)+δ
    target+δ+δ+δ-amp≤-(7/30000000:ℝ)+2*μ := by
  intro δ error target
  have hb:=geometry_final_low_loss_budget μ d Bmass Bnorm U B Lproj omega mesh
    (8*δ) N hμ hd hm hn hU hB hL hω hmesh le_rfl
  dsimp only [target,error]
  change μ/8+μ/128+μ/8+2*δ*d*N+
    (2*Cycle63.Arithmetic.q0/9)*(omega+μ/8)+Cycle63.Arithmetic.q0*mesh+
    μ/8+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤2*μ at hb
  linarith only [hb]

/-- After the literal low exponent has been paid, the fixed strict saving
is uniform in the slot cardinality. -/
theorem geometry_final_main_low_exponent_saving (εaffine : ℝ) (hε : 0<εaffine) :
    -(7/30000000:ℝ)+2*geometryLossUnit 1 εaffine≤-(7/60000000:ℝ) :=
  geometry_low_width_one_exponent_saving εaffine (2*geometryLossUnit 1 εaffine) hε le_rfl

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_low_loss_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_main_low_consumer_ledger
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_main_low_exponent_saving
