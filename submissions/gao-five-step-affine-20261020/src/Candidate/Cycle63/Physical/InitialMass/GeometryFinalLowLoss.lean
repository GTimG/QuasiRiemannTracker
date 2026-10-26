/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalLossParameters
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

variable [Cycle63.AffineLedger] in
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
      Cycle63.AffineLedger.lowRate*(omega+μ/8)+Cycle63.AffineLedger.q*mesh+
      μ/8+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+fees≤2*μ := by
  intro δ
  have rates:=geometry_final_dictionary_budgets μ d Bmass Bnorm U B Lproj N
    hμ hd hm hn hU hB hL
  have hb:=rates.2.2.2.2.1
  change 2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ at hb
  change fees≤8*δ at hfees
  have hq := Cycle63.AffineLedger.q_le_one
  have h1 := mul_le_mul_of_nonneg_left hω Cycle63.AffineLedger.lowRate_mem.1.le
  have h2 := mul_le_mul_of_nonneg_left hmesh Cycle63.AffineLedger.q_pos.le
  have h3 := mul_le_mul_of_nonneg_right hq hμ.le
  have h4 := mul_le_mul_of_nonneg_right Cycle63.AffineLedger.lowRate_le_sixth hμ.le
  linarith

variable [Cycle63.AffineLedger] in
/-- Width one and the actual common rate: the five low-consumer unit fees
leave three more unit fees for physical selection, ratio bins and prime
averaging. The amplifier exponent cancels exactly once. -/
theorem geometry_final_main_low_consumer_ledger
    (μ d Bmass Bnorm U B Lproj omega mesh amp : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤Lproj)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8) :
    let δ:=geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    let error:=μ/8+μ/128-(Cycle63.AffineLedger.lowReserve:ℝ)+μ/8+2*δ*d*N+
      Cycle63.AffineLedger.lowRate*(omega+μ/8)+Cycle63.AffineLedger.q*mesh+μ/8
    let target:=Bmass*δ+amp+error+δ+Bnorm*δ+δ+δ+
      (δ+3*(((N:ℝ)+2)*U)*δ)+δ
    target+δ+δ+δ-amp≤-(Cycle63.AffineLedger.lowReserve:ℝ)+2*μ := by
  intro δ error target
  have hb:=geometry_final_low_loss_budget μ d Bmass Bnorm U B Lproj omega mesh
    (8*δ) N hμ hd hm hn hU hB hL hω hmesh le_rfl
  dsimp only [target,error]
  change μ/8+μ/128+μ/8+2*δ*d*N+
    Cycle63.AffineLedger.lowRate*(omega+μ/8)+Cycle63.AffineLedger.q*mesh+
    μ/8+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤2*μ at hb
  linarith only [hb]

end
end OAI.SevenEighths.Cycle63InitialMass
