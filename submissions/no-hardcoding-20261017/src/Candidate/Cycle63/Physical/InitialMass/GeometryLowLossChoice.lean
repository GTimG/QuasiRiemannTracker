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

/-- The literal width-one low exponent, including both projector-shell
losses and eight additional unit-rate payments, fits inside two loss units.
These eight fees leave room for the box count, first selection, supported
label payment, both shell counts and subsequent fixed finite partitions.
Each consumer must still show that its own fees fit this displayed ledger. -/
theorem geometry_low_width_one_loss_budget
    (μ d Bmass Bnorm U omega mesh : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm) (hU : 0≤U)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8) :
    let δ:=geometryLowDictionaryRate μ d Bmass Bnorm U N
    μ/8+μ/128+μ/8+2*δ*d*N+
      (2*Cycle63.Arithmetic.q0/9)*(omega+μ/8)+Cycle63.Arithmetic.q0*mesh+
      μ/8+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤2*μ := by
  intro δ
  have hb:=(geometry_low_dictionary_rate_budget μ d Bmass Bnorm U N hμ hd hm hn hU).2.2
  change 2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ at hb
  have hq := Cycle63.Arithmetic.q0_bounds
  have h1 := mul_le_mul_of_nonneg_left hω (by linarith : (0:ℝ) ≤ 2*Cycle63.Arithmetic.q0/9)
  have h2 := mul_le_mul_of_nonneg_left hmesh (by linarith : (0:ℝ) ≤ Cycle63.Arithmetic.q0)
  have h3 := mul_le_mul_of_nonneg_right hq.2 hμ.le
  linarith

/-- Any bound supplied by this ledger retains the strict low-branch
saving. This is scalar payment only, not a column-energy hypothesis. -/
theorem geometry_low_width_one_exponent_saving (εaffine loss : ℝ)
    (hε : 0<εaffine) (hloss : loss≤2*geometryLossUnit 1 εaffine) :
    -(Cycle63.Arithmetic.lowReserve:ℝ)+loss≤-((Cycle63.Arithmetic.lowReserve/2):ℝ) := by
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hh:=geometry_paid_loss 1 εaffine 1 (Cycle63.Arithmetic.lowReserve) loss
    (by norm_num) le_rfl le_rfl (by linarith)
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_low_dictionary_rate_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_low_width_one_loss_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_low_width_one_exponent_saving
