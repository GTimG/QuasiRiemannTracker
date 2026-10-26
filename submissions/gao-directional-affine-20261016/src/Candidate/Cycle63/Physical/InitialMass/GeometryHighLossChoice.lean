/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- Choose shell losses after fixing the source and projector norm caps. -/
def geometryHighShellRate (μ B L : ℝ) : ℝ := μ/(B+3*L+16)

theorem geometry_high_shell_rate_budget (μ B L : ℝ)
    (hμ : 0<μ) (hB : 0≤B) (hL : 0≤L) :
    let δ:=geometryHighShellRate μ B L
    0<δ ∧ δ≤μ/16 ∧ B*δ+3*L*δ+δ+8*δ≤μ := by
  intro δ
  have hp : 0<δ := by dsimp [δ,geometryHighShellRate];positivity
  have he : δ*(B+3*L+16)=μ := div_mul_cancel₀ _ (by positivity)
  have hn:=mul_nonneg hp.le (show 0≤B+3*L by positivity)
  refine ⟨hp,?_,?_⟩ <;> nlinarith

/-- This includes the first and second projector shell costs. The caller
still pays every remaining finite partition from the displayed fee budget. -/
theorem geometry_high_width_one_loss_budget
    (μ B L omega rawError allowance fees : ℝ)
    (hμ : 0<μ) (hB : 0≤B) (hL : 0≤L)
    (hω : omega≤33*μ/128) (hraw : rawError≤μ/4)
    (ha : allowance≤μ/4) (hf : fees≤8*geometryHighShellRate μ B L) :
    let δ:=geometryHighShellRate μ B L
    omega+μ/8+μ/8+4*(μ/32)+μ/8+rawError+allowance+
      B*(μ/(8*(B+1)))+μ/8+B*δ+3*L*δ+δ+fees≤4*μ := by
  intro δ
  have hb:=(geometry_high_shell_rate_budget μ B L hμ hB hL).2.2
  change B*δ+3*L*δ+δ+8*δ≤μ at hb
  have hm : 0<μ/(8*(B+1)) := by positivity
  have he : μ/(8*(B+1))*(8*(B+1))=μ := div_mul_cancel₀ _ (by positivity)
  have hmass : B*(μ/(8*(B+1)))≤μ/8 := by nlinarith
  change fees≤8*δ at hf
  linarith

/-- The density degree is fixed before this height parameter is chosen. -/
theorem geometry_high_density_height_choice (μ : ℝ) (J : ℕ) (hμ : 0<μ) :
    let τ:=μ/(16*((J:ℝ)+1))
    0<τ ∧ τ≤μ/16 ∧ 2*τ*((J:ℝ)+1)≤μ/8 := by
  intro τ
  have hp : 0<τ := by dsimp [τ];positivity
  have he : τ*(16*((J:ℝ)+1))=μ := div_mul_cancel₀ _ (by positivity)
  have hn:=mul_nonneg hp.le (Nat.cast_nonneg J : (0:ℝ)≤J)
  refine ⟨hp,?_,?_⟩ <;> nlinarith

theorem geometry_high_width_one_exponent_saving (εaffine loss : ℝ)
    (hε : 0<εaffine) (hloss : loss≤4*geometryLossUnit 1 εaffine) :
    -(720486667/30493190000000:ℝ)+loss≤-(7/60000000:ℝ) := by
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hh:=geometry_paid_loss 1 εaffine 1 (720486667/30493190000000) loss
    (by norm_num) le_rfl geometry_high_reserve_ge_low (by linarith)
  simpa only [one_mul,neg_one_mul] using hh

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_high_shell_rate_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_high_width_one_loss_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_high_density_height_choice
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_high_width_one_exponent_saving
