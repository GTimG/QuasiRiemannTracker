import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
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

/-- The density degree is fixed before this height parameter is chosen. -/
theorem geometry_high_density_height_choice (μ : ℝ) (J : ℕ) (hμ : 0<μ) :
    let τ:=μ/(16*((J:ℝ)+1))
    0<τ ∧ τ≤μ/16 ∧ 2*τ*((J:ℝ)+1)≤μ/8 := by
  intro τ
  have hp : 0<τ := by dsimp [τ];positivity
  have he : τ*(16*((J:ℝ)+1))=μ := div_mul_cancel₀ _ (by positivity)
  have hn:=mul_nonneg hp.le (Nat.cast_nonneg J : (0:ℝ)≤J)
  refine ⟨hp,?_,?_⟩ <;> nlinarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
