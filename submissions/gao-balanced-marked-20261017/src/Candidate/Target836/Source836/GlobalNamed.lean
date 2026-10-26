import Candidate.Target836.SourceProvider.NamedBounds
import Candidate.Target836.SourceProvider.CellGeometry
import Candidate.Target836.Target836Geometry
import Candidate.Cycle63.Arithmetic.LocalReserves

set_option autoImplicit false
namespace OAI.SevenEighths.Target836SourceAssembly.GlobalNamed
noncomputable section
open Target874836.SourceProvider
abbrev lambda : ℝ := Named.lam
abbrev B : ℝ := Named.B
abbrev amp := Named.amp
abbrev totalA := Named.total
abbrev cellUpper := Cycle63.Arithmetic.cellUpper
abbrev cellUpper_bounds := @Cycle63.Arithmetic.cellUpper_bounds
abbrev amp_bounds := @Named.amp_bounds
abbrev amp_pos := @Named.amp_pos
abbrev main_fixed_reserve := @Named.main_fixed_reserve
abbrev error_fixed_reserve := @Named.error_fixed_reserve

theorem second_zero_reserve {b : ℝ} (hb : 3401/100000≤b ∧ b≤1/25) :
    227876729/3446640000 ≤ 1-totalA b-5*amp b := by
  norm_num [totalA,amp,Named.total,Named.amp,Named.K,Named.extra,Named.lowReserve,
    Named.q,Named.kappa,incumbentKappa,Named.gap,Named.B,Named.lam,Named.mesh] at *
  linarith [hb.1,hb.2]
end
end OAI.SevenEighths.Target836SourceAssembly.GlobalNamed
#print axioms OAI.SevenEighths.Target836SourceAssembly.GlobalNamed.second_zero_reserve
