import Candidate.Target836.SourceProvider.NamedSource
import Candidate.Cycle63.Moment.CellGeometry

set_option autoImplicit false
namespace Target874836.SourceProvider
noncomputable section
open OAI OAI.SevenEighths

/-- The accepted finite cell partition is reused with the new affine source
line and the frozen accepted incumbent capacity. -/
theorem normalized_cell_bounds {M n₁ n₂ z : ℝ} (hM : 0<M)
    (hz : (17/500)*M≤z ∧ z≤(1/25)*M)
    (haffine : n₁+n₂+Named.lam*z≤Named.B*M) :
    let j:=Cycle63.Moment.originalCell (z/M)
    1≤j ∧ j≤600 ∧
      max (n₁+n₂+(6*incumbentKappa)*z-M) 0≤M*Named.gap (Cycle63.Arithmetic.cellUpper j) ∧
      n₁+n₂+z≤M*Named.total (Cycle63.Arithmetic.cellUpper j) ∧
      0<M*Named.amp (Cycle63.Arithmetic.cellUpper j) := by
  dsimp only
  have ht : 17/500≤z/M ∧ z/M≤1/25 :=
    ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩
  obtain ⟨hj1,hj600,hl,hu⟩:=Cycle63.Moment.originalCell_mem ht
  have hb:=Cycle63.Arithmetic.cellUpper_bounds hj1 hj600
  have hzup : z≤Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (z/M))*M :=
    (div_le_iff₀ hM).mp hu
  have hzlow : (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (z/M))-1/100000)*M≤z :=
    (le_div_iff₀ hM).mp hl
  have hcoef : 0≤6*incumbentKappa-Named.lam := by norm_num [incumbentKappa,Named.lam]
  have hcoef' : 0≤Named.lam-1 := by norm_num [Named.lam]
  have hdef:=mul_le_mul_of_nonneg_left hzup hcoef
  have htotal:=mul_le_mul_of_nonneg_left hzlow hcoef'
  have hg : 0<Named.gap (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (z/M))) := by
    norm_num [Named.gap,Named.B,Named.lam,Named.kappa,incumbentKappa] at *
    linarith [hb.1]
  have hamp : 0<Named.amp (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (z/M))) := by
    unfold Named.amp Named.K Named.extra
    have hq : 0<Named.q/(6*(Named.kappa-Named.q)) := by norm_num [Named.q,Named.kappa,incumbentKappa]
    have he : 0<Named.lowReserve/(1-Named.q/Named.kappa) := by
      norm_num [Named.lowReserve,Named.q,Named.kappa,incumbentKappa]
    positivity
  refine ⟨hj1,hj600,max_le ?_ (mul_pos hM hg).le,?_,mul_pos hM hamp⟩
  · unfold Named.gap Named.kappa
    nlinarith
  · unfold Named.total Named.mesh
    nlinarith

end
end Target874836.SourceProvider
#print axioms Target874836.SourceProvider.normalized_cell_bounds
