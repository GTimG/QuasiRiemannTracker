import Candidate.Target836.SourceProvider.NamedSource
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineScheduleData
set_option autoImplicit false
namespace Target874836.SourceProvider.Physical
noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.Cycle63InitialMass

def lowTarget (g : GeometryAffineLowSchedule) (N : ℕ) (amp omega mesh : ℝ) : ℝ :=
  3*g.δ+amp+(g.μ/8+g.μ/64/2-Named.lowReserve+g.μ/8+2*g.δ*31*N+
    (Named.q/(6*incumbentKappa))*(omega+g.μ/8)+Named.q*mesh+g.μ/8)+
    g.δ+4*g.δ+g.δ+g.δ+(g.δ+3*((N:ℝ)+2)*3*g.δ)+g.δ

theorem low_target_lower (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ) (ha : 0 ≤ amp) (ho : 0 ≤ omega) (hm : 0 ≤ mesh) :
    -1 ≤ lowTarget g N amp omega mesh := by
  have hq : 0 ≤ Named.q := by norm_num [Named.q]
  have hp : 0 ≤ Named.q/(6*incumbentKappa)*(omega+g.μ/8) := by
    have hk : 0 < incumbentKappa := by norm_num [incumbentKappa]
    have hg := g.μ_pos.le
    positivity
  have hqm := mul_nonneg hq hm
  have hN : 0 ≤ 2*g.δ*31*(N:ℝ) := by have hd := g.δ_pos.le; positivity
  have hother : 0 ≤ 3*((N:ℝ)+2)*3*g.δ := by have hd := g.δ_pos.le; positivity
  unfold lowTarget
  norm_num [Named.lowReserve]
  linarith [g.μ_pos,g.δ_pos]

theorem low_target_le_accepted (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ) (ho : 0 ≤ omega) (hm : 0 ≤ mesh) :
    lowTarget g N amp omega mesh ≤ geometryAffineLowTarget g N amp omega mesh := by
  have hfee : Named.q/(6*incumbentKappa) ≤ 2*Cycle63.Arithmetic.q0/9 := by
    norm_num [Named.q,incumbentKappa,Cycle63.Arithmetic.q0]
  have hq : Named.q ≤ Cycle63.Arithmetic.q0 := by norm_num [Named.q,Cycle63.Arithmetic.q0]
  have hr : (7/30000000 : ℝ) ≤ Named.lowReserve := by norm_num [Named.lowReserve]
  have hω := mul_le_mul_of_nonneg_right hfee (show 0 ≤ omega+g.μ/8 by linarith [g.μ_pos])
  have hmm := mul_le_mul_of_nonneg_right hq hm
  unfold lowTarget geometryAffineLowTarget
  linarith
end
end Target874836.SourceProvider.Physical
#print axioms Target874836.SourceProvider.Physical.low_target_le_accepted

#print axioms Target874836.SourceProvider.Physical.low_target_lower
