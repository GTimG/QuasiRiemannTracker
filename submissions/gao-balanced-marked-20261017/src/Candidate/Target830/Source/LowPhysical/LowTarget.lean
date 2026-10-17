import Candidate.Target830.Parameters
import Candidate.Target830.Source.Low.PaidMain
import Candidate.Target830.Source.Schedule
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineScheduleData
set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.LowPhysical
noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.Target830.Source.LowBranch
open OAI.SevenEighths.Cycle63InitialMass

def lowTarget (P : SourcePlane) (g : GeometryAffineLowSchedule) (N : ℕ) (amp omega mesh : ℝ) : ℝ :=
  3*g.δ+amp+(g.μ/8+g.μ/64/2-lowReserve+g.μ/8+2*g.δ*31*N+
    (P.q/(6*incumbentKappa))*(omega+g.μ/8)+P.q*mesh+g.μ/8)+
    g.δ+4*g.δ+g.δ+g.δ+(g.δ+3*((N:ℝ)+2)*3*g.δ)+g.δ

theorem low_target_lower (P : SourcePlane) (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ) (ha : 0 ≤ amp) (ho : 0 ≤ omega) (hm : 0 ≤ mesh) :
    -1 ≤ lowTarget (P := P) g N amp omega mesh := by
  have hq : 0 ≤ P.q := by cases P <;> norm_num [SourcePlane.q]
  have hp : 0 ≤ P.q/(6*incumbentKappa)*(omega+g.μ/8) := by
    have hk : 0 < incumbentKappa := by norm_num [incumbentKappa,kappa0]
    have hg := g.μ_pos.le
    positivity
  have hqm := mul_nonneg hq hm
  have hN : 0 ≤ 2*g.δ*31*(N:ℝ) := by have hd := g.δ_pos.le; positivity
  have hother : 0 ≤ 3*((N:ℝ)+2)*3*g.δ := by have hd := g.δ_pos.le; positivity
  unfold lowTarget
  norm_num [lowReserve]
  linarith [g.μ_pos,g.δ_pos]

theorem low_target_le_accepted (P : SourcePlane) (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ) (ho : 0 ≤ omega) (hm : 0 ≤ mesh) :
    lowTarget (P := P) g N amp omega mesh ≤ geometryAffineLowTarget g N amp omega mesh := by
  have hfee : P.q/(6*incumbentKappa) ≤ 2*Cycle63.Arithmetic.q0/9 := by
    cases P <;> norm_num [SourcePlane.q,incumbentKappa,kappa0,Cycle63.Arithmetic.q0]
  have hq : P.q ≤ Cycle63.Arithmetic.q0 := by cases P <;> norm_num [SourcePlane.q,Cycle63.Arithmetic.q0]
  have hr : (7/30000000 : ℝ) ≤ lowReserve := by norm_num [lowReserve]
  have hω := mul_le_mul_of_nonneg_right hfee (show 0 ≤ omega+g.μ/8 by linarith [g.μ_pos])
  have hmm := mul_le_mul_of_nonneg_right hq hm
  unfold lowTarget geometryAffineLowTarget
  linarith
end
end OAI.SevenEighths.Target830.Source.LowPhysical
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.low_target_le_accepted

#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.low_target_lower
