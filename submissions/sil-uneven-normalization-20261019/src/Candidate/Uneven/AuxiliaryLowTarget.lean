/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryLowPaidMain
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineScheduleData

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryPhysical
noncomputable section
open AuxiliaryLow Cycle63InitialMass

def lowTarget (g : GeometryAffineLowSchedule) (N : ℕ) (amp omega mesh : ℝ) : ℝ :=
  3*g.δ+amp+(g.μ/8+g.μ/64/2-Sil.Uneven.AuxiliarySource.lowReserve+g.μ/8+2*g.δ*31*N+
    (Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*(omega+g.μ/8)+
      Sil.Uneven.AuxiliarySource.q*mesh+g.μ/8)+
    g.δ+4*g.δ+g.δ+g.δ+(g.δ+3*((N:ℝ)+2)*3*g.δ)+g.δ

theorem low_target_lower (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ) (ha : 0 ≤ amp) (ho : 0 ≤ omega) (hm : 0 ≤ mesh) :
    -1 ≤ lowTarget g N amp omega mesh := by
  have hq : 0 ≤ Sil.Uneven.AuxiliarySource.q := by norm_num [Sil.Uneven.AuxiliarySource.q]
  have hp : 0 ≤ Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa)*(omega+g.μ/8) := by
    have hk : 0 < incumbentKappa := by norm_num [incumbentKappa,Sil.Uneven.AuxiliarySource.kappa]
    have hg := g.μ_pos.le
    positivity
  have hqm := mul_nonneg hq hm
  have hN : 0 ≤ 2*g.δ*31*(N:ℝ) := by have hd := g.δ_pos.le; positivity
  have hother : 0 ≤ 3*((N:ℝ)+2)*3*g.δ := by have hd := g.δ_pos.le; positivity
  unfold lowTarget
  norm_num [Sil.Uneven.AuxiliarySource.lowReserve]
  linarith [g.μ_pos,g.δ_pos]

/-- The larger auxiliary LOW price is absorbed by the reserve only after
the internal allowances have been made sufficiently small. -/
theorem low_target_le_accepted (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ)
    (hmu : g.μ ≤ 1/100000000) (homega : omega ≤ 1/100000000)
    (hmesh : mesh ≤ 1/100000000) :
    lowTarget g N amp omega mesh ≤ geometryAffineLowTarget g N amp omega mesh := by
  unfold lowTarget geometryAffineLowTarget
  norm_num [incumbentKappa, Sil.Uneven.AuxiliarySource.kappa,
    Sil.Uneven.AuxiliarySource.q, Sil.Uneven.AuxiliarySource.lowReserve,
    Cycle63.Arithmetic.q0]
  linarith only [hmu,homega,hmesh]

end
end OAI.SevenEighths.AuxiliaryPhysical
