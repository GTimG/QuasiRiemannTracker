import Candidate.Cycle62.Arithmetic.Constants

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section

/-- Valid numeric scheduling gates; the common positive cutoff is fixed
before the low height degree. The high branch owns its density schedule. -/
structure GeometryAffineLowSchedule where
  μ : ℝ
  δ : ℝ
  τ : ℝ
  e : ℝ
  κ : ℝ
  vslot : ℝ
  μ_pos : 0<μ
  μ_cap : μ≤1/128
  δ_pos : 0<δ
  δ_cap : δ≤μ/128
  τ_pos : 0<τ
  e_pos : 0<e
  e_cap : e<1/1000
  κ_pos : 0<κ
  vslot_nonneg : 0≤vslot
  budget : 8*e+κ≤δ
  cutoff : 2*τ<31*vslot

/-- The exact native24 low exponent, with width one and the common internal rate. -/
def geometryAffineLowTarget (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ) : ℝ :=
  3*g.δ+amp+(g.μ/8+g.μ/64/2-7/30000000+g.μ/8+2*g.δ*31*N+
    (2*Cycle62.Arithmetic.q0/9)*(omega+g.μ/8)+Cycle62.Arithmetic.q0*mesh+g.μ/8)+
    g.δ+4*g.δ+g.δ+g.δ+(g.δ+3*((N:ℝ)+2)*3*g.δ)+g.δ

end
end OAI.SevenEighths.Cycle62InitialMass
