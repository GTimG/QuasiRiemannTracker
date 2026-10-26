import Candidate.Cycle63.Arithmetic.LocalReserves
import Candidate.LocalMoment.UnmarkedDensity

namespace Cycle63.Physical

noncomputable section
open Cycle63.Arithmetic
open OAI.SevenEighths.LocalMoment

/-- The high-bin reserve before the common-part and projector savings. -/
def highMainReserve (b δ : ℝ) : ℝ :=
  1-unmarkedDensity δ-δ*totalA b-amp b*(5-6*unmarkedDensity δ)

theorem high_density_bounds {δ : ℝ} (hd : q0 ≤ δ ∧ δ ≤ 3/4) :
    2/7 ≤ unmarkedDensity δ ∧ unmarkedDensity δ ≤ rho0 ∧
    1/28 ≤ unmarkedDensity δ+δ-1 ∧
    3/7 ≤ 5*unmarkedDensity δ-1 ∧ 1/7 ≤ 4*unmarkedDensity δ-1 ∧
    4*unmarkedDensity δ-1-δ ≤ 4*rho0-1-q0 := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have hq := q0_bounds
  have hlo := unmarkedDensity_ge_two_sevenths hd.2
  have hden : 0 < 3*(5-2*δ) := by linarith [hd.2]
  have hden0 : 0 < 3*(5-2*q0) := by linarith [hq.2]
  have hquot : 10*q0/(3*(5-2*q0)) ≤ 10*δ/(3*(5-2*δ)) := by
    rw [div_le_div_iff₀ hden0 hden]
    nlinarith [hd.1]
  have hhi : unmarkedDensity δ ≤ rho0 := by
    unfold unmarkedDensity rho0 Cycle63.Optimization.density
    linarith
  have hsum : 1/28 ≤ unmarkedDensity δ+δ-1 := by
    have hm := mul_nonneg (show 0 ≤ 3/4-δ by linarith [hd.2])
      (show 0 ≤ 168*δ-20 by linarith [hd.1, hq.1])
    have hq' : 10*δ/(3*(5-2*δ)) ≤ δ-1/28 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    unfold unmarkedDensity
    linarith
  refine ⟨hlo,hhi,hsum,by linarith,by linarith,?_⟩
  linarith [hd.1]

end
end Cycle63.Physical
