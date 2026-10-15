import Candidate.Cycle62.Density.ActualBatchCount
import Mathlib.Analysis.Calculus.BumpFunction.Basic

namespace OAI
noncomputable section
open scoped Classical
open Set
namespace SevenEighths.LocalMoment
open HeckeFamily

private def countingBump : ContDiffBump (3/2 : ℝ) :=
  ⟨1/8, 1/4, by norm_num, by norm_num⟩

def canonicalDensityCountingSetup : DensityCountingSetup where
  modulus := 1
  nonzero := one_ne_zero
  subgroup := ⊤
  units := le_top
  exclusions := ∅
  profile := countingBump
  smooth := countingBump.contDiff (n := ⊤)
  compact := countingBump.hasCompactSupport
  positiveSupport := by
    rw [countingBump.tsupport_eq]
    intro x hx
    have hd : |x-3/2| ≤ (1/4 : ℝ) := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, countingBump] using hx
    have h := (abs_le.mp hd).1
    change 0 < x
    linarith
  nonnegative := fun _ => countingBump.nonneg
  nontrivial := by
    intro h
    have h1 : countingBump (3/2 : ℝ) = 1 := countingBump.one_of_mem_closedBall
      (by simp only [Metric.mem_closedBall, dist_self]; exact countingBump.rIn_pos.le)
    have h0 := congrFun h (3/2 : ℝ)
    simp only [Pi.zero_apply] at h0
    linarith
  lower := 1
  upper := 2
  bound := 1
  lowerPositive := by norm_num
  ordered := by norm_num
  boundPositive := by norm_num
  support := by
    rw [countingBump.support_eq]
    intro x hx
    have hd : |x-3/2| < (1/4 : ℝ) := by
      simpa only [Metric.mem_ball, Real.dist_eq, countingBump] using hx
    have h := abs_lt.mp hd
    constructor <;> linarith
  bounded := fun _ => countingBump.le_one

end SevenEighths.LocalMoment
end
end OAI
