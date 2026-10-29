/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open Set Metric

/-- A compact family of strict scalar gates permits one common perturbation
radius. The perturbation may contain several real source coordinates. -/
theorem compact_positive_perturbation {α E : Type*}
    [PseudoMetricSpace α] [CompactSpace α] [Nonempty α]
    [PseudoMetricSpace E] [ProperSpace E]
    (v0 : E) (F : α × E → ℝ) (hF : Continuous F)
    (hpos : ∀ x, 0 < F (x,v0)) :
    ∃ δ > 0, ∀ x v, dist v v0 ≤ δ → 0 < F (x,v) := by
  have hg : Continuous (fun x => F (x,v0)) := hF.comp (continuous_id.prodMk continuous_const)
  obtain ⟨x0,_,hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hg.continuousOn
  have hm : 0 < F (x0,v0)/2 := div_pos (hpos x0) (by norm_num)
  obtain ⟨d,hd,hmod⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_univ.prod (isCompact_closedBall v0 1)).uniformContinuousOn_of_continuous hF.continuousOn)
    (F (x0,v0)/2) hm
  let δ := min (d/2) (1/2:ℝ)
  refine ⟨δ,lt_min (by positivity) (by norm_num),?_⟩
  intro x v hv
  have hδd : δ ≤ d/2 := min_le_left _ _
  have hδ1 : δ ≤ (1/2:ℝ) := min_le_right _ _
  have hvI : v ∈ closedBall v0 1 := by rw [mem_closedBall]; linarith
  have hzero : v0 ∈ closedBall v0 1 := by simp
  have hdist : dist (x,v) (x,v0) < d := by
    simp only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg]
    linarith
  have hh := hmod (x,v) ⟨mem_univ _,hvI⟩ (x,v0) ⟨mem_univ _,hzero⟩ hdist
  rw [Real.dist_eq] at hh
  have hlo := (abs_lt.mp hh).1
  have hbase := hmin (mem_univ x)
  change F (x0,v0) ≤ F (x,v0) at hbase
  linarith [hpos x0]

end
end Qrh.JointDetector.RepeatedMarks
#print axioms Qrh.JointDetector.RepeatedMarks.compact_positive_perturbation
