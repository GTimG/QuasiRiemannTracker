/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateBounds
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open Set

def rateDomain (floor : ℝ) : Set (ℝ × ℝ) :=
  {x | floor ≤ x.1 ∧ x.1 ≤ 3/4 ∧ 0 ≤ x.2 ∧ x.2 ≤ x.1}

theorem rateDomain_compact (floor : ℝ) : IsCompact (rateDomain floor) := by
  have hclosed : IsClosed {x : ℝ × ℝ | x.2 ≤ x.1} :=
    isClosed_le continuous_snd continuous_fst
  have heq : rateDomain floor = (Icc floor (3/4:ℝ) ×ˢ Icc (0:ℝ) (3/4)) ∩ {x : ℝ × ℝ | x.2 ≤ x.1} := by
    ext x
    simp only [rateDomain,mem_setOf_eq,mem_inter_iff,mem_prod,mem_Icc]
    constructor
    · rintro ⟨h0,h1,h2,h3⟩
      exact ⟨⟨⟨h0,h1⟩,⟨h2,h3.trans h1⟩⟩,h3⟩
    · rintro ⟨⟨⟨h0,h1⟩,⟨h2,_⟩⟩,h3⟩
      exact ⟨h0,h1,h2,h3⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).inter_right hclosed

/-- Buffer continuity includes zero amplitude. B,L,c are fixed source
parameters, hence the modulus is chosen before the later finite slot data. -/
theorem rawRate_continuousOn {B L c floor : ℝ} (hL : (3/2:ℝ) ≤ L) (hfloor : 0 < floor) :
    ContinuousOn (fun x : ℝ × ℝ => rawRepeatedCountRate B L c x.1 x.2) (rateDomain floor) := by
  intro x hx
  have hν : 0 < x.1 := hfloor.trans_le hx.1
  have hνhi : x.1 ≤ (3/4:ℝ) := hx.2.1
  have hv0 : 0 ≤ x.2 := hx.2.2.1
  have hv : x.2 ≤ x.1 := hx.2.2.2
  have hLp : 0 < L := by linarith
  have hp : x.2/(2*x.1) ≤ (1/2:ℝ) :=
    (div_le_iff₀ (by positivity : 0 < 2*x.1)).2 (by linarith)
  have hp0 : 0 ≤ x.2/(2*x.1) := by positivity
  have hA : 0 < 2-4*(x.2/(2*x.1))/L := by
    have hq : 4*(x.2/(2*x.1))/L ≤ (4/3:ℝ) := (div_le_iff₀ hLp).2 (by linarith)
    linarith
  have hD1 := (branch_den_pos hν hνhi hp (by norm_num : (0:ℝ)<2)).ne'
  have hD2 := (branch_den_pos hν hνhi hp hA).ne'
  have hνn : 2*x.1 ≠ 0 := by positivity
  have hD1c : ContinuousAt (fun y : ℝ × ℝ => crossingDen y.1 (y.2/(2*y.1)) 2) x := by
    unfold crossingDen
    fun_prop (disch := assumption)
  have hD2c : ContinuousAt (fun y : ℝ × ℝ => crossingDen y.1 (y.2/(2*y.1)) (2-4*(y.2/(2*y.1))/L)) x := by
    unfold crossingDen
    fun_prop (disch := assumption)
  have hc : ContinuousAt (fun y : ℝ × ℝ => rawRepeatedCountRate B L c y.1 y.2) x := by
    unfold rawRepeatedCountRate capCrossingRate budgetCrossingRate crossingRate
    fun_prop (disch := assumption)
  exact hc.continuousWithinAt

theorem rawRate_uniformContinuousOn {B L c floor : ℝ} (hL : (3/2:ℝ) ≤ L) (hfloor : 0 < floor) :
    UniformContinuousOn (fun x : ℝ × ℝ => rawRepeatedCountRate B L c x.1 x.2) (rateDomain floor) :=
  (rateDomain_compact floor).uniformContinuousOn_of_continuous (rawRate_continuousOn hL hfloor)

/-- One absolute buffer budget for simultaneous zero-slope and amplitude
perturbations; it is independent of the slot count and of the analytic scale. -/
theorem rawRate_buffer {B L c floor ε : ℝ} (hL : (3/2:ℝ) ≤ L) (hfloor : 0 < floor)
    (hε : 0 < ε) : ∃ η : ℝ, 0 < η ∧
    ∀ ν v ν' v' : ℝ, (ν,v) ∈ rateDomain floor → (ν',v') ∈ rateDomain floor →
      |ν-ν'| < η → |v-v'| < η →
      |rawRepeatedCountRate B L c ν v-rawRepeatedCountRate B L c ν' v'| < ε := by
  obtain ⟨η,hη,hh⟩ := (Metric.uniformContinuousOn_iff.mp (rawRate_uniformContinuousOn
    (B:=B) (c:=c) hL hfloor)) ε hε
  refine ⟨η,hη,?_⟩
  intro ν v ν' v' hdom hdom' hν hv
  have hd : dist (ν,v) (ν',v') < η := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact max_lt hν hv
  simpa only [Real.dist_eq] using hh (ν,v) hdom (ν',v') hdom' hd

end
end Qrh.JointDetector.RepeatedMarks
