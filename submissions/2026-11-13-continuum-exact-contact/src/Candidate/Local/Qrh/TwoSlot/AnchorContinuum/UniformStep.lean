/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Uniform positive differential reserve and one common finite-step radius for
all points of a fixed strict continuum subcurve. No analytic moment limit is taken. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.Curve
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.FiniteStep
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum.Curve
open Set

theorem continuousAt_A {r : ℝ} (hr : 2/3 < r) : ContinuousAt A r := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hs : r-2/3 ≠ 0 := ne_of_gt (by linarith)
  exact (continuousAt_const.div continuousAt_id hr0).add
    (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hs)

theorem continuousAt_b {r : ℝ} (hr : 2/3 < r) : ContinuousAt b r := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hl : 15*r-10 ≠ 0 := ne_of_gt (by linarith)
  exact ((continuousAt_const.mul continuousAt_id).sub continuousAt_const).div
    (continuousAt_id.mul ((continuousAt_const.mul continuousAt_id).sub continuousAt_const))
    (mul_ne_zero hr0 hl)

theorem continuousAt_D (lam T : ℝ) {r : ℝ} (hr : 2/3 < r) :
    ContinuousAt (D lam T) r :=
  continuousAt_const.mul
    (((continuousAt_A hr).mul (hasDerivAt_Z T hr).continuousAt).add (continuousAt_b hr))

/-- Compactness supplies the strictly positive reserve before stage lengths,
source padding, detector data or heights are selected. -/
theorem uniform_reserve {lam T : ℝ} (hlam : lam < 1)
    (hT : 3/4 ≤ T) (hT1 : T < 7/9) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ r ∈ Icc (3/4:ℝ) T,
      3*gamma ≤ D lam T r-flow r (W lam T r) := by
  have hc : ContinuousOn (fun r => D lam T r-flow r (W lam T r)) (Icc (3/4:ℝ) T) := by
    simp_rw [strict_reserve_identity]
    exact continuousOn_const.mul (fun r hr => (continuousAt_b (by linarith [hr.1])).continuousWithinAt)
  obtain ⟨g,hg,hall⟩ := isCompact_Icc.exists_forall_le' hc
    (fun r hr => strict_reserve_pos hlam (by linarith [hr.1]) (by linarith [hr.2]))
  refine ⟨g/3,by linarith,?_⟩
  intro r hr
  have h := hall r hr
  linarith

/-- One positive finite-step radius works everywhere on a fixed subcurve. -/
theorem uniform_finite_steps (lam T : ℝ) (hT : 3/4 ≤ T) {gamma : ℝ}
    (hg : 0 < gamma) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ r R : ℝ, 3/4 ≤ r → r ≤ R → R ≤ T → R-r ≤ eta →
      ∀ x ∈ Icc r R, W lam T x ≤ W lam T R+(D lam T R-gamma)*(x-R) := by
  have hc : ContinuousOn (D lam T) (Icc (3/4:ℝ) T) :=
    fun r hr => (continuousAt_D lam T (by linarith [hr.1])).continuousWithinAt
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hc
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu gamma hg
  refine ⟨delta/2,by linarith,?_⟩
  intro r R hr hrR hRT hlength
  apply Qrh.TwoSlot.AnchorContinuum.finite_step_dominates hrR
    (fun x hx => hasDerivAt_W lam T (by linarith [hx.1]))
  intro x hx
  have hdist : dist R x < delta := by
    rw [Real.dist_eq,abs_of_nonneg (by linarith [hx.2])]
    linarith [hx.1]
  have h := hclose R ⟨by linarith,hRT⟩ x ⟨by linarith [hx.1],by linarith [hx.2]⟩ hdist
  rw [Real.dist_eq] at h
  have hh := (abs_lt.mp h).2
  linarith

end Qrh.TwoSlot.AnchorContinuum.Curve
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.uniform_reserve
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.uniform_finite_steps
