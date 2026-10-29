/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates
noncomputable section
set_option autoImplicit false
open Set

/-- A finite secant is an actual derivative ratio at an intermediate point.
The positive slope difference fixes the direction of the source transfer. -/
theorem positive_secant_ratio {a b : ℝ} (hab : a < b)
    (f g df dg : ℝ → ℝ)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (df x) x)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (dg x) x)
    (hgp : ∀ x ∈ Icc a b, 0 < dg x) :
    0 < g b-g a ∧ ∃ c ∈ Ioo a b, (f b-f a)/(g b-g a) = df c/dg c := by
  have hgc : ContinuousOn g (Icc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn g (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hgc
    intro x hx
    have hxc : x ∈ Icc a b := interior_subset hx
    rw [(hg x hxc).deriv]
    exact hgp x hxc
  have hdelta : 0 < g b-g a := sub_pos.mpr (hmono ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hab)
  obtain ⟨c,hc,heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f df hab hfc
    (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩) g dg hgc
    (fun x hx => hg x ⟨hx.1.le,hx.2.le⟩)
  refine ⟨hdelta,c,hc,?_⟩
  apply (div_eq_div_iff hdelta.ne' (hgp c ⟨hc.1.le,hc.2.le⟩).ne').2
  nlinarith [heq]

/-- The finite source crossing lies on the tangent-crossing curve between its
child and parent. In particular continuity controls it uniformly on compact pieces. -/
theorem source_secant_intermediate {a b : ℝ} (hab : a < b)
    (y k : ℝ → ℝ)
    (hy : ∀ q ∈ Icc a b, HasDerivAt y (-k q) q)
    (hq : ∀ q ∈ Icc a b, q ≠ 0)
    (hy0 : ∀ q ∈ Icc a b, y q ≠ 0)
    (hk : ∀ q ∈ Icc a b, 0 < k q) :
    0 < slope (y b)-slope (y a) ∧ ∃ c ∈ Ioo a b,
      (intercept b (y b)-intercept a (y a))/(slope (y b)-slope (y a)) =
      crossingNumerator c (y c) (k c)/denominator c (k c) := by
  obtain ⟨hd,c,hc,hr⟩ := positive_secant_ratio hab
    (fun q => intercept q (y q)) (fun q => slope (y q))
    (fun q => crossingNumerator q (y q) (k q)/(6*q^2*(y q)^2))
    (fun q => k q/(y q)^2)
    (fun q h => hasDerivAt_intercept (hy q h) (hq q h) (hy0 q h))
    (fun q h => hasDerivAt_slope (hy q h) (hy0 q h))
    (fun q h => div_pos (hk q h) (sq_pos_of_ne_zero (hy0 q h)))
  refine ⟨hd,c,hc,?_⟩
  rw [hr, tangent_ratio (hq c ⟨hc.1.le,hc.2.le⟩)
    (hy0 c ⟨hc.1.le,hc.2.le⟩) (hk c ⟨hc.1.le,hc.2.le⟩).ne']

/-- One step size controls every secant on a compact curve piece. This is a
scalar uniformity statement, chosen before any arithmetic source data. -/
theorem uniform_secant_control {a b ε : ℝ} (f g df dg : ℝ → ℝ)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (df x) x)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (dg x) x)
    (hgp : ∀ x ∈ Icc a b, 0 < dg x)
    (hr : ContinuousOn (fun x => df x/dg x) (Icc a b)) (hε : 0 < ε) :
    ∃ δ > 0, ∀ child ∈ Icc a b, ∀ parent ∈ Icc a b,
      child < parent → parent-child ≤ δ →
      0 < g parent-g child ∧
      |(f parent-f child)/(g parent-g child)-df parent/dg parent| < ε := by
  obtain ⟨d,hd,hmod⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hr) ε hε
  refine ⟨d/2, by positivity, ?_⟩
  intro child hc parent hp hcp hsmall
  have hsub : Icc child parent ⊆ Icc a b := by
    intro x hx
    exact ⟨hc.1.trans hx.1,hx.2.trans hp.2⟩
  obtain ⟨hdelta,c,hci,hsec⟩ := positive_secant_ratio hcp f g df dg
    (fun x hx => hf x (hsub hx)) (fun x hx => hg x (hsub hx))
    (fun x hx => hgp x (hsub hx))
  refine ⟨hdelta,?_⟩
  rw [hsec]
  have hdist : dist c parent < d := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hci.2.le)]
    linarith [hci.1]
  simpa only [Real.dist_eq] using
    hmod c (hsub ⟨hci.1.le,hci.2.le⟩) parent hp hdist

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates.source_secant_intermediate
