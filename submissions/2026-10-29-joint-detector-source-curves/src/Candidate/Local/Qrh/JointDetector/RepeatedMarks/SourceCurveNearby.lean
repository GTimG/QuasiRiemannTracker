/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveSecants

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates
noncomputable section
set_option autoImplicit false
open Set

/-- One interval step size controls both source coordinates and their finite
crossing. It follows from ordinary continuity and Cauchy's mean value theorem. -/
theorem uniform_coordinates_and_secant {a b : ℝ} (B L dB dL s : ℝ → ℝ)
    (hB : ∀ x∈Icc a b, HasDerivAt B (dB x) x)
    (hL : ∀ x∈Icc a b, HasDerivAt L (dL x) x)
    (hdL : ∀ x∈Icc a b, 0 < dL x)
    (hs : ContinuousOn s (Icc a b))
    (hratio : ∀ x∈Icc a b, dB x/dL x=s x) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x∈Icc a b, ∀ y∈Icc a b, x < y → y-x ≤ δ →
      0 < L y-L x ∧ |B x-B y| ≤ η ∧ |L x-L y| ≤ η ∧
        |(B y-B x)/(L y-L x)-s y| ≤ η := by
  have hBc : ContinuousOn B (Icc a b) := fun x hx => (hB x hx).continuousAt.continuousWithinAt
  have hLc : ContinuousOn L (Icc a b) := fun x hx => (hL x hx).continuousAt.continuousWithinAt
  have hsc : ContinuousOn (fun x => dB x/dL x) (Icc a b) :=
    hs.congr (fun x hx => hratio x hx)
  intro η hη
  obtain ⟨dB0,hdB,hmodB⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hBc) η hη
  obtain ⟨dL0,hdL0,hmodL⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hLc) η hη
  obtain ⟨dS,hdS,hmodS⟩ := uniform_secant_control B L dB dL hB hL hdL hsc hη
  let δ := min (dB0/2) (min (dL0/2) dS)
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) hdS)
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy hxy hsmall
  have hδB : δ ≤ dB0/2 := min_le_left _ _
  have hδL : δ ≤ dL0/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδS : δ ≤ dS := (min_le_right _ _).trans (min_le_right _ _)
  have hdist : dist x y=y-x := by
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy.le)]
    ring
  have hdistB : dist x y < dB0 := by rw [hdist]; linarith
  have hdistL : dist x y < dL0 := by rw [hdist]; linarith
  obtain ⟨hΔ,hsec⟩ := hmodS x hx y hy hxy (hsmall.trans hδS)
  refine ⟨hΔ,?_,?_,?_⟩
  · exact le_of_lt (by simpa only [Real.dist_eq] using hmodB x hx y hy hdistB)
  · exact le_of_lt (by simpa only [Real.dist_eq] using hmodL x hx y hy hdistL)
  · rw [hratio y hy] at hsec
    exact hsec.le

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates.uniform_coordinates_and_secant
