/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveUniformGeometry
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveNearby
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.PureSourceCurveReachability

namespace Qrh.JointDetector.RepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
open Set SourceCurveCoordinates SourceCurveOpenGeometry

/-- A strict differentiable combined-count curve yields a finite source
construction. Every remaining hypothesis is an explicit scalar curve gate. -/
theorem combined_curve_source {a b floor : ℝ} (hab : a ≤ b)
    (B L dB dL s n r : ℝ → ℝ)
    (hB : ∀ x∈Icc a b, HasDerivAt B (dB x) x)
    (hL : ∀ x∈Icc a b, HasDerivAt L (dL x) x)
    (hdL : ∀ x∈Icc a b, 0 < dL x)
    (hs : ContinuousOn s (Icc a b)) (hn : ContinuousOn n (Icc a b))
    (hr : ContinuousOn r (Icc a b))
    (hratio : ∀ x∈Icc a b, dB x/dL x=s x)
    (hcert : ∀ x∈Icc a b, RayCrossing (B x) (L x) (s x) (n x) (r x))
    (hBmin : ∀ x∈Icc a b, (9/10:ℝ) ≤ B x)
    (hBmax : ∀ x∈Icc a b, B x < 1)
    (hC : ∀ x∈Icc a b, 0 ≤ 6*B x-L x)
    (hgap : ∀ x∈Icc a b, 0 < L x-n x*(6*B x-L x))
    (hfloor : (50001/100000:ℝ) ≤ floor)
    (hnfloor : ∀ x∈Icc a b, floor ≤ n x)
    (hgates : ∀ x∈Icc a b, ∀ i, 0 < gate (B x) (L x) (s x) 0 (1/10) i)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (seed : QRH.Record1252270103Source.GlobalSource (B b) (L b) (1/10)) :
    QRH.Record1252270103Source.GlobalSource (B a) (L a) (1/10) := by
  have hBc : ContinuousOn B (Icc a b) := fun x hx => (hB x hx).continuousAt.continuousWithinAt
  have hLc : ContinuousOn L (Icc a b) := fun x hx => (hL x hx).continuousAt.continuousWithinAt
  have hnear := uniform_coordinates_and_secant B L dB dL s hB hL hdL hs hratio
  have hscalar := uniform_scalar_step_geometry hab B L s n hBc hLc hs hn
    (by linarith : 0 < floor) (fun x hx => (hcert x hx).B_pos) hBmax
    (fun x hx => (hcert x hx).L_lower) hC hnfloor (fun x hx => (hcert x hx).n_upper.le)
    hgap hgates hnear
  exact piece_reachable_backward hab B L s n r hBc hLc hs hn hr hcert hBmin hfloor hscalar hβ seed

/-- The lower-density part uses the repeated count alone; no selected-count
cutoff or below-half operator bound occurs in this theorem. -/
theorem pure_curve_source {a b floor : ℝ} (hab : a ≤ b)
    (B L dB dL s n : ℝ → ℝ)
    (hB : ∀ x∈Icc a b, HasDerivAt B (dB x) x)
    (hL : ∀ x∈Icc a b, HasDerivAt L (dL x) x)
    (hdL : ∀ x∈Icc a b, 0 < dL x)
    (hs : ContinuousOn s (Icc a b)) (hn : ContinuousOn n (Icc a b))
    (hratio : ∀ x∈Icc a b, dB x/dL x=s x)
    (hcert : ∀ x∈Icc a b, PureCrossing (B x) (L x) (s x) (n x))
    (hBmin : ∀ x∈Icc a b, (9/10:ℝ) ≤ B x)
    (hBmax : ∀ x∈Icc a b, B x < 1)
    (hC : ∀ x∈Icc a b, 0 ≤ 6*B x-L x)
    (hgap : ∀ x∈Icc a b, 0 < L x-n x*(6*B x-L x))
    (hfloor : (2/5:ℝ) ≤ floor)
    (hnfloor : ∀ x∈Icc a b, floor ≤ n x)
    (hgates : ∀ x∈Icc a b, ∀ i, 0 < gate (B x) (L x) (s x) 0 (1/10) i)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (seed : QRH.Record1252270103Source.GlobalSource (B b) (L b) (1/10)) :
    QRH.Record1252270103Source.GlobalSource (B a) (L a) (1/10) := by
  have hBc : ContinuousOn B (Icc a b) := fun x hx => (hB x hx).continuousAt.continuousWithinAt
  have hLc : ContinuousOn L (Icc a b) := fun x hx => (hL x hx).continuousAt.continuousWithinAt
  have hnear := uniform_coordinates_and_secant B L dB dL s hB hL hdL hs hratio
  have hscalar := uniform_scalar_step_geometry hab B L s n hBc hLc hs hn
    (by linarith : 0 < floor) (fun x hx => (hcert x hx).B_pos) hBmax
    (fun x hx => (hcert x hx).L_lower) hC hnfloor (fun x hx => (hcert x hx).n_upper.le)
    hgap hgates hnear
  exact pure_piece_reachable_backward hab B L s n hBc hLc hs hn hcert hBmin hfloor hscalar hβ seed

end
end Qrh.JointDetector.RepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.combined_curve_source
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.pure_curve_source
