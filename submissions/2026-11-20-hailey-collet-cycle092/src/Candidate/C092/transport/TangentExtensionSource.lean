/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The complete genuine tangent paired source down to .72. -/
import Candidate.C092.transport.TangentExtensionInduction
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorContinuum.ContactSource
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.TangentExtension
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorContinuum

lemma tangent_below_new_line {r : ℝ} (hr : 0 ≤ r) :
    Contact.exactLine.g0-Contact.exactLine.g1*r ≤
      (Certificate.targetG0:ℝ)-(Certificate.targetG1:ℝ)*r := by
  have hc := Contact.tangent_coefficient_bounds
  have hm := mul_le_mul_of_nonneg_right hc.2.2.1.le hr
  change Contact.tangentIntercept-(-Contact.tangentSlope)*r ≤ _
  norm_num [Certificate.targetG0,Certificate.targetG1]
  linarith

/-- Both original source rectangles, with their complete natural coefficients,
original rays, measures, masks, independent heights and all positive decrements.
The extension is the actual finite source induction, with no analytic premise. -/
theorem tangent_full_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (18/25) (311/400) Contact.exactLine.g0 Contact.exactLine.g1 := by
  intro r hr hr'
  by_cases h : r ≤ 1467/2000
  · have hs := Certificate.finite_improved_moments hβ r hr h
    apply hs.mono le_rfl
    have hg := tangent_below_new_line (r := r) (by linarith)
    linarith
  · exact Contact.tangent_full_moments hβ r (le_of_not_ge h) hr'

/-- Genuine inverse source at every open rectangle below the full tangent. -/
theorem genuine_tangent_inverse
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    {R δ : ℝ} (hR : 18/25 ≤ R) (hR' : R ≤ 311/400) (hδ : 0 < δ) :
    UniformInverseRectSource canonicalFamily
      (anchorRect R (Contact.exactLine.g0-Contact.exactLine.g1*R) δ) :=
  ((tangent_full_moments hβ R hR hR') δ hδ).1

/-- Genuine positive two-ordinary source on its individual original rectangle. -/
theorem genuine_tangent_ordinary
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    {R δ : ℝ} (hR : 18/25 ≤ R) (hR' : R ≤ 311/400) (hδ : 0 < δ) :
    OrdinaryRectSource (anchorRect R (Contact.exactLine.g0-Contact.exactLine.g1*R) δ) :=
  ((tangent_full_moments hβ R hR hR') δ hδ).2

/-- The literal fixed-detector anchor lies strictly inside the new genuine
source range; its two columns retain all positive rectangle decrements. -/
theorem fixed_detector_anchor
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    AnchorAt (360001/500000)
      (Contact.exactLine.g0-Contact.exactLine.g1*(360001/500000)) :=
  tangent_full_moments hβ _ (by norm_num) (by norm_num)

end QRH.Cycle092.TangentExtension
#print axioms QRH.Cycle092.TangentExtension.tangent_full_moments
#print axioms QRH.Cycle092.TangentExtension.genuine_tangent_inverse
#print axioms QRH.Cycle092.TangentExtension.genuine_tangent_ordinary

#print axioms QRH.Cycle092.TangentExtension.fixed_detector_anchor
