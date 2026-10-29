/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveFunctionCoordinates
import Candidate.Local.Qrh.JointDetector.FrontierSourceCurveTheorem

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveFunctionCoordinates
noncomputable section
set_option autoImplicit false
open Set SourceCurveCertificate

/-- Arbitrary fixed-degree paths feed the actual small-gap source theorem.
All path assumptions are scalar calculus and geometry conditions. -/
theorem frontier_source (p : Path) {lo hi floor : ℝ} (hab : lo ≤ hi)
 (hd : Data p lo hi) (hf : ∀ u∈Icc lo hi, CommonFacts (p.state u))
 (hc : ∀ u∈Icc lo hi,
   FrontierRepeatedMarks.SourceCurve.RayCrossing
     (p.state u).B (p.state u).L (p.state u).s (p.state u).n (p.state u).r)
 (hfloor : (50001/100000:ℝ) ≤ floor)
 (hnfloor : ∀ u∈Icc lo hi, floor ≤ (p.state u).n)
 (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
 (seed : QRH.Record1252270103Source.GlobalSource (p.state hi).B (p.state hi).L (1/10)) :
 QRH.Record1252270103Source.GlobalSource (p.state lo).B (p.state lo).L (1/10) :=
 FrontierRepeatedMarks.SourceCurve.combined_curve_source hab
   (fun u => (p.state u).B) (fun u => (p.state u).L) p.dB p.dL
   (fun u => (p.state u).s) (fun u => (p.state u).n) (fun u => (p.state u).r)
   hd.B_derivative hd.L_derivative hd.L_derivative_pos hd.s_continuous hd.n_continuous
   hd.r_continuous hd.tangent_ratio hc (fun u hu => (hf u hu).B_min)
   (fun u hu => (hf u hu).B_max) (fun u hu => (hf u hu).C_nonneg)
   (fun u hu => (hf u hu).low_gap) hfloor hnfloor (fun u hu => (hf u hu).gates) hβ seed

/-- The repeated-only part is degree-independent as well. -/
theorem pure_source (p : Path) {lo hi floor : ℝ} (hab : lo ≤ hi)
 (hd : Data p lo hi) (hf : ∀ u∈Icc lo hi, CommonFacts (p.state u))
 (hc : ∀ u∈Icc lo hi,
   SourceCurve.PureCrossing (p.state u).B (p.state u).L (p.state u).s (p.state u).n)
 (hfloor : (2/5:ℝ) ≤ floor)
 (hnfloor : ∀ u∈Icc lo hi, floor ≤ (p.state u).n)
 (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
 (seed : QRH.Record1252270103Source.GlobalSource (p.state hi).B (p.state hi).L (1/10)) :
 QRH.Record1252270103Source.GlobalSource (p.state lo).B (p.state lo).L (1/10) :=
 SourceCurve.pure_curve_source hab
   (fun u => (p.state u).B) (fun u => (p.state u).L) p.dB p.dL
   (fun u => (p.state u).s) (fun u => (p.state u).n)
   hd.B_derivative hd.L_derivative hd.L_derivative_pos hd.s_continuous hd.n_continuous
   hd.tangent_ratio hc (fun u hu => (hf u hu).B_min)
   (fun u hu => (hf u hu).B_max) (fun u hu => (hf u hu).C_nonneg)
   (fun u hu => (hf u hu).low_gap) hfloor hnfloor (fun u hu => (hf u hu).gates) hβ seed

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveFunctionCoordinates
