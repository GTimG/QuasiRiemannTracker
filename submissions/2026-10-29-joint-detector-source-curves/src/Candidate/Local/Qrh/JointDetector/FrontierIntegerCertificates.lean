/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerCertificates
import Candidate.Local.Qrh.JointDetector.FrontierIntegerPiece
import Candidate.Local.Qrh.JointDetector.FrontierCutoffInteger
namespace Qrh.JointDetector.FrontierIntegerCertificates
noncomputable section
set_option autoImplicit false
open RepeatedMarks.SourceCurveInteger

def OtherCombinedSigns (p : Params) (lo hi : ℤ) : Prop :=
 ∀ i, i≠3 → ∀ j,0<bernsteinNumerator (combinedNumerator p i) p.den lo hi j

def CutoffSigns (p : Params) (lo hi : ℤ) : Prop :=
 ∀ j,0<bernsteinNumerator (FrontierCutoffInteger.numerator p) p.den lo hi j

theorem combined_positive {p : Params} {lo hi : ℤ} (hw : lo<hi)
 (hother : OtherCombinedSigns p lo hi) (hcutoff : CutoffSigns p lo hi)
 {u : ℝ} (hu : u∈Set.Icc ((lo:ℝ)/(p.den:ℝ)) ((hi:ℝ)/(p.den:ℝ))) :
 ∀ i,0<FrontierSourceCurveCertificate.combined (p.toReal.state u) i := by
 intro i
 by_cases hi : i=3
 · subst i; exact FrontierCutoffInteger.positive hw hcutoff hu
 · rw [FrontierSourceCurveCertificate.combined,if_neg hi,←combinedGate_state,←eval_combinedPower]
   change 0<RepeatedMarks.SourceCurveCertificate.eval
     (fun j=>(combinedNumerator p i j:ℝ)/(denominator p:ℝ)) u
   exact positive_of_numerator p.den_pos (denominator_pos p) hw (hother i hi) hu

theorem combined_source_of_signs {p : Params} {lo hi : ℤ} (hw : lo<hi)
 (heps : 0<p.toReal.eps) (hcap : p.toReal.cap=1/10)
 (hc : CommonSigns p lo hi) (hother : OtherCombinedSigns p lo hi)
 (hcutoff : CutoffSigns p lo hi)
 (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
 (seed : QRH.Record1252270103Source.GlobalSource
   (p.toReal.state ((hi:ℝ)/(p.den:ℝ))).B
   (p.toReal.state ((hi:ℝ)/(p.den:ℝ))).L (1/10)) :
 QRH.Record1252270103Source.GlobalSource
   (p.toReal.state ((lo:ℝ)/(p.den:ℝ))).B
   (p.toReal.state ((lo:ℝ)/(p.den:ℝ))).L (1/10) := by
 apply FrontierIntegerPiece.combined_source p.toReal
   ((div_le_div_iff_of_pos_right (by exact_mod_cast p.den_pos)).2 (by exact_mod_cast hw.le))
   heps hcap _ _ hβ seed
 · intro u hu; exact common_positive hw hc hu
 · intro u hu; exact combined_positive hw hother hcutoff hu

end
end Qrh.JointDetector.FrontierIntegerCertificates
