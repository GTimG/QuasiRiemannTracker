/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerEval
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerBernstein
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerPiece
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveJoins
namespace Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
noncomputable section
set_option autoImplicit false
open FractionArithmetic

def CommonSigns (p : Params) (lo hi : ℤ) : Prop :=
  ∀ i j,0<bernsteinNumerator (commonNumerator p i) p.den lo hi j
def CombinedSigns (p : Params) (lo hi : ℤ) : Prop :=
  ∀ i j,0<bernsteinNumerator (combinedNumerator p i) p.den lo hi j
def PureSigns (p : Params) (lo hi : ℤ) : Prop :=
  ∀ i j,0<bernsteinNumerator (pureNumerator p i) p.den lo hi j

theorem common_positive {p : Params} {lo hi : ℤ} (hw : lo<hi) (h : CommonSigns p lo hi)
    {u : ℝ} (hu : u∈Set.Icc ((lo:ℝ)/(p.den:ℝ)) ((hi:ℝ)/(p.den:ℝ))) :
    ∀ i,0<commonGate p.toReal i u := by
  intro i
  rw [←eval_commonPower]
  change 0<SourceCurveCertificate.eval (fun j=>(commonNumerator p i j:ℝ)/(denominator p:ℝ)) u
  exact positive_of_numerator p.den_pos (denominator_pos p) hw (h i) hu

theorem combined_positive {p : Params} {lo hi : ℤ} (hw : lo<hi) (h : CombinedSigns p lo hi)
    {u : ℝ} (hu : u∈Set.Icc ((lo:ℝ)/(p.den:ℝ)) ((hi:ℝ)/(p.den:ℝ))) :
    ∀ i,0<combinedGate p.toReal i u := by
  intro i
  rw [←eval_combinedPower]
  change 0<SourceCurveCertificate.eval (fun j=>(combinedNumerator p i j:ℝ)/(denominator p:ℝ)) u
  exact positive_of_numerator p.den_pos (denominator_pos p) hw (h i) hu

theorem pure_positive {p : Params} {lo hi : ℤ} (hw : lo<hi) (h : PureSigns p lo hi)
    {u : ℝ} (hu : u∈Set.Icc ((lo:ℝ)/(p.den:ℝ)) ((hi:ℝ)/(p.den:ℝ))) :
    ∀ i,0<pureGate p.toReal i u := by
  intro i
  rw [←eval_purePower]
  change 0<SourceCurveCertificate.eval (fun j=>(pureNumerator p i j:ℝ)/(denominator p:ℝ)) u
  exact positive_of_numerator p.den_pos (denominator_pos p) hw (h i) hu

/-- The rounded join weakens both source coordinates by the same factor. -/
theorem state_source_join (p : SourceCurveCertificate.State)
    (heps : 0 < p.eps) (hcap : p.cap=1/10)
    (hc : ∀ i,0 < p.common i) {nextY : ℝ} (hnext : p.y ≤ nextY)
    (hs : QRH.Record1252270103Source.GlobalSource p.B p.L (1/10)) :
    QRH.Record1252270103Source.GlobalSource
      ((1+p.q)/(6*p.q*nextY)) (1/nextY) (1/10) := by
  have f := SourceCurveCertificate.common_facts p heps hcap hc
  have hg := hc 10
  norm_num [SourceCurveCertificate.State.common,hcap] at hg
  have hid : p.B-p.L*(1/10)=
      (1+p.q-6*p.q*(1/10))/(6*p.q*p.y) := by
    dsimp [SourceCurveCertificate.State.B,SourceCurveCertificate.State.L]
    field_simp [f.q_pos.ne',f.y_pos.ne'] <;> ring
  have hbudget : 0 ≤ p.B-p.L*(1/10) := by
    rw [hid]
    exact (div_pos (by linarith) (mul_pos (mul_pos (by norm_num) f.q_pos) f.y_pos)).le
  exact source_reciprocal_join f.q_pos f.y_pos hnext (by norm_num) hbudget hs

/-- Exact integer signs are consumed by the full proved cubic source curve. -/
theorem combined_source_of_signs {p : Params} {lo hi : ℤ} (hw : lo<hi)
    (heps : 0<p.toReal.eps) (hcap : p.toReal.cap=1/10)
    (hc : CommonSigns p lo hi) (hr : CombinedSigns p lo hi)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (seed : QRH.Record1252270103Source.GlobalSource
      (p.toReal.state ((hi:ℝ)/(p.den:ℝ))).B
      (p.toReal.state ((hi:ℝ)/(p.den:ℝ))).L (1/10)) :
    QRH.Record1252270103Source.GlobalSource
      (p.toReal.state ((lo:ℝ)/(p.den:ℝ))).B
      (p.toReal.state ((lo:ℝ)/(p.den:ℝ))).L (1/10) := by
  apply combined_source p.toReal
    ((div_le_div_iff_of_pos_right (by exact_mod_cast p.den_pos)).2 (by exact_mod_cast hw.le))
    heps hcap _ _ hβ seed
  · intro u hu; exact common_positive hw hc hu
  · intro u hu; exact combined_positive hw hr hu

theorem pure_source_of_signs {p : Params} {lo hi : ℤ} (hw : lo<hi)
    (heps : 0<p.toReal.eps) (hcap : p.toReal.cap=1/10)
    (hc : CommonSigns p lo hi) (hr : PureSigns p lo hi)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (seed : QRH.Record1252270103Source.GlobalSource
      (p.toReal.state ((hi:ℝ)/(p.den:ℝ))).B
      (p.toReal.state ((hi:ℝ)/(p.den:ℝ))).L (1/10)) :
    QRH.Record1252270103Source.GlobalSource
      (p.toReal.state ((lo:ℝ)/(p.den:ℝ))).B
      (p.toReal.state ((lo:ℝ)/(p.den:ℝ))).L (1/10) := by
  apply pure_source p.toReal
    ((div_le_div_iff_of_pos_right (by exact_mod_cast p.den_pos)).2 (by exact_mod_cast hw.le))
    heps hcap _ _ hβ seed
  · intro u hu; exact common_positive hw hc hu
  · intro u hu; exact pure_positive hw hr hu

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveInteger

#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveInteger.combined_source_of_signs
