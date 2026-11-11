import Candidate.Local.Qrh.PositiveGap.Return.Tuning.EndpointFromSources
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PositiveGap.Return.Tuning
open QRH.Record1252270103Return QRH.PositiveGap.ReturnTuning Qrh.JointDetector.BoundaryPhysical.Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
variable [TargetC]
abbrev countSourceFace : SourceFace := QRH.Record1252270103Source.globalFace (1 - eps) (2 + 10 * eps) (671447/5000000)
abbrev physicalSourceFace : SourceFace := QRH.Record1252270103Source.globalFace (1 - eps) (2 + 10 * eps) (671447/5000000)
theorem source_restricts_count : countSourceFace.Restricts countGlobal := by
 constructor <;> (dsimp [countSourceFace,QRH.Record1252270103Source.globalFace,countGlobal,
  QRH.Record1252270103Return.globalFace,countCB,countCL,countCap]; linarith [eps_pos, eps_le])
theorem source_restricts_physical : physicalSourceFace.Restricts physicalGlobal := by
 constructor <;> (dsimp [physicalSourceFace,QRH.Record1252270103Source.globalFace,physicalGlobal,
  QRH.Record1252270103Return.globalFace,physicalB,physicalLambda,physicalCap]; linarith [eps_pos, eps_le])
theorem uniform_restrict {strong weak : SourceFace} (h : strong.Restricts weak)
 (hs : UniformUnitFaceSource strong) : UniformUnitFaceSource weak := by
 intro ε hε
 obtain ⟨mesh,hm,hsrc⟩ := hs ε hε
 exact ⟨mesh,hm,unit_source_restrict h hsrc⟩
omit [TargetC] in
lemma natural_cap_return : 2*HeckeZeroSupremum.beta-1≤naturalK/6 := by
 have hi := QRH.RepeatedMarks.beta_le_seven_eighths
 norm_num [naturalK]
 linarith
theorem beta_of_two_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal) :
 HeckeZeroSupremum.beta≤theta :=
 Final.beta_of_global_sources hC hP natural_cap_return
theorem beta_le_theta_of_sources
    (hC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (1 - eps) (2 + 10 * eps) (671447/5000000))
    (hP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (1 - eps) (2 + 10 * eps) (671447/5000000)) :
    HeckeZeroSupremum.beta ≤ theta := by
  by_cases hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
  · exact beta_of_two_global_sources (uniform_restrict source_restricts_count (hC hbeta))
      (uniform_restrict source_restricts_physical (hP hbeta))
  · have ht : (51/100:ℝ) ≤ theta := by unfold theta; linarith [c_hi]
    exact (not_le.mp hbeta).le.trans ht
theorem beta_le_target_of_global_source
    (h : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (1 - eps) (2 + 10 * eps) (671447/5000000)) :
    HeckeZeroSupremum.beta ≤ theta :=
  beta_le_theta_of_sources h h
end
end QRH.PositiveGap.Return.Tuning
