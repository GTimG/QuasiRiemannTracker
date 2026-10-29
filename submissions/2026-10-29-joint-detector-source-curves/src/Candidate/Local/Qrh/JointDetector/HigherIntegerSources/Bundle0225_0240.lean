/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0225_0228
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0229_0232
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0233_0236
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0237_0240
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0225_0228
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0225_0228

theorem source225 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (156236808716697831596468620000000000000000000000000000/157244241294802422205592799857359432012629033770560029:ℝ) (40000000000000000000000000000/16775615573686515098687712553:ℝ) (1/10:ℝ)) :
 GlobalSource (195178826395800024353620975000000000000000000000000000/196458623291793668199895342208834543426799914488960569:ℝ) (50000000000000000000000000000/20990696006617945574295110357:ℝ) (1/10:ℝ) := by
 have heps : 0<p225.toReal.eps := by norm_num [p225,Params.toReal]
 have hcap : p225.toReal.cap=1/10 := by norm_num [p225,Params.toReal]
 have hi : GlobalSource (p225.toReal.state (((cells225 0).2:ℝ)/(p225.den:ℝ))).B (p225.toReal.state (((cells225 0).2:ℝ)/(p225.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p225,cells225,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells225 0).1 < (cells225 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p225) hw0 heps hcap (commonSigns225 0) (highSigns225 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns225 0)
   (u:=((cells225 0).1:ℝ)/(p225.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p225.toReal.state (((cells225 0).1:ℝ)/(p225.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(20990696006617945574295110357/50000000000000000000000000000:ℝ)) (by norm_num [p225,cells225,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p225,cells225,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source226 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (195178826395800024353620975000000000000000000000000000/196458623291793668199895342208834543426799914488960569:ℝ) (50000000000000000000000000000/20990696006617945574295110357:ℝ) (1/10:ℝ)) :
 GlobalSource (325102736492879598686093625000000000000000000000000000/327270126684712752389799466090604914706498230041223673:ℝ) (250000000000000000000000000000/105059751495050914572301127359:ℝ) (1/10:ℝ) := by
 have heps : 0<p226.toReal.eps := by norm_num [p226,Params.toReal]
 have hcap : p226.toReal.cap=1/10 := by norm_num [p226,Params.toReal]
 have hi : GlobalSource (p226.toReal.state (((cells226 0).2:ℝ)/(p226.den:ℝ))).B (p226.toReal.state (((cells226 0).2:ℝ)/(p226.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p226,cells226,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells226 0).1 < (cells226 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p226) hw0 heps hcap (commonSigns226 0) (highSigns226 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns226 0)
   (u:=((cells226 0).1:ℝ)/(p226.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p226.toReal.state (((cells226 0).1:ℝ)/(p226.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(105059751495050914572301127359/250000000000000000000000000000:ℝ)) (by norm_num [p226,cells226,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p226,cells226,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source227 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (325102736492879598686093625000000000000000000000000000/327270126684712752389799466090604914706498230041223673:ℝ) (250000000000000000000000000000/105059751495050914572301127359:ℝ) (1/10:ℝ)) :
 GlobalSource (779777829582621976278765500000000000000000000000000000/785062639758787177255351637317000385589044855636640159:ℝ) (1000000000000000000000000000000/420665654267833314262213410863:ℝ) (1/10:ℝ) := by
 have heps : 0<p227.toReal.eps := by norm_num [p227,Params.toReal]
 have hcap : p227.toReal.cap=1/10 := by norm_num [p227,Params.toReal]
 have hi : GlobalSource (p227.toReal.state (((cells227 0).2:ℝ)/(p227.den:ℝ))).B (p227.toReal.state (((cells227 0).2:ℝ)/(p227.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p227,cells227,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells227 0).1 < (cells227 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p227) hw0 heps hcap (commonSigns227 0) (highSigns227 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns227 0)
   (u:=((cells227 0).1:ℝ)/(p227.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p227.toReal.state (((cells227 0).1:ℝ)/(p227.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(420665654267833314262213410863/1000000000000000000000000000000:ℝ)) (by norm_num [p227,cells227,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p227,cells227,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source228 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (779777829582621976278765500000000000000000000000000000/785062639758787177255351637317000385589044855636640159:ℝ) (1000000000000000000000000000000/420665654267833314262213410863:ℝ) (1/10:ℝ)) :
 GlobalSource (3896545457911664578554531500000000000000000000000000000/3923387504858105740630417832382417712774864239932446797:ℝ) (1000000000000000000000000000000/421093872422836041500511890073:ℝ) (1/10:ℝ) := by
 have heps : 0<p228.toReal.eps := by norm_num [p228,Params.toReal]
 have hcap : p228.toReal.cap=1/10 := by norm_num [p228,Params.toReal]
 have hi : GlobalSource (p228.toReal.state (((cells228 0).2:ℝ)/(p228.den:ℝ))).B (p228.toReal.state (((cells228 0).2:ℝ)/(p228.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p228,cells228,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells228 0).1 < (cells228 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p228) hw0 heps hcap (commonSigns228 0) (highSigns228 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns228 0)
   (u:=((cells228 0).1:ℝ)/(p228.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p228.toReal.state (((cells228 0).1:ℝ)/(p228.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(421093872422836041500511890073/1000000000000000000000000000000:ℝ)) (by norm_num [p228,cells228,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p228,cells228,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (156236808716697831596468620000000000000000000000000000/157244241294802422205592799857359432012629033770560029:ℝ) (40000000000000000000000000000/16775615573686515098687712553:ℝ) (1/10:ℝ)) :
 GlobalSource (3896545457911664578554531500000000000000000000000000000/3923387504858105740630417832382417712774864239932446797:ℝ) (1000000000000000000000000000000/421093872422836041500511890073:ℝ) (1/10:ℝ) := by
 have h225 := source225 hβ hp
 have h226 := source226 hβ h225
 have h227 := source227 hβ h226
 have h228 := source228 hβ h227
 exact h228
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0225_0228
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0229_0232
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0229_0232

theorem source229 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3896545457911664578554531500000000000000000000000000000/3923387504858105740630417832382417712774864239932446797:ℝ) (1000000000000000000000000000000/421093872422836041500511890073:ℝ) (1/10:ℝ)) :
 GlobalSource (324516813992518272976269625000000000000000000000000000/326788703475618919558508580244180477573251703321504599:ℝ) (250000000000000000000000000000/105380916979649762548454093169:ℝ) (1/10:ℝ) := by
 have heps : 0<p229.toReal.eps := by norm_num [p229,Params.toReal]
 have hcap : p229.toReal.cap=1/10 := by norm_num [p229,Params.toReal]
 have hi : GlobalSource (p229.toReal.state (((cells229 0).2:ℝ)/(p229.den:ℝ))).B (p229.toReal.state (((cells229 0).2:ℝ)/(p229.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p229,cells229,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells229 0).1 < (cells229 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p229) hw0 heps hcap (commonSigns229 0) (highSigns229 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns229 0)
   (u:=((cells229 0).1:ℝ)/(p229.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p229.toReal.state (((cells229 0).1:ℝ)/(p229.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(105380916979649762548454093169/250000000000000000000000000000:ℝ)) (by norm_num [p229,cells229,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p229,cells229,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source230 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (324516813992518272976269625000000000000000000000000000/326788703475618919558508580244180477573251703321504599:ℝ) (250000000000000000000000000000/105380916979649762548454093169:ℝ) (1/10:ℝ)) :
 GlobalSource (3891858077908773972875939500000000000000000000000000000/3919544012648578233236248528554060178699456153035438957:ℝ) (1000000000000000000000000000000/421955048274658856223399170361:ℝ) (1/10:ℝ) := by
 have heps : 0<p230.toReal.eps := by norm_num [p230,Params.toReal]
 have hcap : p230.toReal.cap=1/10 := by norm_num [p230,Params.toReal]
 have hi : GlobalSource (p230.toReal.state (((cells230 0).2:ℝ)/(p230.den:ℝ))).B (p230.toReal.state (((cells230 0).2:ℝ)/(p230.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p230,cells230,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells230 0).1 < (cells230 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p230) hw0 heps hcap (commonSigns230 0) (highSigns230 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns230 0)
   (u:=((cells230 0).1:ℝ)/(p230.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p230.toReal.state (((cells230 0).1:ℝ)/(p230.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(421955048274658856223399170361/1000000000000000000000000000000:ℝ)) (by norm_num [p230,cells230,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p230,cells230,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source231 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3891858077908773972875939500000000000000000000000000000/3919544012648578233236248528554060178699456153035438957:ℝ) (1000000000000000000000000000000/421955048274658856223399170361:ℝ) (1/10:ℝ)) :
 GlobalSource (486189298488416083754580437500000000000000000000000000/489703277624573177229748105770229479838512208856032827:ℝ) (125000000000000000000000000000/52798502632131843488172217807:ℝ) (1/10:ℝ) := by
 have heps : 0<p231.toReal.eps := by norm_num [p231,Params.toReal]
 have hcap : p231.toReal.cap=1/10 := by norm_num [p231,Params.toReal]
 have hi : GlobalSource (p231.toReal.state (((cells231 0).2:ℝ)/(p231.den:ℝ))).B (p231.toReal.state (((cells231 0).2:ℝ)/(p231.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p231,cells231,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells231 0).1 < (cells231 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p231) hw0 heps hcap (commonSigns231 0) (highSigns231 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns231 0)
   (u:=((cells231 0).1:ℝ)/(p231.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p231.toReal.state (((cells231 0).1:ℝ)/(p231.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(52798502632131843488172217807/125000000000000000000000000000:ℝ)) (by norm_num [p231,cells231,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p231,cells231,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source232 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (486189298488416083754580437500000000000000000000000000/489703277624573177229748105770229479838512208856032827:ℝ) (125000000000000000000000000000/52798502632131843488172217807:ℝ) (1/10:ℝ)) :
 GlobalSource (3048761331690888915448900000000000000000000000000000/3071145937313612624847785415406110452402818376895547:ℝ) (200000000000000000000000000000/84564518775737099245573249841:ℝ) (1/10:ℝ) := by
 have heps : 0<p232.toReal.eps := by norm_num [p232,Params.toReal]
 have hcap : p232.toReal.cap=1/10 := by norm_num [p232,Params.toReal]
 have hi : GlobalSource (p232.toReal.state (((cells232 0).2:ℝ)/(p232.den:ℝ))).B (p232.toReal.state (((cells232 0).2:ℝ)/(p232.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p232,cells232,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells232 0).1 < (cells232 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p232) hw0 heps hcap (commonSigns232 0) (highSigns232 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns232 0)
   (u:=((cells232 0).1:ℝ)/(p232.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p232.toReal.state (((cells232 0).1:ℝ)/(p232.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(84564518775737099245573249841/200000000000000000000000000000:ℝ)) (by norm_num [p232,cells232,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p232,cells232,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3896545457911664578554531500000000000000000000000000000/3923387504858105740630417832382417712774864239932446797:ℝ) (1000000000000000000000000000000/421093872422836041500511890073:ℝ) (1/10:ℝ)) :
 GlobalSource (3048761331690888915448900000000000000000000000000000/3071145937313612624847785415406110452402818376895547:ℝ) (200000000000000000000000000000/84564518775737099245573249841:ℝ) (1/10:ℝ) := by
 have h229 := source229 hβ hp
 have h230 := source230 hβ h229
 have h231 := source231 hβ h230
 have h232 := source232 hβ h231
 exact h232
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0229_0232
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0233_0236
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0233_0236

theorem source233 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3048761331690888915448900000000000000000000000000000/3071145937313612624847785415406110452402818376895547:ℝ) (200000000000000000000000000000/84564518775737099245573249841:ℝ) (1/10:ℝ)) :
 GlobalSource (776965401580887612871610300000000000000000000000000000/782759712643042646215699788426579466703693013079845597:ℝ) (200000000000000000000000000000/84651754879933868670328486633:ℝ) (1/10:ℝ) := by
 have heps : 0<p233.toReal.eps := by norm_num [p233,Params.toReal]
 have hcap : p233.toReal.cap=1/10 := by norm_num [p233,Params.toReal]
 have hi : GlobalSource (p233.toReal.state (((cells233 0).2:ℝ)/(p233.den:ℝ))).B (p233.toReal.state (((cells233 0).2:ℝ)/(p233.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p233,cells233,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells233 0).1 < (cells233 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p233) hw0 heps hcap (commonSigns233 0) (highSigns233 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns233 0)
   (u:=((cells233 0).1:ℝ)/(p233.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p233.toReal.state (((cells233 0).1:ℝ)/(p233.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(84651754879933868670328486633/200000000000000000000000000000:ℝ)) (by norm_num [p233,cells233,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p233,cells233,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source234 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (776965401580887612871610300000000000000000000000000000/782759712643042646215699788426579466703693013079845597:ℝ) (200000000000000000000000000000/84651754879933868670328486633:ℝ) (1/10:ℝ)) :
 GlobalSource (1941241658951496380759377750000000000000000000000000000/1955944351878964740595015696987016544612156150519407703:ℝ) (500000000000000000000000000000/211848285163853652285750490491:ℝ) (1/10:ℝ) := by
 have heps : 0<p234.toReal.eps := by norm_num [p234,Params.toReal]
 have hcap : p234.toReal.cap=1/10 := by norm_num [p234,Params.toReal]
 have hi : GlobalSource (p234.toReal.state (((cells234 0).2:ℝ)/(p234.den:ℝ))).B (p234.toReal.state (((cells234 0).2:ℝ)/(p234.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p234,cells234,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells234 0).1 < (cells234 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p234) hw0 heps hcap (commonSigns234 0) (highSigns234 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns234 0)
   (u:=((cells234 0).1:ℝ)/(p234.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p234.toReal.state (((cells234 0).1:ℝ)/(p234.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(211848285163853652285750490491/500000000000000000000000000000:ℝ)) (by norm_num [p234,cells234,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p234,cells234,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source235 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1941241658951496380759377750000000000000000000000000000/1955944351878964740595015696987016544612156150519407703:ℝ) (500000000000000000000000000000/211848285163853652285750490491:ℝ) (1/10:ℝ)) :
 GlobalSource (129337987596718248622648650000000000000000000000000000/130332716501725389105642971493115863186867335351674969:ℝ) (100000000000000000000000000000/42413598941844981936893465951:ℝ) (1/10:ℝ) := by
 have heps : 0<p235.toReal.eps := by norm_num [p235,Params.toReal]
 have hcap : p235.toReal.cap=1/10 := by norm_num [p235,Params.toReal]
 have hi : GlobalSource (p235.toReal.state (((cells235 0).2:ℝ)/(p235.den:ℝ))).B (p235.toReal.state (((cells235 0).2:ℝ)/(p235.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p235,cells235,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells235 0).1 < (cells235 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p235) hw0 heps hcap (commonSigns235 0) (highSigns235 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns235 0)
   (u:=((cells235 0).1:ℝ)/(p235.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p235.toReal.state (((cells235 0).1:ℝ)/(p235.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(42413598941844981936893465951/100000000000000000000000000000:ℝ)) (by norm_num [p235,cells235,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p235,cells235,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source236 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (129337987596718248622648650000000000000000000000000000/130332716501725389105642971493115863186867335351674969:ℝ) (100000000000000000000000000000/42413598941844981936893465951:ℝ) (1/10:ℝ)) :
 GlobalSource (193889796895005107792008175000000000000000000000000000/195403847022699274505017907582794738046519271997779447:ℝ) (50000000000000000000000000000/21228851973793339381314988187:ℝ) (1/10:ℝ) := by
 have heps : 0<p236.toReal.eps := by norm_num [p236,Params.toReal]
 have hcap : p236.toReal.cap=1/10 := by norm_num [p236,Params.toReal]
 have hi : GlobalSource (p236.toReal.state (((cells236 0).2:ℝ)/(p236.den:ℝ))).B (p236.toReal.state (((cells236 0).2:ℝ)/(p236.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p236,cells236,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells236 0).1 < (cells236 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p236) hw0 heps hcap (commonSigns236 0) (highSigns236 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns236 0)
   (u:=((cells236 0).1:ℝ)/(p236.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p236.toReal.state (((cells236 0).1:ℝ)/(p236.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(21228851973793339381314988187/50000000000000000000000000000:ℝ)) (by norm_num [p236,cells236,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p236,cells236,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3048761331690888915448900000000000000000000000000000/3071145937313612624847785415406110452402818376895547:ℝ) (200000000000000000000000000000/84564518775737099245573249841:ℝ) (1/10:ℝ)) :
 GlobalSource (193889796895005107792008175000000000000000000000000000/195403847022699274505017907582794738046519271997779447:ℝ) (50000000000000000000000000000/21228851973793339381314988187:ℝ) (1/10:ℝ) := by
 have h233 := source233 hβ hp
 have h234 := source234 hβ h233
 have h235 := source235 hβ h234
 have h236 := source236 hβ h235
 exact h236
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0233_0236
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0237_0240
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0237_0240

theorem source237 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (193889796895005107792008175000000000000000000000000000/195403847022699274505017907582794738046519271997779447:ℝ) (50000000000000000000000000000/21228851973793339381314988187:ℝ) (1/10:ℝ)) :
 GlobalSource (775090449579731370600173500000000000000000000000000000/781235008666086077820765254180373518192831273287489383:ℝ) (1000000000000000000000000000000/425019728352621027518277465463:ℝ) (1/10:ℝ) := by
 have heps : 0<p237.toReal.eps := by norm_num [p237,Params.toReal]
 have hcap : p237.toReal.cap=1/10 := by norm_num [p237,Params.toReal]
 have hi : GlobalSource (p237.toReal.state (((cells237 0).2:ℝ)/(p237.den:ℝ))).B (p237.toReal.state (((cells237 0).2:ℝ)/(p237.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p237,cells237,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells237 0).1 < (cells237 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p237) hw0 heps hcap (commonSigns237 0) (highSigns237 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns237 0)
   (u:=((cells237 0).1:ℝ)/(p237.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p237.toReal.state (((cells237 0).1:ℝ)/(p237.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(425019728352621027518277465463/1000000000000000000000000000000:ℝ)) (by norm_num [p237,cells237,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p237,cells237,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source238 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (775090449579731370600173500000000000000000000000000000/781235008666086077820765254180373518192831273287489383:ℝ) (1000000000000000000000000000000/425019728352621027518277465463:ℝ) (1/10:ℝ)) :
 GlobalSource (322759046491434295846797625000000000000000000000000000/325356317254626228919589121356710357680295548981345121:ℝ) (250000000000000000000000000000/106366015987611298012083469847:ℝ) (1/10:ℝ) := by
 have heps : 0<p238.toReal.eps := by norm_num [p238,Params.toReal]
 have hcap : p238.toReal.cap=1/10 := by norm_num [p238,Params.toReal]
 have hi : GlobalSource (p238.toReal.state (((cells238 0).2:ℝ)/(p238.den:ℝ))).B (p238.toReal.state (((cells238 0).2:ℝ)/(p238.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p238,cells238,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells238 0).1 < (cells238 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p238) hw0 heps hcap (commonSigns238 0) (highSigns238 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns238 0)
   (u:=((cells238 0).1:ℝ)/(p238.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p238.toReal.state (((cells238 0).1:ℝ)/(p238.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(106366015987611298012083469847/250000000000000000000000000000:ℝ)) (by norm_num [p238,cells238,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p238,cells238,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source239 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (322759046491434295846797625000000000000000000000000000/325356317254626228919589121356710357680295548981345121:ℝ) (250000000000000000000000000000/106366015987611298012083469847:ℝ) (1/10:ℝ)) :
 GlobalSource (1935382433947883123661137750000000000000000000000000000/1951189617506140618618078981281922545616244275617811803:ℝ) (500000000000000000000000000000/212955027110261090828053565551:ℝ) (1/10:ℝ) := by
 have heps : 0<p239.toReal.eps := by norm_num [p239,Params.toReal]
 have hcap : p239.toReal.cap=1/10 := by norm_num [p239,Params.toReal]
 have hi : GlobalSource (p239.toReal.state (((cells239 0).2:ℝ)/(p239.den:ℝ))).B (p239.toReal.state (((cells239 0).2:ℝ)/(p239.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p239,cells239,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells239 0).1 < (cells239 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p239) hw0 heps hcap (commonSigns239 0) (highSigns239 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns239 0)
   (u:=((cells239 0).1:ℝ)/(p239.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p239.toReal.state (((cells239 0).1:ℝ)/(p239.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(212955027110261090828053565551/500000000000000000000000000000:ℝ)) (by norm_num [p239,cells239,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p239,cells239,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source240 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1935382433947883123661137750000000000000000000000000000/1951189617506140618618078981281922545616244275617811803:ℝ) (500000000000000000000000000000/212955027110261090828053565551:ℝ) (1/10:ℝ)) :
 GlobalSource (1934210588947160472241489750000000000000000000000000000/1950242665296216219921736746945402570886102730593845249:ℝ) (500000000000000000000000000000/213178853581934545393154605437:ℝ) (1/10:ℝ) := by
 have heps : 0<p240.toReal.eps := by norm_num [p240,Params.toReal]
 have hcap : p240.toReal.cap=1/10 := by norm_num [p240,Params.toReal]
 have hi : GlobalSource (p240.toReal.state (((cells240 0).2:ℝ)/(p240.den:ℝ))).B (p240.toReal.state (((cells240 0).2:ℝ)/(p240.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p240,cells240,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells240 0).1 < (cells240 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p240) hw0 heps hcap (commonSigns240 0) (highSigns240 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns240 0)
   (u:=((cells240 0).1:ℝ)/(p240.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p240.toReal.state (((cells240 0).1:ℝ)/(p240.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(213178853581934545393154605437/500000000000000000000000000000:ℝ)) (by norm_num [p240,cells240,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p240,cells240,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (193889796895005107792008175000000000000000000000000000/195403847022699274505017907582794738046519271997779447:ℝ) (50000000000000000000000000000/21228851973793339381314988187:ℝ) (1/10:ℝ)) :
 GlobalSource (1934210588947160472241489750000000000000000000000000000/1950242665296216219921736746945402570886102730593845249:ℝ) (500000000000000000000000000000/213178853581934545393154605437:ℝ) (1/10:ℝ) := by
 have h237 := source237 hβ hp
 have h238 := source238 hβ h237
 have h239 := source239 hβ h238
 have h240 := source240 hβ h239
 exact h240
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0237_0240
