/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0081_0084
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0085_0088
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0089_0092
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0093_0096
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0081_0084
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0081_0084

theorem source81 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24713905029120421430750000000000000000000000000000/24743487230479116889132888517929618159389814282161:ℝ) (500000000000000000000000000000/198090716778989514557058206619:ℝ) (1/10:ℝ)) :
 GlobalSource (263576840981167221452100000000000000000000000000000/263896683430833280432967078178835109059991351568139:ℝ) (200000000000000000000000000000/79253353691319441706085129153:ℝ) (1/10:ℝ) := by
 have heps : 0<p81.toReal.eps := by norm_num [p81,Params.toReal]
 have hcap : p81.toReal.cap=1/10 := by norm_num [p81,Params.toReal]
 have hi : GlobalSource (p81.toReal.state (((cells81 0).2:ℝ)/(p81.den:ℝ))).B (p81.toReal.state (((cells81 0).2:ℝ)/(p81.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p81,cells81,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells81 0).1 < (cells81 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p81) hw0 heps hcap (commonSigns81 0) (highSigns81 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns81 0)
   (u:=((cells81 0).1:ℝ)/(p81.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p81.toReal.state (((cells81 0).1:ℝ)/(p81.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(79253353691319441706085129153/200000000000000000000000000000:ℝ)) (by norm_num [p81,cells81,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p81,cells81,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source82 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (263576840981167221452100000000000000000000000000000/263896683430833280432967078178835109059991351568139:ℝ) (200000000000000000000000000000/79253353691319441706085129153:ℝ) (1/10:ℝ)) :
 GlobalSource (1976540212387874607321500000000000000000000000000000/1978971338253532197412481417554449875584975097411679:ℝ) (1000000000000000000000000000000/396352175095394521200536127751:ℝ) (1/10:ℝ) := by
 have heps : 0<p82.toReal.eps := by norm_num [p82,Params.toReal]
 have hcap : p82.toReal.cap=1/10 := by norm_num [p82,Params.toReal]
 have hi : GlobalSource (p82.toReal.state (((cells82 0).2:ℝ)/(p82.den:ℝ))).B (p82.toReal.state (((cells82 0).2:ℝ)/(p82.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p82,cells82,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells82 0).1 < (cells82 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p82) hw0 heps hcap (commonSigns82 0) (highSigns82 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns82 0)
   (u:=((cells82 0).1:ℝ)/(p82.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p82.toReal.state (((cells82 0).1:ℝ)/(p82.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(396352175095394521200536127751/1000000000000000000000000000000:ℝ)) (by norm_num [p82,cells82,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p82,cells82,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source83 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1976540212387874607321500000000000000000000000000000/1978971338253532197412481417554449875584975097411679:ℝ) (1000000000000000000000000000000/396352175095394521200536127751:ℝ) (1/10:ℝ)) :
 GlobalSource (988127058708497526876125000000000000000000000000000/989358807995287232099528020872216915956481208841691:ℝ) (250000000000000000000000000000/99109413386365781482383031433:ℝ) (1/10:ℝ) := by
 have heps : 0<p83.toReal.eps := by norm_num [p83,Params.toReal]
 have hcap : p83.toReal.cap=1/10 := by norm_num [p83,Params.toReal]
 have hi : GlobalSource (p83.toReal.state (((cells83 0).2:ℝ)/(p83.den:ℝ))).B (p83.toReal.state (((cells83 0).2:ℝ)/(p83.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p83,cells83,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells83 0).1 < (cells83 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p83) hw0 heps hcap (commonSigns83 0) (highSigns83 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns83 0)
   (u:=((cells83 0).1:ℝ)/(p83.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p83.toReal.state (((cells83 0).1:ℝ)/(p83.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(99109413386365781482383031433/250000000000000000000000000000:ℝ)) (by norm_num [p83,cells83,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p83,cells83,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source84 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (988127058708497526876125000000000000000000000000000/989358807995287232099528020872216915956481208841691:ℝ) (250000000000000000000000000000/99109413386365781482383031433:ℝ) (1/10:ℝ)) :
 GlobalSource (82332000935254812507625000000000000000000000000000/82435998288660962729834737548911684693101523787881:ℝ) (250000000000000000000000000000/99130800969502731477300883207:ℝ) (1/10:ℝ) := by
 have heps : 0<p84.toReal.eps := by norm_num [p84,Params.toReal]
 have hcap : p84.toReal.cap=1/10 := by norm_num [p84,Params.toReal]
 have hi : GlobalSource (p84.toReal.state (((cells84 0).2:ℝ)/(p84.den:ℝ))).B (p84.toReal.state (((cells84 0).2:ℝ)/(p84.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p84,cells84,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells84 0).1 < (cells84 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p84) hw0 heps hcap (commonSigns84 0) (highSigns84 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns84 0)
   (u:=((cells84 0).1:ℝ)/(p84.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p84.toReal.state (((cells84 0).1:ℝ)/(p84.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(99130800969502731477300883207/250000000000000000000000000000:ℝ)) (by norm_num [p84,cells84,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p84,cells84,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24713905029120421430750000000000000000000000000000/24743487230479116889132888517929618159389814282161:ℝ) (500000000000000000000000000000/198090716778989514557058206619:ℝ) (1/10:ℝ)) :
 GlobalSource (82332000935254812507625000000000000000000000000000/82435998288660962729834737548911684693101523787881:ℝ) (250000000000000000000000000000/99130800969502731477300883207:ℝ) (1/10:ℝ) := by
 have h81 := source81 hβ hp
 have h82 := source82 hβ h81
 have h83 := source83 hβ h82
 have h84 := source84 hβ h83
 exact h84
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0081_0084
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0085_0088
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0085_0088

theorem source85 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (82332000935254812507625000000000000000000000000000/82435998288660962729834737548911684693101523787881:ℝ) (250000000000000000000000000000/99130800969502731477300883207:ℝ) (1/10:ℝ)) :
 GlobalSource (790272770990094378645500000000000000000000000000000/791284146820389621751682673310553886842631940257381:ℝ) (1000000000000000000000000000000/396608826164361739772404368197:ℝ) (1/10:ℝ) := by
 have heps : 0<p85.toReal.eps := by norm_num [p85,Params.toReal]
 have hcap : p85.toReal.cap=1/10 := by norm_num [p85,Params.toReal]
 have hi : GlobalSource (p85.toReal.state (((cells85 0).2:ℝ)/(p85.den:ℝ))).B (p85.toReal.state (((cells85 0).2:ℝ)/(p85.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p85,cells85,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells85 0).1 < (cells85 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p85) hw0 heps hcap (commonSigns85 0) (highSigns85 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns85 0)
   (u:=((cells85 0).1:ℝ)/(p85.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p85.toReal.state (((cells85 0).1:ℝ)/(p85.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(396608826164361739772404368197/1000000000000000000000000000000:ℝ)) (by norm_num [p85,cells85,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p85,cells85,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source86 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (790272770990094378645500000000000000000000000000000/791284146820389621751682673310553886842631940257381:ℝ) (1000000000000000000000000000000/396608826164361739772404368197:ℝ) (1/10:ℝ)) :
 GlobalSource (1975395832504356393044500000000000000000000000000000/1977956840345572334931894549586737468649410727151133:ℝ) (1000000000000000000000000000000/396694520475955473050960182199:ℝ) (1/10:ℝ) := by
 have heps : 0<p86.toReal.eps := by norm_num [p86,Params.toReal]
 have hcap : p86.toReal.cap=1/10 := by norm_num [p86,Params.toReal]
 have hi : GlobalSource (p86.toReal.state (((cells86 0).2:ℝ)/(p86.den:ℝ))).B (p86.toReal.state (((cells86 0).2:ℝ)/(p86.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p86,cells86,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells86 0).1 < (cells86 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p86) hw0 heps hcap (commonSigns86 0) (highSigns86 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns86 0)
   (u:=((cells86 0).1:ℝ)/(p86.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p86.toReal.state (((cells86 0).1:ℝ)/(p86.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(396694520475955473050960182199/1000000000000000000000000000000:ℝ)) (by norm_num [p86,cells86,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p86,cells86,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source87 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1975395832504356393044500000000000000000000000000000/1977956840345572334931894549586737468649410727151133:ℝ) (1000000000000000000000000000000/396694520475955473050960182199:ℝ) (1/10:ℝ)) :
 GlobalSource (82296239063894868311468750000000000000000000000000/82404307449892163444182833986587718049701133837059:ℝ) (62500000000000000000000000000/24798767930271768126682382959:ℝ) (1/10:ℝ) := by
 have heps : 0<p87.toReal.eps := by norm_num [p87,Params.toReal]
 have hcap : p87.toReal.cap=1/10 := by norm_num [p87,Params.toReal]
 have hi : GlobalSource (p87.toReal.state (((cells87 0).2:ℝ)/(p87.den:ℝ))).B (p87.toReal.state (((cells87 0).2:ℝ)/(p87.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p87,cells87,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells87 0).1 < (cells87 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p87) hw0 heps hcap (commonSigns87 0) (highSigns87 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns87 0)
   (u:=((cells87 0).1:ℝ)/(p87.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p87.toReal.state (((cells87 0).1:ℝ)/(p87.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(24798767930271768126682382959/62500000000000000000000000000:ℝ)) (by norm_num [p87,cells87,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p87,cells87,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source88 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (82296239063894868311468750000000000000000000000000/82404307449892163444182833986587718049701133837059:ℝ) (62500000000000000000000000000/24798767930271768126682382959:ℝ) (1/10:ℝ)) :
 GlobalSource (493705910640649321476500000000000000000000000000000/494362495598083901197318456135229627846367014065653:ℝ) (1000000000000000000000000000000/396866125461212785975123753467:ℝ) (1/10:ℝ) := by
 have heps : 0<p88.toReal.eps := by norm_num [p88,Params.toReal]
 have hcap : p88.toReal.cap=1/10 := by norm_num [p88,Params.toReal]
 have hi : GlobalSource (p88.toReal.state (((cells88 0).2:ℝ)/(p88.den:ℝ))).B (p88.toReal.state (((cells88 0).2:ℝ)/(p88.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p88,cells88,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells88 0).1 < (cells88 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p88) hw0 heps hcap (commonSigns88 0) (highSigns88 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns88 0)
   (u:=((cells88 0).1:ℝ)/(p88.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p88.toReal.state (((cells88 0).1:ℝ)/(p88.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(396866125461212785975123753467/1000000000000000000000000000000:ℝ)) (by norm_num [p88,cells88,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p88,cells88,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (82332000935254812507625000000000000000000000000000/82435998288660962729834737548911684693101523787881:ℝ) (250000000000000000000000000000/99130800969502731477300883207:ℝ) (1/10:ℝ)) :
 GlobalSource (493705910640649321476500000000000000000000000000000/494362495598083901197318456135229627846367014065653:ℝ) (1000000000000000000000000000000/396866125461212785975123753467:ℝ) (1/10:ℝ) := by
 have h85 := source85 hβ hp
 have h86 := source86 hβ h85
 have h87 := source87 hβ h86
 have h88 := source88 hβ h87
 exact h88
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0085_0088
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0089_0092
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0089_0092

theorem source89 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (493705910640649321476500000000000000000000000000000/494362495598083901197318456135229627846367014065653:ℝ) (1000000000000000000000000000000/396866125461212785975123753467:ℝ) (1/10:ℝ)) :
 GlobalSource (1974537547591717732336750000000000000000000000000000/1977196651116274841037995317677842898601208226445149:ℝ) (500000000000000000000000000000/198476018139169079917239125589:ℝ) (1/10:ℝ) := by
 have heps : 0<p89.toReal.eps := by norm_num [p89,Params.toReal]
 have hcap : p89.toReal.cap=1/10 := by norm_num [p89,Params.toReal]
 have hi : GlobalSource (p89.toReal.state (((cells89 0).2:ℝ)/(p89.den:ℝ))).B (p89.toReal.state (((cells89 0).2:ℝ)/(p89.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p89,cells89,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells89 0).1 < (cells89 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p89) hw0 heps hcap (commonSigns89 0) (highSigns89 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns89 0)
   (u:=((cells89 0).1:ℝ)/(p89.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p89.toReal.state (((cells89 0).1:ℝ)/(p89.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(198476018139169079917239125589/500000000000000000000000000000:ℝ)) (by norm_num [p89,cells89,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p89,cells89,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source90 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1974537547591717732336750000000000000000000000000000/1977196651116274841037995317677842898601208226445149:ℝ) (500000000000000000000000000000/198476018139169079917239125589:ℝ) (1/10:ℝ)) :
 GlobalSource (5264670540322235143380000000000000000000000000000/5271849026547332331917094985963583376933442275487:ℝ) (40000000000000000000000000000/15881520776305215490189519541:ℝ) (1/10:ℝ) := by
 have heps : 0<p90.toReal.eps := by norm_num [p90,Params.toReal]
 have hcap : p90.toReal.cap=1/10 := by norm_num [p90,Params.toReal]
 have hi : GlobalSource (p90.toReal.state (((cells90 0).2:ℝ)/(p90.den:ℝ))).B (p90.toReal.state (((cells90 0).2:ℝ)/(p90.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p90,cells90,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells90 0).1 < (cells90 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p90) hw0 heps hcap (commonSigns90 0) (highSigns90 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns90 0)
   (u:=((cells90 0).1:ℝ)/(p90.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p90.toReal.state (((cells90 0).1:ℝ)/(p90.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(15881520776305215490189519541/40000000000000000000000000000:ℝ)) (by norm_num [p90,cells90,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p90,cells90,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source91 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (5264670540322235143380000000000000000000000000000/5271849026547332331917094985963583376933442275487:ℝ) (40000000000000000000000000000/15881520776305215490189519541:ℝ) (1/10:ℝ)) :
 GlobalSource (3947930715299917250396500000000000000000000000000000/3953380367790736685320991724002827375675231573413711:ℝ) (1000000000000000000000000000000/397124074921112394066703517709:ℝ) (1/10:ℝ) := by
 have heps : 0<p91.toReal.eps := by norm_num [p91,Params.toReal]
 have hcap : p91.toReal.cap=1/10 := by norm_num [p91,Params.toReal]
 have hi : GlobalSource (p91.toReal.state (((cells91 0).2:ℝ)/(p91.den:ℝ))).B (p91.toReal.state (((cells91 0).2:ℝ)/(p91.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p91,cells91,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells91 0).1 < (cells91 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p91) hw0 heps hcap (commonSigns91 0) (highSigns91 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns91 0)
   (u:=((cells91 0).1:ℝ)/(p91.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p91.toReal.state (((cells91 0).1:ℝ)/(p91.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(397124074921112394066703517709/1000000000000000000000000000000:ℝ)) (by norm_num [p91,cells91,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p91,cells91,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source92 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3947930715299917250396500000000000000000000000000000/3953380367790736685320991724002827375675231573413711:ℝ) (1000000000000000000000000000000/397124074921112394066703517709:ℝ) (1/10:ℝ)) :
 GlobalSource (986839631339539535814500000000000000000000000000000/988218523961413819545138912342405978081425312478651:ℝ) (1000000000000000000000000000000/397210202890924230153625082773:ℝ) (1/10:ℝ) := by
 have heps : 0<p92.toReal.eps := by norm_num [p92,Params.toReal]
 have hcap : p92.toReal.cap=1/10 := by norm_num [p92,Params.toReal]
 have hi : GlobalSource (p92.toReal.state (((cells92 0).2:ℝ)/(p92.den:ℝ))).B (p92.toReal.state (((cells92 0).2:ℝ)/(p92.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p92,cells92,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells92 0).1 < (cells92 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p92) hw0 heps hcap (commonSigns92 0) (highSigns92 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns92 0)
   (u:=((cells92 0).1:ℝ)/(p92.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p92.toReal.state (((cells92 0).1:ℝ)/(p92.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(397210202890924230153625082773/1000000000000000000000000000000:ℝ)) (by norm_num [p92,cells92,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p92,cells92,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (493705910640649321476500000000000000000000000000000/494362495598083901197318456135229627846367014065653:ℝ) (1000000000000000000000000000000/396866125461212785975123753467:ℝ) (1/10:ℝ)) :
 GlobalSource (986839631339539535814500000000000000000000000000000/988218523961413819545138912342405978081425312478651:ℝ) (1000000000000000000000000000000/397210202890924230153625082773:ℝ) (1/10:ℝ) := by
 have h89 := source89 hβ hp
 have h90 := source90 hβ h89
 have h91 := source91 hβ h90
 have h92 := source92 hβ h91
 exact h92
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0089_0092
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0093_0096
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0093_0096

theorem source93 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (986839631339539535814500000000000000000000000000000/988218523961413819545138912342405978081425312478651:ℝ) (1000000000000000000000000000000/397210202890924230153625082773:ℝ) (1/10:ℝ)) :
 GlobalSource (164449430642349959838312500000000000000000000000000/164681998085326022892332104020904274801438383494059:ℝ) (125000000000000000000000000000/49662050423665405465108921381:ℝ) (1/10:ℝ) := by
 have heps : 0<p93.toReal.eps := by norm_num [p93,Params.toReal]
 have hcap : p93.toReal.cap=1/10 := by norm_num [p93,Params.toReal]
 have hi : GlobalSource (p93.toReal.state (((cells93 0).2:ℝ)/(p93.den:ℝ))).B (p93.toReal.state (((cells93 0).2:ℝ)/(p93.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p93,cells93,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells93 0).1 < (cells93 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p93) hw0 heps hcap (commonSigns93 0) (highSigns93 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns93 0)
   (u:=((cells93 0).1:ℝ)/(p93.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p93.toReal.state (((cells93 0).1:ℝ)/(p93.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(49662050423665405465108921381/125000000000000000000000000000:ℝ)) (by norm_num [p93,cells93,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p93,cells93,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source94 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (164449430642349959838312500000000000000000000000000/164681998085326022892332104020904274801438383494059:ℝ) (125000000000000000000000000000/49662050423665405465108921381:ℝ) (1/10:ℝ)) :
 GlobalSource (37944366783409999317125000000000000000000000000000/37998672522788365188909514286953383952621221595449:ℝ) (250000000000000000000000000000/99345669122171063997459344459:ℝ) (1/10:ℝ) := by
 have heps : 0<p94.toReal.eps := by norm_num [p94,Params.toReal]
 have hcap : p94.toReal.cap=1/10 := by norm_num [p94,Params.toReal]
 have hi : GlobalSource (p94.toReal.state (((cells94 0).2:ℝ)/(p94.den:ℝ))).B (p94.toReal.state (((cells94 0).2:ℝ)/(p94.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p94,cells94,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells94 0).1 < (cells94 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p94) hw0 heps hcap (commonSigns94 0) (highSigns94 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns94 0)
   (u:=((cells94 0).1:ℝ)/(p94.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p94.toReal.state (((cells94 0).1:ℝ)/(p94.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(99345669122171063997459344459/250000000000000000000000000000:ℝ)) (by norm_num [p94,cells94,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p94,cells94,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source95 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (37944366783409999317125000000000000000000000000000/37998672522788365188909514286953383952621221595449:ℝ) (250000000000000000000000000000/99345669122171063997459344459:ℝ) (1/10:ℝ)) :
 GlobalSource (789128391106576164368500000000000000000000000000000/790271212157014546484830402211130287410304778638259:ℝ) (1000000000000000000000000000000/397469022261499736297784381969:ℝ) (1/10:ℝ) := by
 have heps : 0<p95.toReal.eps := by norm_num [p95,Params.toReal]
 have hcap : p95.toReal.cap=1/10 := by norm_num [p95,Params.toReal]
 have hi : GlobalSource (p95.toReal.state (((cells95 0).2:ℝ)/(p95.den:ℝ))).B (p95.toReal.state (((cells95 0).2:ℝ)/(p95.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p95,cells95,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells95 0).1 < (cells95 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p95) hw0 heps hcap (commonSigns95 0) (highSigns95 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns95 0)
   (u:=((cells95 0).1:ℝ)/(p95.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p95.toReal.state (((cells95 0).1:ℝ)/(p95.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(397469022261499736297784381969/1000000000000000000000000000000:ℝ)) (by norm_num [p95,cells95,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p95,cells95,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source96 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (789128391106576164368500000000000000000000000000000/790271212157014546484830402211130287410304778638259:ℝ) (1000000000000000000000000000000/397469022261499736297784381969:ℝ) (1/10:ℝ)) :
 GlobalSource (2568404795306719866343750000000000000000000000000/2572168170095162355964623380844470495836196698533:ℝ) (1000000000000000000000000000000/397555440780379977592457133387:ℝ) (1/10:ℝ) := by
 have heps : 0<p96.toReal.eps := by norm_num [p96,Params.toReal]
 have hcap : p96.toReal.cap=1/10 := by norm_num [p96,Params.toReal]
 have hi : GlobalSource (p96.toReal.state (((cells96 0).2:ℝ)/(p96.den:ℝ))).B (p96.toReal.state (((cells96 0).2:ℝ)/(p96.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p96,cells96,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells96 0).1 < (cells96 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p96) hw0 heps hcap (commonSigns96 0) (highSigns96 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns96 0)
   (u:=((cells96 0).1:ℝ)/(p96.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p96.toReal.state (((cells96 0).1:ℝ)/(p96.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(397555440780379977592457133387/1000000000000000000000000000000:ℝ)) (by norm_num [p96,cells96,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p96,cells96,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (986839631339539535814500000000000000000000000000000/988218523961413819545138912342405978081425312478651:ℝ) (1000000000000000000000000000000/397210202890924230153625082773:ℝ) (1/10:ℝ)) :
 GlobalSource (2568404795306719866343750000000000000000000000000/2572168170095162355964623380844470495836196698533:ℝ) (1000000000000000000000000000000/397555440780379977592457133387:ℝ) (1/10:ℝ) := by
 have h93 := source93 hβ hp
 have h94 := source94 hβ h93
 have h95 := source95 hβ h94
 have h96 := source96 hβ h95
 exact h96
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0093_0096
