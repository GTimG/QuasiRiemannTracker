/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0417_0420
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0421_0424
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0425_0428
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0429_0432
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0417_0420
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0417_0420

theorem source417 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (738005000000000500000000000000000000000000000/771028862554244528558848245478655966673061137:ℝ) (1000000000000000000000000000000/539924835300548944198891020379:ℝ) (1/10:ℝ)) :
 GlobalSource (368752500000000250000000000000000000000000000/385367862672968203250537142863633598483352623:ℝ) (500000000000000000000000000000/270427894621844727456161117541:ℝ) (1/10:ℝ) := by
 have heps : 0<p417.toReal.eps := by norm_num [p417,Params.toReal]
 have hcap : p417.toReal.cap=1/10 := by norm_num [p417,Params.toReal]
 have hi : GlobalSource (p417.toReal.state (((cells417 0).2:ℝ)/(p417.den:ℝ))).B (p417.toReal.state (((cells417 0).2:ℝ)/(p417.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p417,cells417,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells417 0).1 < (cells417 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p417) hw0 heps hcap (commonSigns417 0) (highSigns417 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns417 0)
   (u:=((cells417 0).1:ℝ)/(p417.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p417.toReal.state (((cells417 0).1:ℝ)/(p417.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(270427894621844727456161117541/500000000000000000000000000000:ℝ)) (by norm_num [p417,cells417,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p417,cells417,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source418 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (368752500000000250000000000000000000000000000/385367862672968203250537142863633598483352623:ℝ) (500000000000000000000000000000/270427894621844727456161117541:ℝ) (1/10:ℝ)) :
 GlobalSource (10236180555555562500000000000000000000000000/10700600393050516241856838717489557945786551:ℝ) (125000000000000000000000000000/67723890169303350143837359653:ℝ) (1/10:ℝ) := by
 have heps : 0<p418.toReal.eps := by norm_num [p418,Params.toReal]
 have hcap : p418.toReal.cap=1/10 := by norm_num [p418,Params.toReal]
 have hi : GlobalSource (p418.toReal.state (((cells418 0).2:ℝ)/(p418.den:ℝ))).B (p418.toReal.state (((cells418 0).2:ℝ)/(p418.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p418,cells418,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells418 0).1 < (cells418 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p418) hw0 heps hcap (commonSigns418 0) (highSigns418 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns418 0)
   (u:=((cells418 0).1:ℝ)/(p418.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p418.toReal.state (((cells418 0).1:ℝ)/(p418.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(67723890169303350143837359653/125000000000000000000000000000:ℝ)) (by norm_num [p418,cells418,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p418,cells418,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source419 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (10236180555555562500000000000000000000000000/10700600393050516241856838717489557945786551:ℝ) (125000000000000000000000000000/67723890169303350143837359653:ℝ) (1/10:ℝ)) :
 GlobalSource (184126250000000125000000000000000000000000000/192537843168663840328734648626797026998440911:ℝ) (250000000000000000000000000000/135682715072030494972332813637:ℝ) (1/10:ℝ) := by
 have heps : 0<p419.toReal.eps := by norm_num [p419,Params.toReal]
 have hcap : p419.toReal.cap=1/10 := by norm_num [p419,Params.toReal]
 have hi : GlobalSource (p419.toReal.state (((cells419 0).2:ℝ)/(p419.den:ℝ))).B (p419.toReal.state (((cells419 0).2:ℝ)/(p419.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p419,cells419,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells419 0).1 < (cells419 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p419) hw0 heps hcap (commonSigns419 0) (highSigns419 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns419 0)
   (u:=((cells419 0).1:ℝ)/(p419.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p419.toReal.state (((cells419 0).1:ℝ)/(p419.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(135682715072030494972332813637/250000000000000000000000000000:ℝ)) (by norm_num [p419,cells419,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p419,cells419,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source420 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (184126250000000125000000000000000000000000000/192537843168663840328734648626797026998440911:ℝ) (250000000000000000000000000000/135682715072030494972332813637:ℝ) (1/10:ℝ)) :
 GlobalSource (13142946428571437500000000000000000000000000/13747502852540008565337091970737357640073309:ℝ) (125000000000000000000000000000/67959379368925697957826837721:ℝ) (1/10:ℝ) := by
 have heps : 0<p420.toReal.eps := by norm_num [p420,Params.toReal]
 have hcap : p420.toReal.cap=1/10 := by norm_num [p420,Params.toReal]
 have hi : GlobalSource (p420.toReal.state (((cells420 0).2:ℝ)/(p420.den:ℝ))).B (p420.toReal.state (((cells420 0).2:ℝ)/(p420.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p420,cells420,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells420 0).1 < (cells420 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p420) hw0 heps hcap (commonSigns420 0) (highSigns420 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns420 0)
   (u:=((cells420 0).1:ℝ)/(p420.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p420.toReal.state (((cells420 0).1:ℝ)/(p420.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(67959379368925697957826837721/125000000000000000000000000000:ℝ)) (by norm_num [p420,cells420,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p420,cells420,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem prefix0417 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (738005000000000500000000000000000000000000000/771028862554244528558848245478655966673061137:ℝ) (1000000000000000000000000000000/539924835300548944198891020379:ℝ) (1/10:ℝ)) :
 GlobalSource (368752500000000250000000000000000000000000000/385367862672968203250537142863633598483352623:ℝ) (500000000000000000000000000000/270427894621844727456161117541:ℝ) (1/10:ℝ) := by
 have h417 := source417 hβ hp
 exact h417

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (738005000000000500000000000000000000000000000/771028862554244528558848245478655966673061137:ℝ) (1000000000000000000000000000000/539924835300548944198891020379:ℝ) (1/10:ℝ)) :
 GlobalSource (13142946428571437500000000000000000000000000/13747502852540008565337091970737357640073309:ℝ) (125000000000000000000000000000/67959379368925697957826837721:ℝ) (1/10:ℝ) := by
 have h417 := source417 hβ hp
 have h418 := source418 hβ h417
 have h419 := source419 hβ h418
 have h420 := source420 hβ h419
 exact h420
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0417_0420
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0421_0424
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0421_0424

theorem source421 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (13142946428571437500000000000000000000000000/13747502852540008565337091970737357640073309:ℝ) (125000000000000000000000000000/67959379368925697957826837721:ℝ) (1/10:ℝ)) :
 GlobalSource (61292083333333375000000000000000000000000000/64130799232142129291636716325239040354536193:ℝ) (250000000000000000000000000000/136155918626232974110354536193:ℝ) (1/10:ℝ) := by
 have heps : 0<p421.toReal.eps := by norm_num [p421,Params.toReal]
 have hcap : p421.toReal.cap=1/10 := by norm_num [p421,Params.toReal]
 have hi : GlobalSource (p421.toReal.state (((cells421 0).2:ℝ)/(p421.den:ℝ))).B (p421.toReal.state (((cells421 0).2:ℝ)/(p421.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p421,cells421,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells421 0).1 < (cells421 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p421) hw0 heps hcap (commonSigns421 0) (highSigns421 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns421 0)
   (u:=((cells421 0).1:ℝ)/(p421.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p421.toReal.state (((cells421 0).1:ℝ)/(p421.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(136155918626232974110354536193/250000000000000000000000000000:ℝ)) (by norm_num [p421,cells421,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p421,cells421,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source422 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (61292083333333375000000000000000000000000000/64130799232142129291636716325239040354536193:ℝ) (250000000000000000000000000000/136155918626232974110354536193:ℝ) (1/10:ℝ)) :
 GlobalSource (735005000000000500000000000000000000000000000/769279667100551557122240574047166665926630367:ℝ) (1000000000000000000000000000000/545576808366169457665308876789:ℝ) (1/10:ℝ) := by
 have heps : 0<p422.toReal.eps := by norm_num [p422,Params.toReal]
 have hcap : p422.toReal.cap=1/10 := by norm_num [p422,Params.toReal]
 have hi : GlobalSource (p422.toReal.state (((cells422 0).2:ℝ)/(p422.den:ℝ))).B (p422.toReal.state (((cells422 0).2:ℝ)/(p422.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p422,cells422,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells422 0).1 < (cells422 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p422) hw0 heps hcap (commonSigns422 0) (highSigns422 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns422 0)
   (u:=((cells422 0).1:ℝ)/(p422.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p422.toReal.state (((cells422 0).1:ℝ)/(p422.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(545576808366169457665308876789/1000000000000000000000000000000:ℝ)) (by norm_num [p422,cells422,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p422,cells422,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source423 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (735005000000000500000000000000000000000000000/769279667100551557122240574047166665926630367:ℝ) (1000000000000000000000000000000/545576808366169457665308876789:ℝ) (1/10:ℝ)) :
 GlobalSource (734505000000000500000000000000000000000000000/768990389994593735158972487714341580164071189:ℝ) (1000000000000000000000000000000/546534466212228662896721357063:ℝ) (1/10:ℝ) := by
 have heps : 0<p423.toReal.eps := by norm_num [p423,Params.toReal]
 have hcap : p423.toReal.cap=1/10 := by norm_num [p423,Params.toReal]
 have hi : GlobalSource (p423.toReal.state (((cells423 0).2:ℝ)/(p423.den:ℝ))).B (p423.toReal.state (((cells423 0).2:ℝ)/(p423.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p423,cells423,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells423 0).1 < (cells423 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p423) hw0 heps hcap (commonSigns423 0) (highSigns423 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns423 0)
   (u:=((cells423 0).1:ℝ)/(p423.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p423.toReal.state (((cells423 0).1:ℝ)/(p423.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(546534466212228662896721357063/1000000000000000000000000000000:ℝ)) (by norm_num [p423,cells423,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p423,cells423,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source424 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (734505000000000500000000000000000000000000000/768990389994593735158972487714341580164071189:ℝ) (1000000000000000000000000000000/546534466212228662896721357063:ℝ) (1/10:ℝ)) :
 GlobalSource (1957346666666668000000000000000000000000000/2049871362101572810587569602344028580683619:ℝ) (8000000000000000000000000000/4379973423861815838580683619:ℝ) (1/10:ℝ) := by
 have heps : 0<p424.toReal.eps := by norm_num [p424,Params.toReal]
 have hcap : p424.toReal.cap=1/10 := by norm_num [p424,Params.toReal]
 have hi : GlobalSource (p424.toReal.state (((cells424 0).2:ℝ)/(p424.den:ℝ))).B (p424.toReal.state (((cells424 0).2:ℝ)/(p424.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p424,cells424,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells424 0).1 < (cells424 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p424) hw0 heps hcap (commonSigns424 0) (highSigns424 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns424 0)
   (u:=((cells424 0).1:ℝ)/(p424.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p424.toReal.state (((cells424 0).1:ℝ)/(p424.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(4379973423861815838580683619/8000000000000000000000000000:ℝ)) (by norm_num [p424,cells424,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p424,cells424,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (13142946428571437500000000000000000000000000/13747502852540008565337091970737357640073309:ℝ) (125000000000000000000000000000/67959379368925697957826837721:ℝ) (1/10:ℝ)) :
 GlobalSource (1957346666666668000000000000000000000000000/2049871362101572810587569602344028580683619:ℝ) (8000000000000000000000000000/4379973423861815838580683619:ℝ) (1/10:ℝ) := by
 have h421 := source421 hβ hp
 have h422 := source422 hβ h421
 have h423 := source423 hβ h422
 have h424 := source424 hβ h423
 exact h424
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0421_0424
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0425_0428
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0425_0428

theorem source425 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1957346666666668000000000000000000000000000/2049871362101572810587569602344028580683619:ℝ) (8000000000000000000000000000/4379973423861815838580683619:ℝ) (1/10:ℝ)) :
 GlobalSource (183376250000000125000000000000000000000000000/192103445203467533712288964652883629395200603:ℝ) (250000000000000000000000000000/137115868470673092199798400201:ℝ) (1/10:ℝ) := by
 have heps : 0<p425.toReal.eps := by norm_num [p425,Params.toReal]
 have hcap : p425.toReal.cap=1/10 := by norm_num [p425,Params.toReal]
 have hi : GlobalSource (p425.toReal.state (((cells425 0).2:ℝ)/(p425.den:ℝ))).B (p425.toReal.state (((cells425 0).2:ℝ)/(p425.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p425,cells425,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells425 0).1 < (cells425 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p425) hw0 heps hcap (commonSigns425 0) (highSigns425 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns425 0)
   (u:=((cells425 0).1:ℝ)/(p425.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p425.toReal.state (((cells425 0).1:ℝ)/(p425.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(137115868470673092199798400201/250000000000000000000000000000:ℝ)) (by norm_num [p425,cells425,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p425,cells425,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source426 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (183376250000000125000000000000000000000000000/192103445203467533712288964652883629395200603:ℝ) (250000000000000000000000000000/137115868470673092199798400201:ℝ) (1/10:ℝ)) :
 GlobalSource (733005000000000500000000000000000000000000000/768126451417469913406691133007922199534938073:ℝ) (1000000000000000000000000000000/549434884385505507823178312691:ℝ) (1/10:ℝ) := by
 have heps : 0<p426.toReal.eps := by norm_num [p426,Params.toReal]
 have hcap : p426.toReal.cap=1/10 := by norm_num [p426,Params.toReal]
 have hi : GlobalSource (p426.toReal.state (((cells426 0).2:ℝ)/(p426.den:ℝ))).B (p426.toReal.state (((cells426 0).2:ℝ)/(p426.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p426,cells426,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells426 0).1 < (cells426 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p426) hw0 heps hcap (commonSigns426 0) (highSigns426 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns426 0)
   (u:=((cells426 0).1:ℝ)/(p426.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p426.toReal.state (((cells426 0).1:ℝ)/(p426.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(549434884385505507823178312691/1000000000000000000000000000000:ℝ)) (by norm_num [p426,cells426,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p426,cells426,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source427 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (733005000000000500000000000000000000000000000/768126451417469913406691133007922199534938073:ℝ) (1000000000000000000000000000000/549434884385505507823178312691:ℝ) (1/10:ℝ)) :
 GlobalSource (40694722222222250000000000000000000000000000/42657765219847962573382911380471616749113783:ℝ) (500000000000000000000000000000/275205470117940716360247341349:ℝ) (1/10:ℝ) := by
 have heps : 0<p427.toReal.eps := by norm_num [p427,Params.toReal]
 have hcap : p427.toReal.cap=1/10 := by norm_num [p427,Params.toReal]
 have hi : GlobalSource (p427.toReal.state (((cells427 0).2:ℝ)/(p427.den:ℝ))).B (p427.toReal.state (((cells427 0).2:ℝ)/(p427.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p427,cells427,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells427 0).1 < (cells427 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p427) hw0 heps hcap (commonSigns427 0) (highSigns427 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns427 0)
   (u:=((cells427 0).1:ℝ)/(p427.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p427.toReal.state (((cells427 0).1:ℝ)/(p427.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(275205470117940716360247341349/500000000000000000000000000000:ℝ)) (by norm_num [p427,cells427,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p427,cells427,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source428 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (40694722222222250000000000000000000000000000/42657765219847962573382911380471616749113783:ℝ) (500000000000000000000000000000/275205470117940716360247341349:ℝ) (1/10:ℝ)) :
 GlobalSource (366002500000000250000000000000000000000000000/383776874902299905734847532076966412244892869:ℝ) (500000000000000000000000000000/275695836226445607240748297623:ℝ) (1/10:ℝ) := by
 have heps : 0<p428.toReal.eps := by norm_num [p428,Params.toReal]
 have hcap : p428.toReal.cap=1/10 := by norm_num [p428,Params.toReal]
 have hi : GlobalSource (p428.toReal.state (((cells428 0).2:ℝ)/(p428.den:ℝ))).B (p428.toReal.state (((cells428 0).2:ℝ)/(p428.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p428,cells428,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells428 0).1 < (cells428 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p428) hw0 heps hcap (commonSigns428 0) (highSigns428 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns428 0)
   (u:=((cells428 0).1:ℝ)/(p428.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p428.toReal.state (((cells428 0).1:ℝ)/(p428.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(275695836226445607240748297623/500000000000000000000000000000:ℝ)) (by norm_num [p428,cells428,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p428,cells428,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1957346666666668000000000000000000000000000/2049871362101572810587569602344028580683619:ℝ) (8000000000000000000000000000/4379973423861815838580683619:ℝ) (1/10:ℝ)) :
 GlobalSource (366002500000000250000000000000000000000000000/383776874902299905734847532076966412244892869:ℝ) (500000000000000000000000000000/275695836226445607240748297623:ℝ) (1/10:ℝ) := by
 have h425 := source425 hβ hp
 have h426 := source426 hβ h425
 have h427 := source427 hβ h426
 have h428 := source428 hβ h427
 exact h428
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0425_0428
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0429_0432
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0429_0432

theorem source429 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (366002500000000250000000000000000000000000000/383776874902299905734847532076966412244892869:ℝ) (500000000000000000000000000000/275695836226445607240748297623:ℝ) (1/10:ℝ)) :
 GlobalSource (731505000000000500000000000000000000000000000/767268380343942410337635218834721186818685907:ℝ) (1000000000000000000000000000000/552377112333024307038939561969:ℝ) (1/10:ℝ) := by
 have heps : 0<p429.toReal.eps := by norm_num [p429,Params.toReal]
 have hcap : p429.toReal.cap=1/10 := by norm_num [p429,Params.toReal]
 have hi : GlobalSource (p429.toReal.state (((cells429 0).2:ℝ)/(p429.den:ℝ))).B (p429.toReal.state (((cells429 0).2:ℝ)/(p429.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p429,cells429,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells429 0).1 < (cells429 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p429) hw0 heps hcap (commonSigns429 0) (highSigns429 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns429 0)
   (u:=((cells429 0).1:ℝ)/(p429.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p429.toReal.state (((cells429 0).1:ℝ)/(p429.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(552377112333024307038939561969/1000000000000000000000000000000:ℝ)) (by norm_num [p429,cells429,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p429,cells429,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source430 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (731505000000000500000000000000000000000000000/767268380343942410337635218834721186818685907:ℝ) (1000000000000000000000000000000/552377112333024307038939561969:ℝ) (1/10:ℝ)) :
 GlobalSource (121834166666666750000000000000000000000000000/127830611162168043745379381598492486280718929:ℝ) (500000000000000000000000000000/276683645726646105196280718929:ℝ) (1/10:ℝ) := by
 have heps : 0<p430.toReal.eps := by norm_num [p430,Params.toReal]
 have hcap : p430.toReal.cap=1/10 := by norm_num [p430,Params.toReal]
 have hi : GlobalSource (p430.toReal.state (((cells430 0).2:ℝ)/(p430.den:ℝ))).B (p430.toReal.state (((cells430 0).2:ℝ)/(p430.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p430,cells430,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells430 0).1 < (cells430 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p430) hw0 heps hcap (commonSigns430 0) (highSigns430 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns430 0)
   (u:=((cells430 0).1:ℝ)/(p430.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p430.toReal.state (((cells430 0).1:ℝ)/(p430.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(276683645726646105196280718929/500000000000000000000000000000:ℝ)) (by norm_num [p430,cells430,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p430,cells430,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source431 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (121834166666666750000000000000000000000000000/127830611162168043745379381598492486280718929:ℝ) (500000000000000000000000000000/276683645726646105196280718929:ℝ) (1/10:ℝ)) :
 GlobalSource (730505000000000500000000000000000000000000000/766699611102911282678954237059871473371323697:ℝ) (1000000000000000000000000000000/554362241674374105834457107899:ℝ) (1/10:ℝ) := by
 have heps : 0<p431.toReal.eps := by norm_num [p431,Params.toReal]
 have hcap : p431.toReal.cap=1/10 := by norm_num [p431,Params.toReal]
 have hi : GlobalSource (p431.toReal.state (((cells431 0).2:ℝ)/(p431.den:ℝ))).B (p431.toReal.state (((cells431 0).2:ℝ)/(p431.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p431,cells431,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells431 0).1 < (cells431 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p431) hw0 heps hcap (commonSigns431 0) (highSigns431 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns431 0)
   (u:=((cells431 0).1:ℝ)/(p431.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p431.toReal.state (((cells431 0).1:ℝ)/(p431.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(554362241674374105834457107899/1000000000000000000000000000000:ℝ)) (by norm_num [p431,cells431,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p431,cells431,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source432 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (730505000000000500000000000000000000000000000/766699611102911282678954237059871473371323697:ℝ) (1000000000000000000000000000000/554362241674374105834457107899:ℝ) (1/10:ℝ)) :
 GlobalSource (45625312500000031250000000000000000000000000/47901013384894191411174859411308084300058581:ℝ) (62500000000000000000000000000/34710124696487820758100019527:ℝ) (1/10:ℝ) := by
 have heps : 0<p432.toReal.eps := by norm_num [p432,Params.toReal]
 have hcap : p432.toReal.cap=1/10 := by norm_num [p432,Params.toReal]
 have hi : GlobalSource (p432.toReal.state (((cells432 0).2:ℝ)/(p432.den:ℝ))).B (p432.toReal.state (((cells432 0).2:ℝ)/(p432.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p432,cells432,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells432 0).1 < (cells432 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p432) hw0 heps hcap (commonSigns432 0) (highSigns432 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns432 0)
   (u:=((cells432 0).1:ℝ)/(p432.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p432.toReal.state (((cells432 0).1:ℝ)/(p432.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(34710124696487820758100019527/62500000000000000000000000000:ℝ)) (by norm_num [p432,cells432,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p432,cells432,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (366002500000000250000000000000000000000000000/383776874902299905734847532076966412244892869:ℝ) (500000000000000000000000000000/275695836226445607240748297623:ℝ) (1/10:ℝ)) :
 GlobalSource (45625312500000031250000000000000000000000000/47901013384894191411174859411308084300058581:ℝ) (62500000000000000000000000000/34710124696487820758100019527:ℝ) (1/10:ℝ) := by
 have h429 := source429 hβ hp
 have h430 := source430 hβ h429
 have h431 := source431 hβ h430
 have h432 := source432 hβ h431
 exact h432
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0429_0432
