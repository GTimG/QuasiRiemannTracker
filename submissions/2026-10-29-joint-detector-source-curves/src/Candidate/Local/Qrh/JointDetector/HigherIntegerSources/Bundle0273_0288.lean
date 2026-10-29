/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0273_0276
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0277_0280
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0281_0284
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0285_0288
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0273_0276
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0273_0276

theorem source273 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (758684619569614250725101500000000000000000000000000000/768261931537492978182823620359308091913499420529983911:ℝ) (1000000000000000000000000000000/441611133711316701850699287479:ℝ) (1/10:ℝ)) :
 GlobalSource (473884925980828243848276437500000000000000000000000000/479938218308823455890613972336845601318720596179718071:ℝ) (125000000000000000000000000000/55264811734632476493686272859:ℝ) (1/10:ℝ) := by
 have heps : 0<p273.toReal.eps := by norm_num [p273,Params.toReal]
 have hcap : p273.toReal.cap=1/10 := by norm_num [p273,Params.toReal]
 have hi : GlobalSource (p273.toReal.state (((cells273 0).2:ℝ)/(p273.den:ℝ))).B (p273.toReal.state (((cells273 0).2:ℝ)/(p273.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p273,cells273,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells273 0).1 < (cells273 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p273) hw0 heps hcap (commonSigns273 0) (highSigns273 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns273 0)
   (u:=((cells273 0).1:ℝ)/(p273.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p273.toReal.state (((cells273 0).1:ℝ)/(p273.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(55264811734632476493686272859/125000000000000000000000000000:ℝ)) (by norm_num [p273,cells273,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p273,cells273,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source274 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (473884925980828243848276437500000000000000000000000000/479938218308823455890613972336845601318720596179718071:ℝ) (125000000000000000000000000000/55264811734632476493686272859:ℝ) (1/10:ℝ)) :
 GlobalSource (252582381189678709863127700000000000000000000000000000/255846974907914473284668586410968324421693325164825931:ℝ) (200000000000000000000000000000/88525564279488738326301211101:ℝ) (1/10:ℝ) := by
 have heps : 0<p274.toReal.eps := by norm_num [p274,Params.toReal]
 have hcap : p274.toReal.cap=1/10 := by norm_num [p274,Params.toReal]
 have hi : GlobalSource (p274.toReal.state (((cells274 0).2:ℝ)/(p274.den:ℝ))).B (p274.toReal.state (((cells274 0).2:ℝ)/(p274.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p274,cells274,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells274 0).1 < (cells274 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p274) hw0 heps hcap (commonSigns274 0) (highSigns274 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns274 0)
   (u:=((cells274 0).1:ℝ)/(p274.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p274.toReal.state (((cells274 0).1:ℝ)/(p274.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(88525564279488738326301211101/200000000000000000000000000000:ℝ)) (by norm_num [p274,cells274,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p274,cells274,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source275 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (252582381189678709863127700000000000000000000000000000/255846974907914473284668586410968324421693325164825931:ℝ) (200000000000000000000000000000/88525564279488738326301211101:ℝ) (1/10:ℝ)) :
 GlobalSource (946598006960933836276904875000000000000000000000000000/958976573212778440726632339339220728025365772713987483:ℝ) (250000000000000000000000000000/110784781572529758587887431599:ℝ) (1/10:ℝ) := by
 have heps : 0<p275.toReal.eps := by norm_num [p275,Params.toReal]
 have hcap : p275.toReal.cap=1/10 := by norm_num [p275,Params.toReal]
 have hi : GlobalSource (p275.toReal.state (((cells275 0).2:ℝ)/(p275.den:ℝ))).B (p275.toReal.state (((cells275 0).2:ℝ)/(p275.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p275,cells275,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells275 0).1 < (cells275 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p275) hw0 heps hcap (commonSigns275 0) (highSigns275 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns275 0)
   (u:=((cells275 0).1:ℝ)/(p275.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p275.toReal.state (((cells275 0).1:ℝ)/(p275.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(110784781572529758587887431599/250000000000000000000000000000:ℝ)) (by norm_num [p275,cells275,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p275,cells275,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source276 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (946598006960933836276904875000000000000000000000000000/958976573212778440726632339339220728025365772713987483:ℝ) (250000000000000000000000000000/110784781572529758587887431599:ℝ) (1/10:ℝ)) :
 GlobalSource (1892024168921145021134161750000000000000000000000000000/1917055378948580358437841422651548770053290268878113393:ℝ) (500000000000000000000000000000/221826209319554510280732297773:ℝ) (1/10:ℝ) := by
 have heps : 0<p276.toReal.eps := by norm_num [p276,Params.toReal]
 have hcap : p276.toReal.cap=1/10 := by norm_num [p276,Params.toReal]
 have hi : GlobalSource (p276.toReal.state (((cells276 0).2:ℝ)/(p276.den:ℝ))).B (p276.toReal.state (((cells276 0).2:ℝ)/(p276.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p276,cells276,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells276 0).1 < (cells276 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p276) hw0 heps hcap (commonSigns276 0) (highSigns276 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns276 0)
   (u:=((cells276 0).1:ℝ)/(p276.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p276.toReal.state (((cells276 0).1:ℝ)/(p276.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(221826209319554510280732297773/500000000000000000000000000000:ℝ)) (by norm_num [p276,cells276,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p276,cells276,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (758684619569614250725101500000000000000000000000000000/768261931537492978182823620359308091913499420529983911:ℝ) (1000000000000000000000000000000/441611133711316701850699287479:ℝ) (1/10:ℝ)) :
 GlobalSource (1892024168921145021134161750000000000000000000000000000/1917055378948580358437841422651548770053290268878113393:ℝ) (500000000000000000000000000000/221826209319554510280732297773:ℝ) (1/10:ℝ) := by
 have h273 := source273 hβ hp
 have h274 := source274 hβ h273
 have h275 := source275 hβ h274
 have h276 := source276 hβ h275
 exact h276
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0273_0276
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0277_0280
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0277_0280

theorem source277 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1892024168921145021134161750000000000000000000000000000/1917055378948580358437841422651548770053290268878113393:ℝ) (500000000000000000000000000000/221826209319554510280732297773:ℝ) (1/10:ℝ)) :
 GlobalSource (5042272863787792985905370000000000000000000000000000/5109757363328546780237438804871714831780156136255339:ℝ) (20000000000000000000000000000/8883354171907111550992368049:ℝ) (1/10:ℝ) := by
 have heps : 0<p277.toReal.eps := by norm_num [p277,Params.toReal]
 have hcap : p277.toReal.cap=1/10 := by norm_num [p277,Params.toReal]
 have hi : GlobalSource (p277.toReal.state (((cells277 0).2:ℝ)/(p277.den:ℝ))).B (p277.toReal.state (((cells277 0).2:ℝ)/(p277.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p277,cells277,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells277 0).1 < (cells277 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p277) hw0 heps hcap (commonSigns277 0) (highSigns277 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns277 0)
   (u:=((cells277 0).1:ℝ)/(p277.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p277.toReal.state (((cells277 0).1:ℝ)/(p277.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(8883354171907111550992368049/20000000000000000000000000000:ℝ)) (by norm_num [p277,cells277,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p277,cells277,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source278 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (5042272863787792985905370000000000000000000000000000/5109757363328546780237438804871714831780156136255339:ℝ) (20000000000000000000000000000/8883354171907111550992368049:ℝ) (1/10:ℝ)) :
 GlobalSource (30234887662715195492717852000000000000000000000000000/30644224723189039112719077974501428594602373202905791:ℝ) (8000000000000000000000000000/3557480051018168262231383619:ℝ) (1/10:ℝ) := by
 have heps : 0<p278.toReal.eps := by norm_num [p278,Params.toReal]
 have hcap : p278.toReal.cap=1/10 := by norm_num [p278,Params.toReal]
 have hi : GlobalSource (p278.toReal.state (((cells278 0).2:ℝ)/(p278.den:ℝ))).B (p278.toReal.state (((cells278 0).2:ℝ)/(p278.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p278,cells278,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells278 0).1 < (cells278 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p278) hw0 heps hcap (commonSigns278 0) (highSigns278 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns278 0)
   (u:=((cells278 0).1:ℝ)/(p278.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p278.toReal.state (((cells278 0).1:ℝ)/(p278.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(3557480051018168262231383619/8000000000000000000000000000:ℝ)) (by norm_num [p278,cells278,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p278,cells278,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source279 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (30234887662715195492717852000000000000000000000000000/30644224723189039112719077974501428594602373202905791:ℝ) (8000000000000000000000000000/3557480051018168262231383619:ℝ) (1/10:ℝ)) :
 GlobalSource (1888508633918977066875217750000000000000000000000000000/1914370482681925637308932868485982619016600053799787449:ℝ) (500000000000000000000000000000/222602161135647611524997861973:ℝ) (1/10:ℝ) := by
 have heps : 0<p279.toReal.eps := by norm_num [p279,Params.toReal]
 have hcap : p279.toReal.cap=1/10 := by norm_num [p279,Params.toReal]
 have hi : GlobalSource (p279.toReal.state (((cells279 0).2:ℝ)/(p279.den:ℝ))).B (p279.toReal.state (((cells279 0).2:ℝ)/(p279.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p279,cells279,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells279 0).1 < (cells279 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p279) hw0 heps hcap (commonSigns279 0) (highSigns279 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns279 0)
   (u:=((cells279 0).1:ℝ)/(p279.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p279.toReal.state (((cells279 0).1:ℝ)/(p279.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(222602161135647611524997861973/500000000000000000000000000000:ℝ)) (by norm_num [p279,cells279,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p279,cells279,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source280 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1888508633918977066875217750000000000000000000000000000/1914370482681925637308932868485982619016600053799787449:ℝ) (500000000000000000000000000000/222602161135647611524997861973:ℝ) (1/10:ℝ)) :
 GlobalSource (125822452594550294363704650000000000000000000000000000/127565221705413870683179751297042644975085291494268351:ℝ) (100000000000000000000000000000/44572566663245812264488832969:ℝ) (1/10:ℝ) := by
 have heps : 0<p280.toReal.eps := by norm_num [p280,Params.toReal]
 have hcap : p280.toReal.cap=1/10 := by norm_num [p280,Params.toReal]
 have hi : GlobalSource (p280.toReal.state (((cells280 0).2:ℝ)/(p280.den:ℝ))).B (p280.toReal.state (((cells280 0).2:ℝ)/(p280.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p280,cells280,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells280 0).1 < (cells280 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p280) hw0 heps hcap (commonSigns280 0) (highSigns280 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns280 0)
   (u:=((cells280 0).1:ℝ)/(p280.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p280.toReal.state (((cells280 0).1:ℝ)/(p280.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(44572566663245812264488832969/100000000000000000000000000000:ℝ)) (by norm_num [p280,cells280,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p280,cells280,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1892024168921145021134161750000000000000000000000000000/1917055378948580358437841422651548770053290268878113393:ℝ) (500000000000000000000000000000/221826209319554510280732297773:ℝ) (1/10:ℝ)) :
 GlobalSource (125822452594550294363704650000000000000000000000000000/127565221705413870683179751297042644975085291494268351:ℝ) (100000000000000000000000000000/44572566663245812264488832969:ℝ) (1/10:ℝ) := by
 have h277 := source277 hβ hp
 have h278 := source278 hβ h277
 have h279 := source279 hβ h278
 have h280 := source280 hβ h279
 exact h280
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0277_0280
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0281_0284
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0281_0284

theorem source281 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (125822452594550294363704650000000000000000000000000000/127565221705413870683179751297042644975085291494268351:ℝ) (100000000000000000000000000000/44572566663245812264488832969:ℝ) (1/10:ℝ)) :
 GlobalSource (1886164943917531764035921750000000000000000000000000000/1912587575787512516014489285767087486071518074246307899:ℝ) (500000000000000000000000000000/223124524942474027224091281359:ℝ) (1/10:ℝ) := by
 have heps : 0<p281.toReal.eps := by norm_num [p281,Params.toReal]
 have hcap : p281.toReal.cap=1/10 := by norm_num [p281,Params.toReal]
 have hi : GlobalSource (p281.toReal.state (((cells281 0).2:ℝ)/(p281.den:ℝ))).B (p281.toReal.state (((cells281 0).2:ℝ)/(p281.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p281,cells281,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells281 0).1 < (cells281 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p281) hw0 heps hcap (commonSigns281 0) (highSigns281 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns281 0)
   (u:=((cells281 0).1:ℝ)/(p281.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p281.toReal.state (((cells281 0).1:ℝ)/(p281.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(223124524942474027224091281359/500000000000000000000000000000:ℝ)) (by norm_num [p281,cells281,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p281,cells281,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source282 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1886164943917531764035921750000000000000000000000000000/1912587575787512516014489285767087486071518074246307899:ℝ) (500000000000000000000000000000/223124524942474027224091281359:ℝ) (1/10:ℝ)) :
 GlobalSource (188499309891680911261627375000000000000000000000000000/191169823519639286310753034697562389798800677298903809:ℝ) (250000000000000000000000000000/111693620630671387224100852337:ℝ) (1/10:ℝ) := by
 have heps : 0<p282.toReal.eps := by norm_num [p282,Params.toReal]
 have hcap : p282.toReal.cap=1/10 := by norm_num [p282,Params.toReal]
 have hi : GlobalSource (p282.toReal.state (((cells282 0).2:ℝ)/(p282.den:ℝ))).B (p282.toReal.state (((cells282 0).2:ℝ)/(p282.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p282,cells282,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells282 0).1 < (cells282 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p282) hw0 heps hcap (commonSigns282 0) (highSigns282 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns282 0)
   (u:=((cells282 0).1:ℝ)/(p282.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p282.toReal.state (((cells282 0).1:ℝ)/(p282.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(111693620630671387224100852337/250000000000000000000000000000:ℝ)) (by norm_num [p282,cells282,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p282,cells282,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source283 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (188499309891680911261627375000000000000000000000000000/191169823519639286310753034697562389798800677298903809:ℝ) (250000000000000000000000000000/111693620630671387224100852337:ℝ) (1/10:ℝ)) :
 GlobalSource (627940417972028820398875250000000000000000000000000000/636936768569543635609966550553223219210189770117874767:ℝ) (500000000000000000000000000000/223650987554951458236920188089:ℝ) (1/10:ℝ) := by
 have heps : 0<p283.toReal.eps := by norm_num [p283,Params.toReal]
 have hcap : p283.toReal.cap=1/10 := by norm_num [p283,Params.toReal]
 have hi : GlobalSource (p283.toReal.state (((cells283 0).2:ℝ)/(p283.den:ℝ))).B (p283.toReal.state (((cells283 0).2:ℝ)/(p283.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p283,cells283,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells283 0).1 < (cells283 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p283) hw0 heps hcap (commonSigns283 0) (highSigns283 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns283 0)
   (u:=((cells283 0).1:ℝ)/(p283.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p283.toReal.state (((cells283 0).1:ℝ)/(p283.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(223650987554951458236920188089/500000000000000000000000000000:ℝ)) (by norm_num [p283,cells283,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p283,cells283,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source284 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (627940417972028820398875250000000000000000000000000000/636936768569543635609966550553223219210189770117874767:ℝ) (500000000000000000000000000000/223650987554951458236920188089:ℝ) (1/10:ℝ)) :
 GlobalSource (941324704457681904888488875000000000000000000000000000/954961894615130495737686385223423764966924939829776551:ℝ) (250000000000000000000000000000/111957884570432400088307140747:ℝ) (1/10:ℝ) := by
 have heps : 0<p284.toReal.eps := by norm_num [p284,Params.toReal]
 have hcap : p284.toReal.cap=1/10 := by norm_num [p284,Params.toReal]
 have hi : GlobalSource (p284.toReal.state (((cells284 0).2:ℝ)/(p284.den:ℝ))).B (p284.toReal.state (((cells284 0).2:ℝ)/(p284.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p284,cells284,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells284 0).1 < (cells284 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p284) hw0 heps hcap (commonSigns284 0) (highSigns284 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns284 0)
   (u:=((cells284 0).1:ℝ)/(p284.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p284.toReal.state (((cells284 0).1:ℝ)/(p284.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(111957884570432400088307140747/250000000000000000000000000000:ℝ)) (by norm_num [p284,cells284,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p284,cells284,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (125822452594550294363704650000000000000000000000000000/127565221705413870683179751297042644975085291494268351:ℝ) (100000000000000000000000000000/44572566663245812264488832969:ℝ) (1/10:ℝ)) :
 GlobalSource (941324704457681904888488875000000000000000000000000000/954961894615130495737686385223423764966924939829776551:ℝ) (250000000000000000000000000000/111957884570432400088307140747:ℝ) (1/10:ℝ) := by
 have h281 := source281 hβ hp
 have h282 := source282 hβ h281
 have h283 := source283 hβ h282
 have h284 := source284 hβ h283
 exact h284
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0281_0284
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0285_0288
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0285_0288

theorem source285 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (941324704457681904888488875000000000000000000000000000/954961894615130495737686385223423764966924939829776551:ℝ) (250000000000000000000000000000/111957884570432400088307140747:ℝ) (1/10:ℝ)) :
 GlobalSource (3762955127829282316714659500000000000000000000000000000/3818077375345189593248387525903600810577088434617965257:ℝ) (1000000000000000000000000000000/448363182744783376673548356901:ℝ) (1/10:ℝ) := by
 have heps : 0<p285.toReal.eps := by norm_num [p285,Params.toReal]
 have hcap : p285.toReal.cap=1/10 := by norm_num [p285,Params.toReal]
 have hi : GlobalSource (p285.toReal.state (((cells285 0).2:ℝ)/(p285.den:ℝ))).B (p285.toReal.state (((cells285 0).2:ℝ)/(p285.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p285,cells285,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells285 0).1 < (cells285 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p285) hw0 heps hcap (commonSigns285 0) (highSigns285 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns285 0)
   (u:=((cells285 0).1:ℝ)/(p285.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p285.toReal.state (((cells285 0).1:ℝ)/(p285.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(448363182744783376673548356901/1000000000000000000000000000000:ℝ)) (by norm_num [p285,cells285,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p285,cells285,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source286 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3762955127829282316714659500000000000000000000000000000/3818077375345189593248387525903600810577088434617965257:ℝ) (1000000000000000000000000000000/448363182744783376673548356901:ℝ) (1/10:ℝ)) :
 GlobalSource (1253537145942612337958454500000000000000000000000000000/1272103335301497560329314393386103355404678553792975683:ℝ) (1000000000000000000000000000000/448896919277767470854691233829:ℝ) (1/10:ℝ) := by
 have heps : 0<p286.toReal.eps := by norm_num [p286,Params.toReal]
 have hcap : p286.toReal.cap=1/10 := by norm_num [p286,Params.toReal]
 have hi : GlobalSource (p286.toReal.state (((cells286 0).2:ℝ)/(p286.den:ℝ))).B (p286.toReal.state (((cells286 0).2:ℝ)/(p286.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p286,cells286,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells286 0).1 < (cells286 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p286) hw0 heps hcap (commonSigns286 0) (highSigns286 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns286 0)
   (u:=((cells286 0).1:ℝ)/(p286.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p286.toReal.state (((cells286 0).1:ℝ)/(p286.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(448896919277767470854691233829/1000000000000000000000000000000:ℝ)) (by norm_num [p286,cells286,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p286,cells286,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source287 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1253537145942612337958454500000000000000000000000000000/1272103335301497560329314393386103355404678553792975683:ℝ) (1000000000000000000000000000000/448896919277767470854691233829:ℝ) (1/10:ℝ)) :
 GlobalSource (375826774782639171103606750000000000000000000000000000/381454547398231438670741420246789739794901693175425999:ℝ) (500000000000000000000000000000/224716379366036829635073699679:ℝ) (1/10:ℝ) := by
 have heps : 0<p287.toReal.eps := by norm_num [p287,Params.toReal]
 have hcap : p287.toReal.cap=1/10 := by norm_num [p287,Params.toReal]
 have hi : GlobalSource (p287.toReal.state (((cells287 0).2:ℝ)/(p287.den:ℝ))).B (p287.toReal.state (((cells287 0).2:ℝ)/(p287.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p287,cells287,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells287 0).1 < (cells287 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p287) hw0 heps hcap (commonSigns287 0) (highSigns287 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns287 0)
   (u:=((cells287 0).1:ℝ)/(p287.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p287.toReal.state (((cells287 0).1:ℝ)/(p287.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(224716379366036829635073699679/500000000000000000000000000000:ℝ)) (by norm_num [p287,cells287,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p287,cells287,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source288 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (375826774782639171103606750000000000000000000000000000/381454547398231438670741420246789739794901693175425999:ℝ) (500000000000000000000000000000/224716379366036829635073699679:ℝ) (1/10:ℝ)) :
 GlobalSource (1877962028912473204098385750000000000000000000000000000/1906391891716621904073478894254594790163589461893785747:ℝ) (500000000000000000000000000000/224985356016195713267221062343:ℝ) (1/10:ℝ) := by
 have heps : 0<p288.toReal.eps := by norm_num [p288,Params.toReal]
 have hcap : p288.toReal.cap=1/10 := by norm_num [p288,Params.toReal]
 have hi : GlobalSource (p288.toReal.state (((cells288 0).2:ℝ)/(p288.den:ℝ))).B (p288.toReal.state (((cells288 0).2:ℝ)/(p288.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p288,cells288,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells288 0).1 < (cells288 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p288) hw0 heps hcap (commonSigns288 0) (highSigns288 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns288 0)
   (u:=((cells288 0).1:ℝ)/(p288.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p288.toReal.state (((cells288 0).1:ℝ)/(p288.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(224985356016195713267221062343/500000000000000000000000000000:ℝ)) (by norm_num [p288,cells288,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p288,cells288,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (941324704457681904888488875000000000000000000000000000/954961894615130495737686385223423764966924939829776551:ℝ) (250000000000000000000000000000/111957884570432400088307140747:ℝ) (1/10:ℝ)) :
 GlobalSource (1877962028912473204098385750000000000000000000000000000/1906391891716621904073478894254594790163589461893785747:ℝ) (500000000000000000000000000000/224985356016195713267221062343:ℝ) (1/10:ℝ) := by
 have h285 := source285 hβ hp
 have h286 := source286 hβ h285
 have h287 := source287 hβ h286
 have h288 := source288 hβ h287
 exact h288
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0285_0288
