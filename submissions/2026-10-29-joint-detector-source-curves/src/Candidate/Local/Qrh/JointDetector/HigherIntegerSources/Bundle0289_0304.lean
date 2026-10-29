/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0289_0292
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0293_0296
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0297_0300
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0301_0304
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0289_0292
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0289_0292

theorem source289 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1877962028912473204098385750000000000000000000000000000/1906391891716621904073478894254594790163589461893785747:ℝ) (500000000000000000000000000000/224985356016195713267221062343:ℝ) (1/10:ℝ)) :
 GlobalSource (78199590996322939694947406250000000000000000000000000/79396352877554735122857857261687593054784837663720657:ℝ) (62500000000000000000000000000/28156924386082703100751860007:ℝ) (1/10:ℝ) := by
 have heps : 0<p289.toReal.eps := by norm_num [p289,Params.toReal]
 have hcap : p289.toReal.cap=1/10 := by norm_num [p289,Params.toReal]
 have hi : GlobalSource (p289.toReal.state (((cells289 0).2:ℝ)/(p289.den:ℝ))).B (p289.toReal.state (((cells289 0).2:ℝ)/(p289.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p289,cells289,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells289 0).1 < (cells289 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p289) hw0 heps hcap (commonSigns289 0) (highSigns289 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns289 0)
   (u:=((cells289 0).1:ℝ)/(p289.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p289.toReal.state (((cells289 0).1:ℝ)/(p289.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(28156924386082703100751860007/62500000000000000000000000000:ℝ)) (by norm_num [p289,cells289,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p289,cells289,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source290 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (78199590996322939694947406250000000000000000000000000/79396352877554735122857857261687593054784837663720657:ℝ) (62500000000000000000000000000/28156924386082703100751860007:ℝ) (1/10:ℝ)) :
 GlobalSource (937809169455513950629544875000000000000000000000000000/952317235481655032002522492731545759596926003434772003:ℝ) (250000000000000000000000000000/112763251060001520229750166039:ℝ) (1/10:ℝ) := by
 have heps : 0<p290.toReal.eps := by norm_num [p290,Params.toReal]
 have hcap : p290.toReal.cap=1/10 := by norm_num [p290,Params.toReal]
 have hi : GlobalSource (p290.toReal.state (((cells290 0).2:ℝ)/(p290.den:ℝ))).B (p290.toReal.state (((cells290 0).2:ℝ)/(p290.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p290,cells290,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells290 0).1 < (cells290 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p290) hw0 heps hcap (commonSigns290 0) (highSigns290 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns290 0)
   (u:=((cells290 0).1:ℝ)/(p290.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p290.toReal.state (((cells290 0).1:ℝ)/(p290.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(112763251060001520229750166039/250000000000000000000000000000:ℝ)) (by norm_num [p290,cells290,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p290,cells290,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source291 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (937809169455513950629544875000000000000000000000000000/952317235481655032002522492731545759596926003434772003:ℝ) (250000000000000000000000000000/112763251060001520229750166039:ℝ) (1/10:ℝ)) :
 GlobalSource (1874446493910305249839441750000000000000000000000000000/1903757899366119390063210462320029948961507380985448081:ℝ) (500000000000000000000000000000/225798682684369551784262456781:ℝ) (1/10:ℝ) := by
 have heps : 0<p291.toReal.eps := by norm_num [p291,Params.toReal]
 have hcap : p291.toReal.cap=1/10 := by norm_num [p291,Params.toReal]
 have hi : GlobalSource (p291.toReal.state (((cells291 0).2:ℝ)/(p291.den:ℝ))).B (p291.toReal.state (((cells291 0).2:ℝ)/(p291.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p291,cells291,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells291 0).1 < (cells291 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p291) hw0 heps hcap (commonSigns291 0) (highSigns291 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns291 0)
   (u:=((cells291 0).1:ℝ)/(p291.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p291.toReal.state (((cells291 0).1:ℝ)/(p291.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(225798682684369551784262456781/500000000000000000000000000000:ℝ)) (by norm_num [p291,cells291,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p291,cells291,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source292 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1874446493910305249839441750000000000000000000000000000/1903757899366119390063210462320029948961507380985448081:ℝ) (500000000000000000000000000000/225798682684369551784262456781:ℝ) (1/10:ℝ)) :
 GlobalSource (24976995318794434645597250000000000000000000000000000/25371770082916089652110663011680183495928803774361099:ℝ) (500000000000000000000000000000/226071942393808916452855569877:ℝ) (1/10:ℝ) := by
 have heps : 0<p292.toReal.eps := by norm_num [p292,Params.toReal]
 have hcap : p292.toReal.cap=1/10 := by norm_num [p292,Params.toReal]
 have hi : GlobalSource (p292.toReal.state (((cells292 0).2:ℝ)/(p292.den:ℝ))).B (p292.toReal.state (((cells292 0).2:ℝ)/(p292.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p292,cells292,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells292 0).1 < (cells292 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p292) hw0 heps hcap (commonSigns292 0) (highSigns292 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns292 0)
   (u:=((cells292 0).1:ℝ)/(p292.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p292.toReal.state (((cells292 0).1:ℝ)/(p292.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(226071942393808916452855569877/500000000000000000000000000000:ℝ)) (by norm_num [p292,cells292,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p292,cells292,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1877962028912473204098385750000000000000000000000000000/1906391891716621904073478894254594790163589461893785747:ℝ) (500000000000000000000000000000/224985356016195713267221062343:ℝ) (1/10:ℝ)) :
 GlobalSource (24976995318794434645597250000000000000000000000000000/25371770082916089652110663011680183495928803774361099:ℝ) (500000000000000000000000000000/226071942393808916452855569877:ℝ) (1/10:ℝ) := by
 have h289 := source289 hβ hp
 have h290 := source290 hβ h289
 have h291 := source291 hβ h290
 have h292 := source292 hβ h291
 exact h292
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0289_0292
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0293_0296
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0293_0296

theorem source293 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24976995318794434645597250000000000000000000000000000/25371770082916089652110663011680183495928803774361099:ℝ) (500000000000000000000000000000/226071942393808916452855569877:ℝ) (1/10:ℝ)) :
 GlobalSource (9360514019544299735000728750000000000000000000000000/9510045217377602944951377865138250920648665802835709:ℝ) (2500000000000000000000000000/1131731434492936598719420041:ℝ) (1/10:ℝ) := by
 have heps : 0<p293.toReal.eps := by norm_num [p293,Params.toReal]
 have hcap : p293.toReal.cap=1/10 := by norm_num [p293,Params.toReal]
 have hi : GlobalSource (p293.toReal.state (((cells293 0).2:ℝ)/(p293.den:ℝ))).B (p293.toReal.state (((cells293 0).2:ℝ)/(p293.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p293,cells293,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells293 0).1 < (cells293 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p293) hw0 heps hcap (commonSigns293 0) (highSigns293 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns293 0)
   (u:=((cells293 0).1:ℝ)/(p293.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p293.toReal.state (((cells293 0).1:ℝ)/(p293.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(1131731434492936598719420041/2500000000000000000000000000:ℝ)) (by norm_num [p293,cells293,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p293,cells293,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source294 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (9360514019544299735000728750000000000000000000000000/9510045217377602944951377865138250920648665802835709:ℝ) (2500000000000000000000000000/1131731434492936598719420041:ℝ) (1/10:ℝ)) :
 GlobalSource (3741861917816274591160995500000000000000000000000000000/3802273526193039406303178120273834199454164605257268367:ℝ) (1000000000000000000000000000000/453243443775025769691294138579:ℝ) (1/10:ℝ) := by
 have heps : 0<p294.toReal.eps := by norm_num [p294,Params.toReal]
 have hcap : p294.toReal.cap=1/10 := by norm_num [p294,Params.toReal]
 have hi : GlobalSource (p294.toReal.state (((cells294 0).2:ℝ)/(p294.den:ℝ))).B (p294.toReal.state (((cells294 0).2:ℝ)/(p294.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p294,cells294,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells294 0).1 < (cells294 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p294) hw0 heps hcap (commonSigns294 0) (highSigns294 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns294 0)
   (u:=((cells294 0).1:ℝ)/(p294.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p294.toReal.state (((cells294 0).1:ℝ)/(p294.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(453243443775025769691294138579/1000000000000000000000000000000:ℝ)) (by norm_num [p294,cells294,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p294,cells294,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source295 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3741861917816274591160995500000000000000000000000000000/3802273526193039406303178120273834199454164605257268367:ℝ) (1000000000000000000000000000000/453243443775025769691294138579:ℝ) (1/10:ℝ)) :
 GlobalSource (178072296562610918491509500000000000000000000000000000/180977706385447617996117322249585443060441926195539323:ℝ) (1000000000000000000000000000000/453796506176524941170469249339:ℝ) (1/10:ℝ) := by
 have heps : 0<p295.toReal.eps := by norm_num [p295,Params.toReal]
 have hcap : p295.toReal.cap=1/10 := by norm_num [p295,Params.toReal]
 have hi : GlobalSource (p295.toReal.state (((cells295 0).2:ℝ)/(p295.den:ℝ))).B (p295.toReal.state (((cells295 0).2:ℝ)/(p295.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p295,cells295,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells295 0).1 < (cells295 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p295) hw0 heps hcap (commonSigns295 0) (highSigns295 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns295 0)
   (u:=((cells295 0).1:ℝ)/(p295.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p295.toReal.state (((cells295 0).1:ℝ)/(p295.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(453796506176524941170469249339/1000000000000000000000000000000:ℝ)) (by norm_num [p295,cells295,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p295,cells295,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source296 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (178072296562610918491509500000000000000000000000000000/180977706385447617996117322249585443060441926195539323:ℝ) (1000000000000000000000000000000/453796506176524941170469249339:ℝ) (1/10:ℝ)) :
 GlobalSource (1868587268906691992741201750000000000000000000000000000/1899396507298621824297773961734367699086839004747994531:ℝ) (500000000000000000000000000000/227175886267711795724080853911:ℝ) (1/10:ℝ) := by
 have heps : 0<p296.toReal.eps := by norm_num [p296,Params.toReal]
 have hcap : p296.toReal.cap=1/10 := by norm_num [p296,Params.toReal]
 have hi : GlobalSource (p296.toReal.state (((cells296 0).2:ℝ)/(p296.den:ℝ))).B (p296.toReal.state (((cells296 0).2:ℝ)/(p296.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p296,cells296,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells296 0).1 < (cells296 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p296) hw0 heps hcap (commonSigns296 0) (highSigns296 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns296 0)
   (u:=((cells296 0).1:ℝ)/(p296.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p296.toReal.state (((cells296 0).1:ℝ)/(p296.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(227175886267711795724080853911/500000000000000000000000000000:ℝ)) (by norm_num [p296,cells296,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p296,cells296,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24976995318794434645597250000000000000000000000000000/25371770082916089652110663011680183495928803774361099:ℝ) (500000000000000000000000000000/226071942393808916452855569877:ℝ) (1/10:ℝ)) :
 GlobalSource (1868587268906691992741201750000000000000000000000000000/1899396507298621824297773961734367699086839004747994531:ℝ) (500000000000000000000000000000/227175886267711795724080853911:ℝ) (1/10:ℝ) := by
 have h293 := source293 hβ hp
 have h294 := source294 hβ h293
 have h295 := source295 hβ h294
 have h296 := source296 hβ h295
 exact h296
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0293_0296
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0297_0300
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0297_0300

theorem source297 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1868587268906691992741201750000000000000000000000000000/1899396507298621824297773961734367699086839004747994531:ℝ) (500000000000000000000000000000/227175886267711795724080853911:ℝ) (1/10:ℝ)) :
 GlobalSource (8119197495243344962267625000000000000000000000000000/8254471894901902334619657399821499685369056705286239:ℝ) (250000000000000000000000000000/113727313616134464749198844793:ℝ) (1/10:ℝ) := by
 have heps : 0<p297.toReal.eps := by norm_num [p297,Params.toReal]
 have hcap : p297.toReal.cap=1/10 := by norm_num [p297,Params.toReal]
 have hi : GlobalSource (p297.toReal.state (((cells297 0).2:ℝ)/(p297.den:ℝ))).B (p297.toReal.state (((cells297 0).2:ℝ)/(p297.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p297,cells297,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells297 0).1 < (cells297 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p297) hw0 heps hcap (commonSigns297 0) (highSigns297 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns297 0)
   (u:=((cells297 0).1:ℝ)/(p297.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p297.toReal.state (((cells297 0).1:ℝ)/(p297.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(113727313616134464749198844793/250000000000000000000000000000:ℝ)) (by norm_num [p297,cells297,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p297,cells297,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source298 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (8119197495243344962267625000000000000000000000000000/8254471894901902334619657399821499685369056705286239:ℝ) (250000000000000000000000000000/113727313616134464749198844793:ℝ) (1/10:ℝ)) :
 GlobalSource (414720795312277042200423500000000000000000000000000000/421702667692426477128160246426161598033421732528031033:ℝ) (1000000000000000000000000000000/455468963656422377257531430013:ℝ) (1/10:ℝ) := by
 have heps : 0<p298.toReal.eps := by norm_num [p298,Params.toReal]
 have hcap : p298.toReal.cap=1/10 := by norm_num [p298,Params.toReal]
 have hi : GlobalSource (p298.toReal.state (((cells298 0).2:ℝ)/(p298.den:ℝ))).B (p298.toReal.state (((cells298 0).2:ℝ)/(p298.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p298,cells298,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells298 0).1 < (cells298 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p298) hw0 heps hcap (commonSigns298 0) (highSigns298 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns298 0)
   (u:=((cells298 0).1:ℝ)/(p298.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p298.toReal.state (((cells298 0).1:ℝ)/(p298.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(455468963656422377257531430013/1000000000000000000000000000000:ℝ)) (by norm_num [p298,cells298,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p298,cells298,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source299 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (414720795312277042200423500000000000000000000000000000/421702667692426477128160246426161598033421732528031033:ℝ) (1000000000000000000000000000000/455468963656422377257531430013:ℝ) (1/10:ℝ)) :
 GlobalSource (1865071733904524038482257750000000000000000000000000000/1896796915651986361243943999845775167905170348435556837:ℝ) (500000000000000000000000000000/228015455942025481577610349009:ℝ) (1/10:ℝ) := by
 have heps : 0<p299.toReal.eps := by norm_num [p299,Params.toReal]
 have hcap : p299.toReal.cap=1/10 := by norm_num [p299,Params.toReal]
 have hi : GlobalSource (p299.toReal.state (((cells299 0).2:ℝ)/(p299.den:ℝ))).B (p299.toReal.state (((cells299 0).2:ℝ)/(p299.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p299,cells299,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells299 0).1 < (cells299 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p299) hw0 heps hcap (commonSigns299 0) (highSigns299 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns299 0)
   (u:=((cells299 0).1:ℝ)/(p299.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p299.toReal.state (((cells299 0).1:ℝ)/(p299.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(228015455942025481577610349009/500000000000000000000000000000:ℝ)) (by norm_num [p299,cells299,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p299,cells299,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source300 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1865071733904524038482257750000000000000000000000000000/1896796915651986361243943999845775167905170348435556837:ℝ) (500000000000000000000000000000/228015455942025481577610349009:ℝ) (1/10:ℝ)) :
 GlobalSource (3426286560484929020335679687500000000000000000000000/3485171453914034600067012412145215959868303968453669:ℝ) (15625000000000000000000000000/7134298609398504418640321569:ℝ) (1/10:ℝ) := by
 have heps : 0<p300.toReal.eps := by norm_num [p300,Params.toReal]
 have hcap : p300.toReal.cap=1/10 := by norm_num [p300,Params.toReal]
 have hi : GlobalSource (p300.toReal.state (((cells300 0).2:ℝ)/(p300.den:ℝ))).B (p300.toReal.state (((cells300 0).2:ℝ)/(p300.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p300,cells300,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells300 0).1 < (cells300 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p300) hw0 heps hcap (commonSigns300 0) (highSigns300 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns300 0)
   (u:=((cells300 0).1:ℝ)/(p300.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p300.toReal.state (((cells300 0).1:ℝ)/(p300.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(7134298609398504418640321569/15625000000000000000000000000:ℝ)) (by norm_num [p300,cells300,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p300,cells300,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1868587268906691992741201750000000000000000000000000000/1899396507298621824297773961734367699086839004747994531:ℝ) (500000000000000000000000000000/227175886267711795724080853911:ℝ) (1/10:ℝ)) :
 GlobalSource (3426286560484929020335679687500000000000000000000000/3485171453914034600067012412145215959868303968453669:ℝ) (15625000000000000000000000000/7134298609398504418640321569:ℝ) (1/10:ℝ) := by
 have h297 := source297 hβ hp
 have h298 := source298 hβ h297
 have h299 := source299 hβ h298
 have h300 := source300 hβ h299
 exact h300
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0297_0300
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0301_0304
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0301_0304

theorem source301 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3426286560484929020335679687500000000000000000000000/3485171453914034600067012412145215959868303968453669:ℝ) (15625000000000000000000000000/7134298609398504418640321569:ℝ) (1/10:ℝ)) :
 GlobalSource (248363739187077164752394900000000000000000000000000000/252676142992928615961686238042716298083944273477868753:ℝ) (200000000000000000000000000000/91432314588932915630892693799:ℝ) (1/10:ℝ) := by
 have heps : 0<p301.toReal.eps := by norm_num [p301,Params.toReal]
 have hcap : p301.toReal.cap=1/10 := by norm_num [p301,Params.toReal]
 have hi : GlobalSource (p301.toReal.state (((cells301 0).2:ℝ)/(p301.den:ℝ))).B (p301.toReal.state (((cells301 0).2:ℝ)/(p301.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p301,cells301,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells301 0).1 < (cells301 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p301) hw0 heps hcap (commonSigns301 0) (highSigns301 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns301 0)
   (u:=((cells301 0).1:ℝ)/(p301.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p301.toReal.state (((cells301 0).1:ℝ)/(p301.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(91432314588932915630892693799/200000000000000000000000000000:ℝ)) (by norm_num [p301,cells301,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p301,cells301,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source302 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (248363739187077164752394900000000000000000000000000000/252676142992928615961686238042716298083944273477868753:ℝ) (200000000000000000000000000000/91432314588932915630892693799:ℝ) (1/10:ℝ)) :
 GlobalSource (372311239780471216844662750000000000000000000000000000/378842064442041812390304408463724342425300387426239369:ℝ) (500000000000000000000000000000/228865154865958769902117514873:ℝ) (1/10:ℝ) := by
 have heps : 0<p302.toReal.eps := by norm_num [p302,Params.toReal]
 have hcap : p302.toReal.cap=1/10 := by norm_num [p302,Params.toReal]
 have hi : GlobalSource (p302.toReal.state (((cells302 0).2:ℝ)/(p302.den:ℝ))).B (p302.toReal.state (((cells302 0).2:ℝ)/(p302.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p302,cells302,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells302 0).1 < (cells302 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p302) hw0 heps hcap (commonSigns302 0) (highSigns302 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns302 0)
   (u:=((cells302 0).1:ℝ)/(p302.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p302.toReal.state (((cells302 0).1:ℝ)/(p302.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(228865154865958769902117514873/500000000000000000000000000000:ℝ)) (by norm_num [p302,cells302,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p302,cells302,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source303 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (372311239780471216844662750000000000000000000000000000/378842064442041812390304408463724342425300387426239369:ℝ) (500000000000000000000000000000/228865154865958769902117514873:ℝ) (1/10:ℝ)) :
 GlobalSource (132365500000000000000000000000000000/134691681706757286391944389662954587:ℝ) (1000000000000000000000000000000/457834420624410799685731440459:ℝ) (1/10:ℝ) := by
 have heps : 0<p303.toReal.eps := by norm_num [p303,Params.toReal]
 have hcap : p303.toReal.cap=1/10 := by norm_num [p303,Params.toReal]
 have hi : GlobalSource (p303.toReal.state (((cells303 0).2:ℝ)/(p303.den:ℝ))).B (p303.toReal.state (((cells303 0).2:ℝ)/(p303.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p303,cells303,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells303 0).1 < (cells303 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p303) hw0 heps hcap (commonSigns303 0) (highSigns303 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns303 0)
   (u:=((cells303 0).1:ℝ)/(p303.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p303.toReal.state (((cells303 0).1:ℝ)/(p303.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(457834420624410799685731440459/1000000000000000000000000000000:ℝ)) (by norm_num [p303,cells303,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p303,cells303,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source304 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (132365500000000000000000000000000000/134691681706757286391944389662954587:ℝ) (1000000000000000000000000000000/457834420624410799685731440459:ℝ) (1/10:ℝ)) :
 GlobalSource (24802906250000000000000000000000000/25243236227959016986755807395199093:ℝ) (62500000000000000000000000000/28650366457444811403694569267:ℝ) (1/10:ℝ) := by
 have heps : 0<p304.toReal.eps := by norm_num [p304,Params.toReal]
 have hcap : p304.toReal.cap=1/10 := by norm_num [p304,Params.toReal]
 have hi : GlobalSource (p304.toReal.state (((cells304 0).2:ℝ)/(p304.den:ℝ))).B (p304.toReal.state (((cells304 0).2:ℝ)/(p304.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p304,cells304,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells304 0).1 < (cells304 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p304) hw0 heps hcap (commonSigns304 0) (highSigns304 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns304 0)
   (u:=((cells304 0).1:ℝ)/(p304.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p304.toReal.state (((cells304 0).1:ℝ)/(p304.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(28650366457444811403694569267/62500000000000000000000000000:ℝ)) (by norm_num [p304,cells304,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p304,cells304,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem prefix0303 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3426286560484929020335679687500000000000000000000000/3485171453914034600067012412145215959868303968453669:ℝ) (15625000000000000000000000000/7134298609398504418640321569:ℝ) (1/10:ℝ)) :
 GlobalSource (132365500000000000000000000000000000/134691681706757286391944389662954587:ℝ) (1000000000000000000000000000000/457834420624410799685731440459:ℝ) (1/10:ℝ) := by
 have h301 := source301 hβ hp
 have h302 := source302 hβ h301
 have h303 := source303 hβ h302
 exact h303

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3426286560484929020335679687500000000000000000000000/3485171453914034600067012412145215959868303968453669:ℝ) (15625000000000000000000000000/7134298609398504418640321569:ℝ) (1/10:ℝ)) :
 GlobalSource (24802906250000000000000000000000000/25243236227959016986755807395199093:ℝ) (62500000000000000000000000000/28650366457444811403694569267:ℝ) (1/10:ℝ) := by
 have h301 := source301 hβ hp
 have h302 := source302 hβ h301
 have h303 := source303 hβ h302
 have h304 := source304 hβ h303
 exact h304
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0301_0304
