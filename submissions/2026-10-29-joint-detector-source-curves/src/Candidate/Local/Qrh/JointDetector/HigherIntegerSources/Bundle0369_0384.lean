/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0369_0372
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0373_0376
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0377_0380
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0381_0384
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0369_0372
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0369_0372

theorem source369 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (190423250000000000000000000000000000/196413576346749754754208100812485763:ℝ) (500000000000000000000000000000/250183199839442597183478478997:ℝ) (1/10:ℝ)) :
 GlobalSource (42288500000000000000000000000000000/43629443167318306396344216139529117:ℝ) (1000000000000000000000000000000/501117294498531427676211263007:ℝ) (1/10:ℝ) := by
 have heps : 0<p369.toReal.eps := by norm_num [p369,Params.toReal]
 have hcap : p369.toReal.cap=1/10 := by norm_num [p369,Params.toReal]
 have hi : GlobalSource (p369.toReal.state (((cells369 0).2:ℝ)/(p369.den:ℝ))).B (p369.toReal.state (((cells369 0).2:ℝ)/(p369.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p369,cells369,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells369 0).1 < (cells369 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p369) hw0 heps hcap (commonSigns369 0) (highSigns369 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns369 0)
   (u:=((cells369 0).1:ℝ)/(p369.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p369.toReal.state (((cells369 0).1:ℝ)/(p369.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(501117294498531427676211263007/1000000000000000000000000000000:ℝ)) (by norm_num [p369,cells369,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p369,cells369,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source370 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (42288500000000000000000000000000000/43629443167318306396344216139529117:ℝ) (1000000000000000000000000000000/501117294498531427676211263007:ℝ) (1/10:ℝ)) :
 GlobalSource (47543312500000000000000000000000000/49062895652095943307189309414783399:ℝ) (125000000000000000000000000000/62733938198181952599659765081:ℝ) (1/10:ℝ) := by
 have heps : 0<p370.toReal.eps := by norm_num [p370,Params.toReal]
 have hcap : p370.toReal.cap=1/10 := by norm_num [p370,Params.toReal]
 have hi : GlobalSource (p370.toReal.state (((cells370 0).2:ℝ)/(p370.den:ℝ))).B (p370.toReal.state (((cells370 0).2:ℝ)/(p370.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p370,cells370,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells370 0).1 < (cells370 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p370) hw0 heps hcap (commonSigns370 0) (highSigns370 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns370 0)
   (u:=((cells370 0).1:ℝ)/(p370.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p370.toReal.state (((cells370 0).1:ℝ)/(p370.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(62733938198181952599659765081/125000000000000000000000000000:ℝ)) (by norm_num [p370,cells370,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p370,cells370,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source371 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (47543312500000000000000000000000000/49062895652095943307189309414783399:ℝ) (125000000000000000000000000000/62733938198181952599659765081:ℝ) (1/10:ℝ)) :
 GlobalSource (76019300000000000000000000000000000/78468336671250648053577021505077609:ℝ) (200000000000000000000000000000/100525810547363749285564973571:ℝ) (1/10:ℝ) := by
 have heps : 0<p371.toReal.eps := by norm_num [p371,Params.toReal]
 have hcap : p371.toReal.cap=1/10 := by norm_num [p371,Params.toReal]
 have hi : GlobalSource (p371.toReal.state (((cells371 0).2:ℝ)/(p371.den:ℝ))).B (p371.toReal.state (((cells371 0).2:ℝ)/(p371.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p371,cells371,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells371 0).1 < (cells371 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p371) hw0 heps hcap (commonSigns371 0) (highSigns371 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns371 0)
   (u:=((cells371 0).1:ℝ)/(p371.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p371.toReal.state (((cells371 0).1:ℝ)/(p371.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(100525810547363749285564973571/200000000000000000000000000000:ℝ)) (by norm_num [p371,cells371,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p371,cells371,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source372 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (76019300000000000000000000000000000/78468336671250648053577021505077609:ℝ) (200000000000000000000000000000/100525810547363749285564973571:ℝ) (1/10:ℝ)) :
 GlobalSource (63307750000000000000000000000000000/65363423909373074838653780467952909:ℝ) (500000000000000000000000000000/251694977952324763619557633313:ℝ) (1/10:ℝ) := by
 have heps : 0<p372.toReal.eps := by norm_num [p372,Params.toReal]
 have hcap : p372.toReal.cap=1/10 := by norm_num [p372,Params.toReal]
 have hi : GlobalSource (p372.toReal.state (((cells372 0).2:ℝ)/(p372.den:ℝ))).B (p372.toReal.state (((cells372 0).2:ℝ)/(p372.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p372,cells372,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells372 0).1 < (cells372 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p372) hw0 heps hcap (commonSigns372 0) (highSigns372 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns372 0)
   (u:=((cells372 0).1:ℝ)/(p372.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p372.toReal.state (((cells372 0).1:ℝ)/(p372.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(251694977952324763619557633313/500000000000000000000000000000:ℝ)) (by norm_num [p372,cells372,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p372,cells372,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (190423250000000000000000000000000000/196413576346749754754208100812485763:ℝ) (500000000000000000000000000000/250183199839442597183478478997:ℝ) (1/10:ℝ)) :
 GlobalSource (63307750000000000000000000000000000/65363423909373074838653780467952909:ℝ) (500000000000000000000000000000/251694977952324763619557633313:ℝ) (1/10:ℝ) := by
 have h369 := source369 hβ hp
 have h370 := source370 hβ h369
 have h371 := source371 hβ h370
 have h372 := source372 hβ h371
 exact h372
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0369_0372
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0373_0376
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0373_0376

theorem source373 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (63307750000000000000000000000000000/65363423909373074838653780467952909:ℝ) (500000000000000000000000000000/251694977952324763619557633313:ℝ) (1/10:ℝ)) :
 GlobalSource (189798250000000000000000000000000000/196009873025262862184698860315684501:ℝ) (500000000000000000000000000000/252077117598678542224904299519:ℝ) (1/10:ℝ) := by
 have heps : 0<p373.toReal.eps := by norm_num [p373,Params.toReal]
 have hcap : p373.toReal.cap=1/10 := by norm_num [p373,Params.toReal]
 have hi : GlobalSource (p373.toReal.state (((cells373 0).2:ℝ)/(p373.den:ℝ))).B (p373.toReal.state (((cells373 0).2:ℝ)/(p373.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p373,cells373,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells373 0).1 < (cells373 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p373) hw0 heps hcap (commonSigns373 0) (highSigns373 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns373 0)
   (u:=((cells373 0).1:ℝ)/(p373.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p373.toReal.state (((cells373 0).1:ℝ)/(p373.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(252077117598678542224904299519/500000000000000000000000000000:ℝ)) (by norm_num [p373,cells373,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p373,cells373,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source374 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (189798250000000000000000000000000000/196009873025262862184698860315684501:ℝ) (500000000000000000000000000000/252077117598678542224904299519:ℝ) (1/10:ℝ)) :
 GlobalSource (189673250000000000000000000000000000/195929645837409253113903202699850391:ℝ) (500000000000000000000000000000/252460955440630725884740087929:ℝ) (1/10:ℝ) := by
 have heps : 0<p374.toReal.eps := by norm_num [p374,Params.toReal]
 have hcap : p374.toReal.cap=1/10 := by norm_num [p374,Params.toReal]
 have hi : GlobalSource (p374.toReal.state (((cells374 0).2:ℝ)/(p374.den:ℝ))).B (p374.toReal.state (((cells374 0).2:ℝ)/(p374.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p374,cells374,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells374 0).1 < (cells374 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p374) hw0 heps hcap (commonSigns374 0) (highSigns374 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns374 0)
   (u:=((cells374 0).1:ℝ)/(p374.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p374.toReal.state (((cells374 0).1:ℝ)/(p374.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(252460955440630725884740087929/500000000000000000000000000000:ℝ)) (by norm_num [p374,cells374,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p374,cells374,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source375 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (189673250000000000000000000000000000/195929645837409253113903202699850391:ℝ) (500000000000000000000000000000/252460955440630725884740087929:ℝ) (1/10:ℝ)) :
 GlobalSource (126365500000000000000000000000000000/130566393622245442541445477648716481:ℝ) (1000000000000000000000000000000/505693003382142205797389850417:ℝ) (1/10:ℝ) := by
 have heps : 0<p375.toReal.eps := by norm_num [p375,Params.toReal]
 have hcap : p375.toReal.cap=1/10 := by norm_num [p375,Params.toReal]
 have hi : GlobalSource (p375.toReal.state (((cells375 0).2:ℝ)/(p375.den:ℝ))).B (p375.toReal.state (((cells375 0).2:ℝ)/(p375.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p375,cells375,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells375 0).1 < (cells375 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p375) hw0 heps hcap (commonSigns375 0) (highSigns375 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns375 0)
   (u:=((cells375 0).1:ℝ)/(p375.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p375.toReal.state (((cells375 0).1:ℝ)/(p375.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(505693003382142205797389850417/1000000000000000000000000000000:ℝ)) (by norm_num [p375,cells375,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p375,cells375,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source376 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (126365500000000000000000000000000000/130566393622245442541445477648716481:ℝ) (1000000000000000000000000000000/505693003382142205797389850417:ℝ) (1/10:ℝ)) :
 GlobalSource (11838953125000000000000000000000000/12235606692682196391589856826573963:ℝ) (31250000000000000000000000000/15827110415212670880453170797:ℝ) (1/10:ℝ) := by
 have heps : 0<p376.toReal.eps := by norm_num [p376,Params.toReal]
 have hcap : p376.toReal.cap=1/10 := by norm_num [p376,Params.toReal]
 have hi : GlobalSource (p376.toReal.state (((cells376 0).2:ℝ)/(p376.den:ℝ))).B (p376.toReal.state (((cells376 0).2:ℝ)/(p376.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p376,cells376,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells376 0).1 < (cells376 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p376) hw0 heps hcap (commonSigns376 0) (highSigns376 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns376 0)
   (u:=((cells376 0).1:ℝ)/(p376.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p376.toReal.state (((cells376 0).1:ℝ)/(p376.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(15827110415212670880453170797/31250000000000000000000000000:ℝ)) (by norm_num [p376,cells376,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p376,cells376,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (63307750000000000000000000000000000/65363423909373074838653780467952909:ℝ) (500000000000000000000000000000/251694977952324763619557633313:ℝ) (1/10:ℝ)) :
 GlobalSource (11838953125000000000000000000000000/12235606692682196391589856826573963:ℝ) (31250000000000000000000000000/15827110415212670880453170797:ℝ) (1/10:ℝ) := by
 have h373 := source373 hβ hp
 have h374 := source374 hβ h373
 have h375 := source375 hβ h374
 have h376 := source376 hβ h375
 exact h376
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0373_0376
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0377_0380
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0377_0380

theorem source377 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (11838953125000000000000000000000000/12235606692682196391589856826573963:ℝ) (31250000000000000000000000000/15827110415212670880453170797:ℝ) (1/10:ℝ)) :
 GlobalSource (23662281250000000000000000000000000/24461249507099923643656273703594241:ℝ) (62500000000000000000000000000/31702845084041846192880150579:ℝ) (1/10:ℝ) := by
 have heps : 0<p377.toReal.eps := by norm_num [p377,Params.toReal]
 have hcap : p377.toReal.cap=1/10 := by norm_num [p377,Params.toReal]
 have hi : GlobalSource (p377.toReal.state (((cells377 0).2:ℝ)/(p377.den:ℝ))).B (p377.toReal.state (((cells377 0).2:ℝ)/(p377.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p377,cells377,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells377 0).1 < (cells377 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p377) hw0 heps hcap (commonSigns377 0) (highSigns377 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns377 0)
   (u:=((cells377 0).1:ℝ)/(p377.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p377.toReal.state (((cells377 0).1:ℝ)/(p377.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(31702845084041846192880150579/62500000000000000000000000000:ℝ)) (by norm_num [p377,cells377,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p377,cells377,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source378 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (23662281250000000000000000000000000/24461249507099923643656273703594241:ℝ) (62500000000000000000000000000/31702845084041846192880150579:ℝ) (1/10:ℝ)) :
 GlobalSource (18016500000000000000000000000000000/18629567393023978013438390722947571:ℝ) (1000000000000000000000000000000/508026988469369426100706817329:ℝ) (1/10:ℝ) := by
 have heps : 0<p378.toReal.eps := by norm_num [p378,Params.toReal]
 have hcap : p378.toReal.cap=1/10 := by norm_num [p378,Params.toReal]
 have hi : GlobalSource (p378.toReal.state (((cells378 0).2:ℝ)/(p378.den:ℝ))).B (p378.toReal.state (((cells378 0).2:ℝ)/(p378.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p378,cells378,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells378 0).1 < (cells378 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p378) hw0 heps hcap (commonSigns378 0) (highSigns378 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns378 0)
   (u:=((cells378 0).1:ℝ)/(p378.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p378.toReal.state (((cells378 0).1:ℝ)/(p378.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(508026988469369426100706817329/1000000000000000000000000000000:ℝ)) (by norm_num [p378,cells378,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p378,cells378,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source379 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (18016500000000000000000000000000000/18629567393023978013438390722947571:ℝ) (1000000000000000000000000000000/508026988469369426100706817329:ℝ) (1/10:ℝ)) :
 GlobalSource (378096500000000000000000000000000000/391062184130985932602084233862366383:ℝ) (1000000000000000000000000000000/508811955740380536811549930277:ℝ) (1/10:ℝ) := by
 have heps : 0<p379.toReal.eps := by norm_num [p379,Params.toReal]
 have hcap : p379.toReal.cap=1/10 := by norm_num [p379,Params.toReal]
 have hi : GlobalSource (p379.toReal.state (((cells379 0).2:ℝ)/(p379.den:ℝ))).B (p379.toReal.state (((cells379 0).2:ℝ)/(p379.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p379,cells379,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells379 0).1 < (cells379 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p379) hw0 heps hcap (commonSigns379 0) (highSigns379 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns379 0)
   (u:=((cells379 0).1:ℝ)/(p379.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p379.toReal.state (((cells379 0).1:ℝ)/(p379.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(508811955740380536811549930277/1000000000000000000000000000000:ℝ)) (by norm_num [p379,cells379,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p379,cells379,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source380 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (378096500000000000000000000000000000/391062184130985932602084233862366383:ℝ) (1000000000000000000000000000000/508811955740380536811549930277:ℝ) (1/10:ℝ)) :
 GlobalSource (9446162500000000000000000000000000/9772594982337089381607114414719499:ℝ) (25000000000000000000000000000/12740011110116545207999585981:ℝ) (1/10:ℝ) := by
 have heps : 0<p380.toReal.eps := by norm_num [p380,Params.toReal]
 have hcap : p380.toReal.cap=1/10 := by norm_num [p380,Params.toReal]
 have hi : GlobalSource (p380.toReal.state (((cells380 0).2:ℝ)/(p380.den:ℝ))).B (p380.toReal.state (((cells380 0).2:ℝ)/(p380.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p380,cells380,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells380 0).1 < (cells380 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p380) hw0 heps hcap (commonSigns380 0) (highSigns380 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns380 0)
   (u:=((cells380 0).1:ℝ)/(p380.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p380.toReal.state (((cells380 0).1:ℝ)/(p380.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(12740011110116545207999585981/25000000000000000000000000000:ℝ)) (by norm_num [p380,cells380,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p380,cells380,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (11838953125000000000000000000000000/12235606692682196391589856826573963:ℝ) (31250000000000000000000000000/15827110415212670880453170797:ℝ) (1/10:ℝ)) :
 GlobalSource (9446162500000000000000000000000000/9772594982337089381607114414719499:ℝ) (25000000000000000000000000000/12740011110116545207999585981:ℝ) (1/10:ℝ) := by
 have h377 := source377 hβ hp
 have h378 := source378 hβ h377
 have h379 := source379 hβ h378
 have h380 := source380 hβ h379
 exact h380
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0377_0380
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0381_0384
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0381_0384

theorem source381 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (9446162500000000000000000000000000/9772594982337089381607114414719499:ℝ) (25000000000000000000000000000/12740011110116545207999585981:ℝ) (1/10:ℝ)) :
 GlobalSource (62932750000000000000000000000000000/65124293548407873027408688910756827:ℝ) (500000000000000000000000000000/255196237939159275636121245139:ℝ) (1/10:ℝ) := by
 have heps : 0<p381.toReal.eps := by norm_num [p381,Params.toReal]
 have hcap : p381.toReal.cap=1/10 := by norm_num [p381,Params.toReal]
 have hi : GlobalSource (p381.toReal.state (((cells381 0).2:ℝ)/(p381.den:ℝ))).B (p381.toReal.state (((cells381 0).2:ℝ)/(p381.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p381,cells381,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells381 0).1 < (cells381 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p381) hw0 heps hcap (commonSigns381 0) (highSigns381 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns381 0)
   (u:=((cells381 0).1:ℝ)/(p381.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p381.toReal.state (((cells381 0).1:ℝ)/(p381.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(255196237939159275636121245139/500000000000000000000000000000:ℝ)) (by norm_num [p381,cells381,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p381,cells381,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source382 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (62932750000000000000000000000000000/65124293548407873027408688910756827:ℝ) (500000000000000000000000000000/255196237939159275636121245139:ℝ) (1/10:ℝ)) :
 GlobalSource (377346500000000000000000000000000000/390588070673358076808511399108333939:ℝ) (1000000000000000000000000000000/511188071748285290930010377341:ℝ) (1/10:ℝ) := by
 have heps : 0<p382.toReal.eps := by norm_num [p382,Params.toReal]
 have hcap : p382.toReal.cap=1/10 := by norm_num [p382,Params.toReal]
 have hi : GlobalSource (p382.toReal.state (((cells382 0).2:ℝ)/(p382.den:ℝ))).B (p382.toReal.state (((cells382 0).2:ℝ)/(p382.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p382,cells382,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells382 0).1 < (cells382 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p382) hw0 heps hcap (commonSigns382 0) (highSigns382 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns382 0)
   (u:=((cells382 0).1:ℝ)/(p382.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p382.toReal.state (((cells382 0).1:ℝ)/(p382.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(511188071748285290930010377341/1000000000000000000000000000000:ℝ)) (by norm_num [p382,cells382,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p382,cells382,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source383 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (377346500000000000000000000000000000/390588070673358076808511399108333939:ℝ) (1000000000000000000000000000000/511188071748285290930010377341:ℝ) (1/10:ℝ)) :
 GlobalSource (18854825000000000000000000000000000/19521536399787258945565840204563141:ℝ) (50000000000000000000000000000/25599362688701444631396668679:ℝ) (1/10:ℝ) := by
 have heps : 0<p383.toReal.eps := by norm_num [p383,Params.toReal]
 have hcap : p383.toReal.cap=1/10 := by norm_num [p383,Params.toReal]
 have hi : GlobalSource (p383.toReal.state (((cells383 0).2:ℝ)/(p383.den:ℝ))).B (p383.toReal.state (((cells383 0).2:ℝ)/(p383.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p383,cells383,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells383 0).1 < (cells383 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p383) hw0 heps hcap (commonSigns383 0) (highSigns383 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns383 0)
   (u:=((cells383 0).1:ℝ)/(p383.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p383.toReal.state (((cells383 0).1:ℝ)/(p383.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(25599362688701444631396668679/50000000000000000000000000000:ℝ)) (by norm_num [p383,cells383,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p383,cells383,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source384 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (18854825000000000000000000000000000/19521536399787258945565840204563141:ℝ) (50000000000000000000000000000/25599362688701444631396668679:ℝ) (1/10:ℝ)) :
 GlobalSource (62807750000000000000000000000000000/65045622302200574228907592881370479:ℝ) (500000000000000000000000000000/256395021944636131974108835803:ℝ) (1/10:ℝ) := by
 have heps : 0<p384.toReal.eps := by norm_num [p384,Params.toReal]
 have hcap : p384.toReal.cap=1/10 := by norm_num [p384,Params.toReal]
 have hi : GlobalSource (p384.toReal.state (((cells384 0).2:ℝ)/(p384.den:ℝ))).B (p384.toReal.state (((cells384 0).2:ℝ)/(p384.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p384,cells384,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells384 0).1 < (cells384 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p384) hw0 heps hcap (commonSigns384 0) (highSigns384 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns384 0)
   (u:=((cells384 0).1:ℝ)/(p384.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p384.toReal.state (((cells384 0).1:ℝ)/(p384.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(256395021944636131974108835803/500000000000000000000000000000:ℝ)) (by norm_num [p384,cells384,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p384,cells384,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (9446162500000000000000000000000000/9772594982337089381607114414719499:ℝ) (25000000000000000000000000000/12740011110116545207999585981:ℝ) (1/10:ℝ)) :
 GlobalSource (62807750000000000000000000000000000/65045622302200574228907592881370479:ℝ) (500000000000000000000000000000/256395021944636131974108835803:ℝ) (1/10:ℝ) := by
 have h381 := source381 hβ hp
 have h382 := source382 hβ h381
 have h383 := source383 hβ h382
 have h384 := source384 hβ h383
 exact h384
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0381_0384
