/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0449_0452
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0453_0456
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0457_0459
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0449_0452
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0449_0452

theorem source449 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (48133666666666700000000000000000000000000000/50798179619533743896139363578581149326717909:ℝ) (200000000000000000000000000000/114407737707559806059326717909:ℝ) (1/10:ℝ)) :
 GlobalSource (144301000000000100000000000000000000000000000/152340146185327154794816045690370258824553919:ℝ) (200000000000000000000000000000/114625062026686238022941517973:ℝ) (1/10:ℝ) := by
 have heps : 0<p449.toReal.eps := by norm_num [p449,Params.toReal]
 have hcap : p449.toReal.cap=1/10 := by norm_num [p449,Params.toReal]
 have hi : GlobalSource (p449.toReal.state (((cells449 0).2:ℝ)/(p449.den:ℝ))).B (p449.toReal.state (((cells449 0).2:ℝ)/(p449.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p449,cells449,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells449 0).1 < (cells449 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p449) hw0 heps hcap (commonSigns449 0) (highSigns449 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns449 0)
   (u:=((cells449 0).1:ℝ)/(p449.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p449.toReal.state (((cells449 0).1:ℝ)/(p449.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(114625062026686238022941517973/200000000000000000000000000000:ℝ)) (by norm_num [p449,cells449,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p449,cells449,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source450 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (144301000000000100000000000000000000000000000/152340146185327154794816045690370258824553919:ℝ) (200000000000000000000000000000/114625062026686238022941517973:ℝ) (1/10:ℝ)) :
 GlobalSource (360502500000000250000000000000000000000000000/380714727312443070681856453272489912939666519:ℝ) (500000000000000000000000000000/287108683297091475574313222173:ℝ) (1/10:ℝ) := by
 have heps : 0<p450.toReal.eps := by norm_num [p450,Params.toReal]
 have hcap : p450.toReal.cap=1/10 := by norm_num [p450,Params.toReal]
 have hi : GlobalSource (p450.toReal.state (((cells450 0).2:ℝ)/(p450.den:ℝ))).B (p450.toReal.state (((cells450 0).2:ℝ)/(p450.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p450,cells450,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells450 0).1 < (cells450 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p450) hw0 heps hcap (commonSigns450 0) (highSigns450 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns450 0)
   (u:=((cells450 0).1:ℝ)/(p450.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p450.toReal.state (((cells450 0).1:ℝ)/(p450.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(287108683297091475574313222173/500000000000000000000000000000:ℝ)) (by norm_num [p450,cells450,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p450,cells450,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source451 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (360502500000000250000000000000000000000000000/380714727312443070681856453272489912939666519:ℝ) (500000000000000000000000000000/287108683297091475574313222173:ℝ) (1/10:ℝ)) :
 GlobalSource (60042083333333375000000000000000000000000000/63429905591711174284884796020164611280128799:ℝ) (250000000000000000000000000000/143828724046418517621280128799:ℝ) (1/10:ℝ) := by
 have heps : 0<p451.toReal.eps := by norm_num [p451,Params.toReal]
 have hcap : p451.toReal.cap=1/10 := by norm_num [p451,Params.toReal]
 have hi : GlobalSource (p451.toReal.state (((cells451 0).2:ℝ)/(p451.den:ℝ))).B (p451.toReal.state (((cells451 0).2:ℝ)/(p451.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p451,cells451,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells451 0).1 < (cells451 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p451) hw0 heps hcap (commonSigns451 0) (highSigns451 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns451 0)
   (u:=((cells451 0).1:ℝ)/(p451.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p451.toReal.state (((cells451 0).1:ℝ)/(p451.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(143828724046418517621280128799/250000000000000000000000000000:ℝ)) (by norm_num [p451,cells451,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p451,cells451,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source452 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (60042083333333375000000000000000000000000000/63429905591711174284884796020164611280128799:ℝ) (250000000000000000000000000000/143828724046418517621280128799:ℝ) (1/10:ℝ)) :
 GlobalSource (72000500000000050000000000000000000000000000/76088897008333686023196447774980979665206473:ℝ) (100000000000000000000000000000/57641793753424932083221735491:ℝ) (1/10:ℝ) := by
 have heps : 0<p452.toReal.eps := by norm_num [p452,Params.toReal]
 have hcap : p452.toReal.cap=1/10 := by norm_num [p452,Params.toReal]
 have hi : GlobalSource (p452.toReal.state (((cells452 0).2:ℝ)/(p452.den:ℝ))).B (p452.toReal.state (((cells452 0).2:ℝ)/(p452.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p452,cells452,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells452 0).1 < (cells452 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p452) hw0 heps hcap (commonSigns452 0) (highSigns452 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns452 0)
   (u:=((cells452 0).1:ℝ)/(p452.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p452.toReal.state (((cells452 0).1:ℝ)/(p452.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(57641793753424932083221735491/100000000000000000000000000000:ℝ)) (by norm_num [p452,cells452,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p452,cells452,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (48133666666666700000000000000000000000000000/50798179619533743896139363578581149326717909:ℝ) (200000000000000000000000000000/114407737707559806059326717909:ℝ) (1/10:ℝ)) :
 GlobalSource (72000500000000050000000000000000000000000000/76088897008333686023196447774980979665206473:ℝ) (100000000000000000000000000000/57641793753424932083221735491:ℝ) (1/10:ℝ) := by
 have h449 := source449 hβ hp
 have h450 := source450 hβ h449
 have h451 := source451 hβ h450
 have h452 := source452 hβ h451
 exact h452
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0449_0452
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0453_0456
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0453_0456

theorem source453 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (72000500000000050000000000000000000000000000/76088897008333686023196447774980979665206473:ℝ) (100000000000000000000000000000/57641793753424932083221735491:ℝ) (1/10:ℝ)) :
 GlobalSource (11069307692307700000000000000000000000000000/11701842543388235094756757974637352411698161:ℝ) (200000000000000000000000000000/115505305926248232550450692031:ℝ) (1/10:ℝ) := by
 have heps : 0<p453.toReal.eps := by norm_num [p453,Params.toReal]
 have hcap : p453.toReal.cap=1/10 := by norm_num [p453,Params.toReal]
 have hi : GlobalSource (p453.toReal.state (((cells453 0).2:ℝ)/(p453.den:ℝ))).B (p453.toReal.state (((cells453 0).2:ℝ)/(p453.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p453,cells453,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells453 0).1 < (cells453 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p453) hw0 heps hcap (commonSigns453 0) (highSigns453 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns453 0)
   (u:=((cells453 0).1:ℝ)/(p453.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p453.toReal.state (((cells453 0).1:ℝ)/(p453.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(115505305926248232550450692031/200000000000000000000000000000:ℝ)) (by norm_num [p453,cells453,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p453,cells453,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source454 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (11069307692307700000000000000000000000000000/11701842543388235094756757974637352411698161:ℝ) (200000000000000000000000000000/115505305926248232550450692031:ℝ) (1/10:ℝ)) :
 GlobalSource (1443785140562250000000000000000000000000000/1526809748143695611304406793441284173617239:ℝ) (500000000000000000000000000000/289320355918646712216410230837:ℝ) (1/10:ℝ) := by
 have heps : 0<p454.toReal.eps := by norm_num [p454,Params.toReal]
 have hcap : p454.toReal.cap=1/10 := by norm_num [p454,Params.toReal]
 have hi : GlobalSource (p454.toReal.state (((cells454 0).2:ℝ)/(p454.den:ℝ))).B (p454.toReal.state (((cells454 0).2:ℝ)/(p454.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p454,cells454,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells454 0).1 < (cells454 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p454) hw0 heps hcap (commonSigns454 0) (highSigns454 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns454 0)
   (u:=((cells454 0).1:ℝ)/(p454.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p454.toReal.state (((cells454 0).1:ℝ)/(p454.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(289320355918646712216410230837/500000000000000000000000000000:ℝ)) (by norm_num [p454,cells454,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p454,cells454,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source455 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1443785140562250000000000000000000000000000/1526809748143695611304406793441284173617239:ℝ) (500000000000000000000000000000/289320355918646712216410230837:ℝ) (1/10:ℝ)) :
 GlobalSource (143701000000000100000000000000000000000000000/152016687926248737285756317573389984084770429:ℝ) (200000000000000000000000000000/115952104777349404231361590143:ℝ) (1/10:ℝ) := by
 have heps : 0<p455.toReal.eps := by norm_num [p455,Params.toReal]
 have hcap : p455.toReal.cap=1/10 := by norm_num [p455,Params.toReal]
 have hi : GlobalSource (p455.toReal.state (((cells455 0).2:ℝ)/(p455.den:ℝ))).B (p455.toReal.state (((cells455 0).2:ℝ)/(p455.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p455,cells455,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells455 0).1 < (cells455 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p455) hw0 heps hcap (commonSigns455 0) (highSigns455 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns455 0)
   (u:=((cells455 0).1:ℝ)/(p455.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p455.toReal.state (((cells455 0).1:ℝ)/(p455.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(115952104777349404231361590143/200000000000000000000000000000:ℝ)) (by norm_num [p455,cells455,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p455,cells455,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source456 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (143701000000000100000000000000000000000000000/152016687926248737285756317573389984084770429:ℝ) (200000000000000000000000000000/115952104777349404231361590143:ℝ) (1/10:ℝ)) :
 GlobalSource (359002500000000250000000000000000000000000000/379908161143515306256277724933207159000910071:ℝ) (500000000000000000000000000000/290443002946044383483000303357:ℝ) (1/10:ℝ) := by
 have heps : 0<p456.toReal.eps := by norm_num [p456,Params.toReal]
 have hcap : p456.toReal.cap=1/10 := by norm_num [p456,Params.toReal]
 have hi : GlobalSource (p456.toReal.state (((cells456 0).2:ℝ)/(p456.den:ℝ))).B (p456.toReal.state (((cells456 0).2:ℝ)/(p456.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p456,cells456,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells456 0).1 < (cells456 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p456) hw0 heps hcap (commonSigns456 0) (highSigns456 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns456 0)
   (u:=((cells456 0).1:ℝ)/(p456.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p456.toReal.state (((cells456 0).1:ℝ)/(p456.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(290443002946044383483000303357/500000000000000000000000000000:ℝ)) (by norm_num [p456,cells456,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p456,cells456,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (72000500000000050000000000000000000000000000/76088897008333686023196447774980979665206473:ℝ) (100000000000000000000000000000/57641793753424932083221735491:ℝ) (1/10:ℝ)) :
 GlobalSource (359002500000000250000000000000000000000000000/379908161143515306256277724933207159000910071:ℝ) (500000000000000000000000000000/290443002946044383483000303357:ℝ) (1/10:ℝ) := by
 have h453 := source453 hβ hp
 have h454 := source454 hβ h453
 have h455 := source455 hβ h454
 have h456 := source456 hβ h455
 exact h456
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0453_0456
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0457_0459
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0457_0459

theorem source457 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (359002500000000250000000000000000000000000000/379908161143515306256277724933207159000910071:ℝ) (500000000000000000000000000000/290443002946044383483000303357:ℝ) (1/10:ℝ)) :
 GlobalSource (7474010416666671875000000000000000000000000/7911978170423939365539128655281184004000519:ℝ) (31250000000000000000000000000/18188037448389510994004000519:ℝ) (1/10:ℝ) := by
 have heps : 0<p457.toReal.eps := by norm_num [p457,Params.toReal]
 have hcap : p457.toReal.cap=1/10 := by norm_num [p457,Params.toReal]
 have hi : GlobalSource (p457.toReal.state (((cells457 0).2:ℝ)/(p457.den:ℝ))).B (p457.toReal.state (((cells457 0).2:ℝ)/(p457.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p457,cells457,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells457 0).1 < (cells457 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p457) hw0 heps hcap (commonSigns457 0) (highSigns457 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns457 0)
   (u:=((cells457 0).1:ℝ)/(p457.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p457.toReal.state (((cells457 0).1:ℝ)/(p457.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(18188037448389510994004000519/31250000000000000000000000000:ℝ)) (by norm_num [p457,cells457,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p457,cells457,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source458 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (7474010416666671875000000000000000000000000/7911978170423939365539128655281184004000519:ℝ) (31250000000000000000000000000/18188037448389510994004000519:ℝ) (1/10:ℝ)) :
 GlobalSource (71700500000000050000000000000000000000000000/75928418768827596266223116815994708074411509:ℝ) (100000000000000000000000000000/58315414213825657872691470503:ℝ) (1/10:ℝ) := by
 have heps : 0<p458.toReal.eps := by norm_num [p458,Params.toReal]
 have hcap : p458.toReal.cap=1/10 := by norm_num [p458,Params.toReal]
 have hi : GlobalSource (p458.toReal.state (((cells458 0).2:ℝ)/(p458.den:ℝ))).B (p458.toReal.state (((cells458 0).2:ℝ)/(p458.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p458,cells458,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells458 0).1 < (cells458 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p458) hw0 heps hcap (commonSigns458 0) (highSigns458 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns458 0)
   (u:=((cells458 0).1:ℝ)/(p458.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p458.toReal.state (((cells458 0).1:ℝ)/(p458.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(58315414213825657872691470503/100000000000000000000000000000:ℝ)) (by norm_num [p458,cells458,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p458,cells458,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source459 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (71700500000000050000000000000000000000000000/75928418768827596266223116815994708074411509:ℝ) (100000000000000000000000000000/58315414213825657872691470503:ℝ) (1/10:ℝ)) :
 GlobalSource (71696583625000000000000000000000000000/75926340443464644863021341853153397837:ℝ) (250000000000000000000000000000/145810860048603321803352465691:ℝ) (1/10:ℝ) := by
 have heps : 0<p459.toReal.eps := by norm_num [p459,Params.toReal]
 have hcap : p459.toReal.cap=1/10 := by norm_num [p459,Params.toReal]
 have hi : GlobalSource (p459.toReal.state (((cells459 0).2:ℝ)/(p459.den:ℝ))).B (p459.toReal.state (((cells459 0).2:ℝ)/(p459.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p459,cells459,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells459 0).1 < (cells459 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p459) hw0 heps hcap (commonSigns459 0) (highSigns459 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns459 0)
   (u:=((cells459 0).1:ℝ)/(p459.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p459.toReal.state (((cells459 0).1:ℝ)/(p459.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(145810860048603321803352465691/250000000000000000000000000000:ℝ)) (by norm_num [p459,cells459,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p459,cells459,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (359002500000000250000000000000000000000000000/379908161143515306256277724933207159000910071:ℝ) (500000000000000000000000000000/290443002946044383483000303357:ℝ) (1/10:ℝ)) :
 GlobalSource (71696583625000000000000000000000000000/75926340443464644863021341853153397837:ℝ) (250000000000000000000000000000/145810860048603321803352465691:ℝ) (1/10:ℝ) := by
 have h457 := source457 hβ hp
 have h458 := source458 hβ h457
 have h459 := source459 hβ h458
 exact h459
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0457_0459
