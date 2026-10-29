/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0433_0436
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0437_0440
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0441_0444
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0445_0448
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0433_0436
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0433_0436

theorem source433 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (45625312500000031250000000000000000000000000/47901013384894191411174859411308084300058581:ℝ) (62500000000000000000000000000/34710124696487820758100019527:ℝ) (1/10:ℝ)) :
 GlobalSource (243168333333333500000000000000000000000000000/255377825859180013038878345306506251558672139:ℝ) (1000000000000000000000000000000/556366584299207983861558672139:ℝ) (1/10:ℝ) := by
 have heps : 0<p433.toReal.eps := by norm_num [p433,Params.toReal]
 have hcap : p433.toReal.cap=1/10 := by norm_num [p433,Params.toReal]
 have hi : GlobalSource (p433.toReal.state (((cells433 0).2:ℝ)/(p433.den:ℝ))).B (p433.toReal.state (((cells433 0).2:ℝ)/(p433.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p433,cells433,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells433 0).1 < (cells433 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p433) hw0 heps hcap (commonSigns433 0) (highSigns433 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns433 0)
   (u:=((cells433 0).1:ℝ)/(p433.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p433.toReal.state (((cells433 0).1:ℝ)/(p433.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(556366584299207983861558672139/1000000000000000000000000000000:ℝ)) (by norm_num [p433,cells433,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p433,cells433,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source434 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (243168333333333500000000000000000000000000000/255377825859180013038878345306506251558672139:ℝ) (1000000000000000000000000000000/556366584299207983861558672139:ℝ) (1/10:ℝ)) :
 GlobalSource (729005000000000500000000000000000000000000000/765851402812792973593037025970646102529008679:ℝ) (1000000000000000000000000000000/557376041871568525770843002893:ℝ) (1/10:ℝ) := by
 have heps : 0<p434.toReal.eps := by norm_num [p434,Params.toReal]
 have hcap : p434.toReal.cap=1/10 := by norm_num [p434,Params.toReal]
 have hi : GlobalSource (p434.toReal.state (((cells434 0).2:ℝ)/(p434.den:ℝ))).B (p434.toReal.state (((cells434 0).2:ℝ)/(p434.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p434,cells434,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells434 0).1 < (cells434 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p434) hw0 heps hcap (commonSigns434 0) (highSigns434 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns434 0)
   (u:=((cells434 0).1:ℝ)/(p434.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p434.toReal.state (((cells434 0).1:ℝ)/(p434.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(557376041871568525770843002893/1000000000000000000000000000000:ℝ)) (by norm_num [p434,cells434,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p434,cells434,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source435 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (729005000000000500000000000000000000000000000/765851402812792973593037025970646102529008679:ℝ) (1000000000000000000000000000000/557376041871568525770843002893:ℝ) (1/10:ℝ)) :
 GlobalSource (364252500000000250000000000000000000000000000/382784995665119392904586807825745468114866177:ℝ) (500000000000000000000000000000/279195200444278064899371622059:ℝ) (1/10:ℝ) := by
 have heps : 0<p435.toReal.eps := by norm_num [p435,Params.toReal]
 have hcap : p435.toReal.cap=1/10 := by norm_num [p435,Params.toReal]
 have hi : GlobalSource (p435.toReal.state (((cells435 0).2:ℝ)/(p435.den:ℝ))).B (p435.toReal.state (((cells435 0).2:ℝ)/(p435.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p435,cells435,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells435 0).1 < (cells435 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p435) hw0 heps hcap (commonSigns435 0) (highSigns435 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns435 0)
   (u:=((cells435 0).1:ℝ)/(p435.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p435.toReal.state (((cells435 0).1:ℝ)/(p435.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(279195200444278064899371622059/500000000000000000000000000000:ℝ)) (by norm_num [p435,cells435,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p435,cells435,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source436 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (364252500000000250000000000000000000000000000/382784995665119392904586807825745468114866177:ℝ) (500000000000000000000000000000/279195200444278064899371622059:ℝ) (1/10:ℝ)) :
 GlobalSource (242668333333333500000000000000000000000000000/255096414870064929651736272222633699417763499:ℝ) (1000000000000000000000000000000/559409694677889454709417763499:ℝ) (1/10:ℝ) := by
 have heps : 0<p436.toReal.eps := by norm_num [p436,Params.toReal]
 have hcap : p436.toReal.cap=1/10 := by norm_num [p436,Params.toReal]
 have hi : GlobalSource (p436.toReal.state (((cells436 0).2:ℝ)/(p436.den:ℝ))).B (p436.toReal.state (((cells436 0).2:ℝ)/(p436.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p436,cells436,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells436 0).1 < (cells436 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p436) hw0 heps hcap (commonSigns436 0) (highSigns436 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns436 0)
   (u:=((cells436 0).1:ℝ)/(p436.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p436.toReal.state (((cells436 0).1:ℝ)/(p436.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(559409694677889454709417763499/1000000000000000000000000000000:ℝ)) (by norm_num [p436,cells436,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p436,cells436,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (45625312500000031250000000000000000000000000/47901013384894191411174859411308084300058581:ℝ) (62500000000000000000000000000/34710124696487820758100019527:ℝ) (1/10:ℝ)) :
 GlobalSource (242668333333333500000000000000000000000000000/255096414870064929651736272222633699417763499:ℝ) (1000000000000000000000000000000/559409694677889454709417763499:ℝ) (1/10:ℝ) := by
 have h433 := source433 hβ hp
 have h434 := source434 hβ h433
 have h435 := source435 hβ h434
 have h436 := source436 hβ h435
 exact h436
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0433_0436
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0437_0440
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0437_0440

theorem source437 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (242668333333333500000000000000000000000000000/255096414870064929651736272222633699417763499:ℝ) (1000000000000000000000000000000/559409694677889454709417763499:ℝ) (1/10:ℝ)) :
 GlobalSource (727505000000000500000000000000000000000000000/765009164147279371943495783061278682257248887:ℝ) (1000000000000000000000000000000/560433956870748401604085749629:ℝ) (1/10:ℝ) := by
 have heps : 0<p437.toReal.eps := by norm_num [p437,Params.toReal]
 have hcap : p437.toReal.cap=1/10 := by norm_num [p437,Params.toReal]
 have hi : GlobalSource (p437.toReal.state (((cells437 0).2:ℝ)/(p437.den:ℝ))).B (p437.toReal.state (((cells437 0).2:ℝ)/(p437.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p437,cells437,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells437 0).1 < (cells437 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p437) hw0 heps hcap (commonSigns437 0) (highSigns437 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns437 0)
   (u:=((cells437 0).1:ℝ)/(p437.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p437.toReal.state (((cells437 0).1:ℝ)/(p437.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(560433956870748401604085749629/1000000000000000000000000000000:ℝ)) (by norm_num [p437,cells437,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p437,cells437,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source438 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (727505000000000500000000000000000000000000000/765009164147279371943495783061278682257248887:ℝ) (1000000000000000000000000000000/560433956870748401604085749629:ℝ) (1/10:ℝ)) :
 GlobalSource (727005000000000500000000000000000000000000000/764729751450571176987747184619380080819076497:ℝ) (1000000000000000000000000000000/561463221405232992370273025499:ℝ) (1/10:ℝ) := by
 have heps : 0<p438.toReal.eps := by norm_num [p438,Params.toReal]
 have hcap : p438.toReal.cap=1/10 := by norm_num [p438,Params.toReal]
 have hi : GlobalSource (p438.toReal.state (((cells438 0).2:ℝ)/(p438.den:ℝ))).B (p438.toReal.state (((cells438 0).2:ℝ)/(p438.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p438,cells438,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells438 0).1 < (cells438 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p438) hw0 heps hcap (commonSigns438 0) (highSigns438 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns438 0)
   (u:=((cells438 0).1:ℝ)/(p438.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p438.toReal.state (((cells438 0).1:ℝ)/(p438.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(561463221405232992370273025499/1000000000000000000000000000000:ℝ)) (by norm_num [p438,cells438,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p438,cells438,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source439 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (727005000000000500000000000000000000000000000/764729751450571176987747184619380080819076497:ℝ) (1000000000000000000000000000000/561463221405232992370273025499:ℝ) (1/10:ℝ)) :
 GlobalSource (242168333333333500000000000000000000000000000/254817002681256940453191926117609743218684461:ℝ) (1000000000000000000000000000000/562497522529869932133218684461:ℝ) (1/10:ℝ) := by
 have heps : 0<p439.toReal.eps := by norm_num [p439,Params.toReal]
 have hcap : p439.toReal.cap=1/10 := by norm_num [p439,Params.toReal]
 have hi : GlobalSource (p439.toReal.state (((cells439 0).2:ℝ)/(p439.den:ℝ))).B (p439.toReal.state (((cells439 0).2:ℝ)/(p439.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p439,cells439,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells439 0).1 < (cells439 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p439) hw0 heps hcap (commonSigns439 0) (highSigns439 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns439 0)
   (u:=((cells439 0).1:ℝ)/(p439.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p439.toReal.state (((cells439 0).1:ℝ)/(p439.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(562497522529869932133218684461/1000000000000000000000000000000:ℝ)) (by norm_num [p439,cells439,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p439,cells439,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source440 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (242168333333333500000000000000000000000000000/254817002681256940453191926117609743218684461:ℝ) (1000000000000000000000000000000/562497522529869932133218684461:ℝ) (1/10:ℝ)) :
 GlobalSource (145201000000000100000000000000000000000000000/152834587093073042683056508425884131798686147:ℝ) (200000000000000000000000000000/112707378961433526220599562049:ℝ) (1/10:ℝ) := by
 have heps : 0<p440.toReal.eps := by norm_num [p440,Params.toReal]
 have hcap : p440.toReal.cap=1/10 := by norm_num [p440,Params.toReal]
 have hi : GlobalSource (p440.toReal.state (((cells440 0).2:ℝ)/(p440.den:ℝ))).B (p440.toReal.state (((cells440 0).2:ℝ)/(p440.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p440,cells440,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells440 0).1 < (cells440 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p440) hw0 heps hcap (commonSigns440 0) (highSigns440 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns440 0)
   (u:=((cells440 0).1:ℝ)/(p440.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p440.toReal.state (((cells440 0).1:ℝ)/(p440.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(112707378961433526220599562049/200000000000000000000000000000:ℝ)) (by norm_num [p440,cells440,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p440,cells440,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (242668333333333500000000000000000000000000000/255096414870064929651736272222633699417763499:ℝ) (1000000000000000000000000000000/559409694677889454709417763499:ℝ) (1/10:ℝ)) :
 GlobalSource (145201000000000100000000000000000000000000000/152834587093073042683056508425884131798686147:ℝ) (200000000000000000000000000000/112707378961433526220599562049:ℝ) (1/10:ℝ) := by
 have h437 := source437 hβ hp
 have h438 := source438 hβ h437
 have h439 := source439 hβ h438
 have h440 := source440 hβ h439
 exact h440
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0437_0440
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0441_0444
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0441_0444

theorem source441 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (145201000000000100000000000000000000000000000/152834587093073042683056508425884131798686147:ℝ) (200000000000000000000000000000/112707378961433526220599562049:ℝ) (1/10:ℝ)) :
 GlobalSource (362752500000000250000000000000000000000000000/381947767634397257089753953329228140635412737:ℝ) (500000000000000000000000000000/282290686558610237923545137579:ℝ) (1/10:ℝ) := by
 have heps : 0<p441.toReal.eps := by norm_num [p441,Params.toReal]
 have hcap : p441.toReal.cap=1/10 := by norm_num [p441,Params.toReal]
 have hi : GlobalSource (p441.toReal.state (((cells441 0).2:ℝ)/(p441.den:ℝ))).B (p441.toReal.state (((cells441 0).2:ℝ)/(p441.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p441,cells441,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells441 0).1 < (cells441 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p441) hw0 heps hcap (commonSigns441 0) (highSigns441 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns441 0)
   (u:=((cells441 0).1:ℝ)/(p441.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p441.toReal.state (((cells441 0).1:ℝ)/(p441.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(282290686558610237923545137579/500000000000000000000000000000:ℝ)) (by norm_num [p441,cells441,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p441,cells441,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source442 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (362752500000000250000000000000000000000000000/381947767634397257089753953329228140635412737:ℝ) (500000000000000000000000000000/282290686558610237923545137579:ℝ) (1/10:ℝ)) :
 GlobalSource (3776067708333335937500000000000000000000000/3977181296992821859371789361509386432366009:ℝ) (15625000000000000000000000000/8837984260333799296432366009:ℝ) (1/10:ℝ) := by
 have heps : 0<p442.toReal.eps := by norm_num [p442,Params.toReal]
 have hcap : p442.toReal.cap=1/10 := by norm_num [p442,Params.toReal]
 have hi : GlobalSource (p442.toReal.state (((cells442 0).2:ℝ)/(p442.den:ℝ))).B (p442.toReal.state (((cells442 0).2:ℝ)/(p442.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p442,cells442,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells442 0).1 < (cells442 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p442) hw0 heps hcap (commonSigns442 0) (highSigns442 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns442 0)
   (u:=((cells442 0).1:ℝ)/(p442.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p442.toReal.state (((cells442 0).1:ℝ)/(p442.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(8837984260333799296432366009/15625000000000000000000000000:ℝ)) (by norm_num [p442,cells442,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p442,cells442,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source443 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3776067708333335937500000000000000000000000/3977181296992821859371789361509386432366009:ℝ) (15625000000000000000000000000/8837984260333799296432366009:ℝ) (1/10:ℝ)) :
 GlobalSource (181126250000000125000000000000000000000000000/190835689577676364761048273088000015257229641:ℝ) (250000000000000000000000000000/141671447241468964868419076547:ℝ) (1/10:ℝ) := by
 have heps : 0<p443.toReal.eps := by norm_num [p443,Params.toReal]
 have hcap : p443.toReal.cap=1/10 := by norm_num [p443,Params.toReal]
 have hi : GlobalSource (p443.toReal.state (((cells443 0).2:ℝ)/(p443.den:ℝ))).B (p443.toReal.state (((cells443 0).2:ℝ)/(p443.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p443,cells443,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells443 0).1 < (cells443 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p443) hw0 heps hcap (commonSigns443 0) (highSigns443 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns443 0)
   (u:=((cells443 0).1:ℝ)/(p443.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p443.toReal.state (((cells443 0).1:ℝ)/(p443.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(141671447241468964868419076547/250000000000000000000000000000:ℝ)) (by norm_num [p443,cells443,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p443,cells443,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source444 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (181126250000000125000000000000000000000000000/190835689577676364761048273088000015257229641:ℝ) (250000000000000000000000000000/141671447241468964868419076547:ℝ) (1/10:ℝ)) :
 GlobalSource (181001250000000125000000000000000000000000000/190766846183093609930593281902380618331661339:ℝ) (250000000000000000000000000000/141936449471435298409443887113:ℝ) (1/10:ℝ) := by
 have heps : 0<p444.toReal.eps := by norm_num [p444,Params.toReal]
 have hcap : p444.toReal.cap=1/10 := by norm_num [p444,Params.toReal]
 have hi : GlobalSource (p444.toReal.state (((cells444 0).2:ℝ)/(p444.den:ℝ))).B (p444.toReal.state (((cells444 0).2:ℝ)/(p444.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p444,cells444,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells444 0).1 < (cells444 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p444) hw0 heps hcap (commonSigns444 0) (highSigns444 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns444 0)
   (u:=((cells444 0).1:ℝ)/(p444.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p444.toReal.state (((cells444 0).1:ℝ)/(p444.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(141936449471435298409443887113/250000000000000000000000000000:ℝ)) (by norm_num [p444,cells444,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p444,cells444,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (145201000000000100000000000000000000000000000/152834587093073042683056508425884131798686147:ℝ) (200000000000000000000000000000/112707378961433526220599562049:ℝ) (1/10:ℝ)) :
 GlobalSource (181001250000000125000000000000000000000000000/190766846183093609930593281902380618331661339:ℝ) (250000000000000000000000000000/141936449471435298409443887113:ℝ) (1/10:ℝ) := by
 have h441 := source441 hβ hp
 have h442 := source442 hβ h441
 have h443 := source443 hβ h442
 have h444 := source444 hβ h443
 exact h444
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0441_0444
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0445_0448
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0445_0448

theorem source445 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (181001250000000125000000000000000000000000000/190766846183093609930593281902380618331661339:ℝ) (250000000000000000000000000000/141936449471435298409443887113:ℝ) (1/10:ℝ)) :
 GlobalSource (48233666666666700000000000000000000000000000/50852845993507086828073726912887331221460867:ℝ) (200000000000000000000000000000/113762211121690729661221460867:ℝ) (1/10:ℝ) := by
 have heps : 0<p445.toReal.eps := by norm_num [p445,Params.toReal]
 have hcap : p445.toReal.cap=1/10 := by norm_num [p445,Params.toReal]
 have hi : GlobalSource (p445.toReal.state (((cells445 0).2:ℝ)/(p445.den:ℝ))).B (p445.toReal.state (((cells445 0).2:ℝ)/(p445.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p445,cells445,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells445 0).1 < (cells445 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p445) hw0 heps hcap (commonSigns445 0) (highSigns445 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns445 0)
   (u:=((cells445 0).1:ℝ)/(p445.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p445.toReal.state (((cells445 0).1:ℝ)/(p445.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(113762211121690729661221460867/200000000000000000000000000000:ℝ)) (by norm_num [p445,cells445,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p445,cells445,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source446 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (48233666666666700000000000000000000000000000/50852845993507086828073726912887331221460867:ℝ) (200000000000000000000000000000/113762211121690729661221460867:ℝ) (1/10:ℝ)) :
 GlobalSource (723005000000000500000000000000000000000000000/762518675452208237344955393232597847443598989:ℝ) (1000000000000000000000000000000/569881598657882504652481199663:ℝ) (1/10:ℝ) := by
 have heps : 0<p446.toReal.eps := by norm_num [p446,Params.toReal]
 have hcap : p446.toReal.cap=1/10 := by norm_num [p446,Params.toReal]
 have hi : GlobalSource (p446.toReal.state (((cells446 0).2:ℝ)/(p446.den:ℝ))).B (p446.toReal.state (((cells446 0).2:ℝ)/(p446.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p446,cells446,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells446 0).1 < (cells446 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p446) hw0 heps hcap (commonSigns446 0) (highSigns446 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns446 0)
   (u:=((cells446 0).1:ℝ)/(p446.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p446.toReal.state (((cells446 0).1:ℝ)/(p446.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(569881598657882504652481199663/1000000000000000000000000000000:ℝ)) (by norm_num [p446,cells446,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p446,cells446,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source447 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (723005000000000500000000000000000000000000000/762518675452208237344955393232597847443598989:ℝ) (1000000000000000000000000000000/569881598657882504652481199663:ℝ) (1/10:ℝ)) :
 GlobalSource (722505000000000500000000000000000000000000000/762245343028001044640210045205416176788051141:ℝ) (1000000000000000000000000000000/570957463898189053255596017047:ℝ) (1/10:ℝ) := by
 have heps : 0<p447.toReal.eps := by norm_num [p447,Params.toReal]
 have hcap : p447.toReal.cap=1/10 := by norm_num [p447,Params.toReal]
 have hi : GlobalSource (p447.toReal.state (((cells447 0).2:ℝ)/(p447.den:ℝ))).B (p447.toReal.state (((cells447 0).2:ℝ)/(p447.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p447,cells447,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells447 0).1 < (cells447 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p447) hw0 heps hcap (commonSigns447 0) (highSigns447 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns447 0)
   (u:=((cells447 0).1:ℝ)/(p447.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p447.toReal.state (((cells447 0).1:ℝ)/(p447.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(570957463898189053255596017047/1000000000000000000000000000000:ℝ)) (by norm_num [p447,cells447,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p447,cells447,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source448 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (722505000000000500000000000000000000000000000/762245343028001044640210045205416176788051141:ℝ) (1000000000000000000000000000000/570957463898189053255596017047:ℝ) (1/10:ℝ)) :
 GlobalSource (48133666666666700000000000000000000000000000/50798179619533743896139363578581149326717909:ℝ) (200000000000000000000000000000/114407737707559806059326717909:ℝ) (1/10:ℝ) := by
 have heps : 0<p448.toReal.eps := by norm_num [p448,Params.toReal]
 have hcap : p448.toReal.cap=1/10 := by norm_num [p448,Params.toReal]
 have hi : GlobalSource (p448.toReal.state (((cells448 0).2:ℝ)/(p448.den:ℝ))).B (p448.toReal.state (((cells448 0).2:ℝ)/(p448.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p448,cells448,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells448 0).1 < (cells448 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p448) hw0 heps hcap (commonSigns448 0) (highSigns448 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns448 0)
   (u:=((cells448 0).1:ℝ)/(p448.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p448.toReal.state (((cells448 0).1:ℝ)/(p448.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(114407737707559806059326717909/200000000000000000000000000000:ℝ)) (by norm_num [p448,cells448,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p448,cells448,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem prefix0447 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (181001250000000125000000000000000000000000000/190766846183093609930593281902380618331661339:ℝ) (250000000000000000000000000000/141936449471435298409443887113:ℝ) (1/10:ℝ)) :
 GlobalSource (722505000000000500000000000000000000000000000/762245343028001044640210045205416176788051141:ℝ) (1000000000000000000000000000000/570957463898189053255596017047:ℝ) (1/10:ℝ) := by
 have h445 := source445 hβ hp
 have h446 := source446 hβ h445
 have h447 := source447 hβ h446
 exact h447

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (181001250000000125000000000000000000000000000/190766846183093609930593281902380618331661339:ℝ) (250000000000000000000000000000/141936449471435298409443887113:ℝ) (1/10:ℝ)) :
 GlobalSource (48133666666666700000000000000000000000000000/50798179619533743896139363578581149326717909:ℝ) (200000000000000000000000000000/114407737707559806059326717909:ℝ) (1/10:ℝ) := by
 have h445 := source445 hβ hp
 have h446 := source446 hβ h445
 have h447 := source447 hβ h446
 have h448 := source448 hβ h447
 exact h448
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0445_0448
