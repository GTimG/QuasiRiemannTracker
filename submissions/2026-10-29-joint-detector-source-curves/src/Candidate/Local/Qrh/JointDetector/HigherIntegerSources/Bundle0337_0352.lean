/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0337_0340
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0341_0344
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0345_0348
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0349_0352
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0337_0340
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0337_0340

theorem source337 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (129615500000000000000000000000000000/132731107427273282712601311684141901:ℝ) (1000000000000000000000000000000/477977865582759676018485563857:ℝ) (1/10:ℝ)) :
 GlobalSource (97149125000000000000000000000000000/99505129673920523325400028241037239:ℝ) (250000000000000000000000000000/119658059756103176397431907541:ℝ) (1/10:ℝ) := by
 have heps : 0<p337.toReal.eps := by norm_num [p337,Params.toReal]
 have hcap : p337.toReal.cap=1/10 := by norm_num [p337,Params.toReal]
 have hi : GlobalSource (p337.toReal.state (((cells337 0).2:ℝ)/(p337.den:ℝ))).B (p337.toReal.state (((cells337 0).2:ℝ)/(p337.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p337,cells337,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells337 0).1 < (cells337 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p337) hw0 heps hcap (commonSigns337 0) (highSigns337 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns337 0)
   (u:=((cells337 0).1:ℝ)/(p337.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p337.toReal.state (((cells337 0).1:ℝ)/(p337.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(119658059756103176397431907541/250000000000000000000000000000:ℝ)) (by norm_num [p337,cells337,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p337,cells337,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source338 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (97149125000000000000000000000000000/99505129673920523325400028241037239:ℝ) (250000000000000000000000000000/119658059756103176397431907541:ℝ) (1/10:ℝ)) :
 GlobalSource (194173250000000000000000000000000000/198924019978859144792322143811399153:ℝ) (500000000000000000000000000000/239644684396134759212463083407:ℝ) (1/10:ℝ) := by
 have heps : 0<p338.toReal.eps := by norm_num [p338,Params.toReal]
 have hcap : p338.toReal.cap=1/10 := by norm_num [p338,Params.toReal]
 have hi : GlobalSource (p338.toReal.state (((cells338 0).2:ℝ)/(p338.den:ℝ))).B (p338.toReal.state (((cells338 0).2:ℝ)/(p338.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p338,cells338,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells338 0).1 < (cells338 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p338) hw0 heps hcap (commonSigns338 0) (highSigns338 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns338 0)
   (u:=((cells338 0).1:ℝ)/(p338.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p338.toReal.state (((cells338 0).1:ℝ)/(p338.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(239644684396134759212463083407/500000000000000000000000000000:ℝ)) (by norm_num [p338,cells338,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p338,cells338,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source339 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (194173250000000000000000000000000000/198924019978859144792322143811399153:ℝ) (500000000000000000000000000000/239644684396134759212463083407:ℝ) (1/10:ℝ)) :
 GlobalSource (129365500000000000000000000000000000/132558628848212937565589694280236799:ℝ) (1000000000000000000000000000000/479949270431230833386761048543:ℝ) (1/10:ℝ) := by
 have heps : 0<p339.toReal.eps := by norm_num [p339,Params.toReal]
 have hcap : p339.toReal.cap=1/10 := by norm_num [p339,Params.toReal]
 have hi : GlobalSource (p339.toReal.state (((cells339 0).2:ℝ)/(p339.den:ℝ))).B (p339.toReal.state (((cells339 0).2:ℝ)/(p339.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p339,cells339,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells339 0).1 < (cells339 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p339) hw0 heps hcap (commonSigns339 0) (highSigns339 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns339 0)
   (u:=((cells339 0).1:ℝ)/(p339.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p339.toReal.state (((cells339 0).1:ℝ)/(p339.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(479949270431230833386761048543/1000000000000000000000000000000:ℝ)) (by norm_num [p339,cells339,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p339,cells339,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source340 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (129365500000000000000000000000000000/132558628848212937565589694280236799:ℝ) (1000000000000000000000000000000/479949270431230833386761048543:ℝ) (1/10:ℝ)) :
 GlobalSource (48480812500000000000000000000000000/49688007366832014763457972717312319:ℝ) (125000000000000000000000000000/60076494950097892418327599561:ℝ) (1/10:ℝ) := by
 have heps : 0<p340.toReal.eps := by norm_num [p340,Params.toReal]
 have hcap : p340.toReal.cap=1/10 := by norm_num [p340,Params.toReal]
 have hi : GlobalSource (p340.toReal.state (((cells340 0).2:ℝ)/(p340.den:ℝ))).B (p340.toReal.state (((cells340 0).2:ℝ)/(p340.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p340,cells340,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells340 0).1 < (cells340 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p340) hw0 heps hcap (commonSigns340 0) (highSigns340 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns340 0)
   (u:=((cells340 0).1:ℝ)/(p340.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p340.toReal.state (((cells340 0).1:ℝ)/(p340.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(60076494950097892418327599561/125000000000000000000000000000:ℝ)) (by norm_num [p340,cells340,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p340,cells340,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (129615500000000000000000000000000000/132731107427273282712601311684141901:ℝ) (1000000000000000000000000000000/477977865582759676018485563857:ℝ) (1/10:ℝ)) :
 GlobalSource (48480812500000000000000000000000000/49688007366832014763457972717312319:ℝ) (125000000000000000000000000000/60076494950097892418327599561:ℝ) (1/10:ℝ) := by
 have h337 := source337 hβ hp
 have h338 := source338 hβ h337
 have h339 := source339 hβ h338
 have h340 := source340 hβ h339
 exact h340
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0337_0340
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0341_0344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0341_0344

theorem source341 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (48480812500000000000000000000000000/49688007366832014763457972717312319:ℝ) (125000000000000000000000000000/60076494950097892418327599561:ℝ) (1/10:ℝ)) :
 GlobalSource (387596500000000000000000000000000000/397332557607493981317153471699196899:ℝ) (1000000000000000000000000000000/481277452076050845911964175081:ℝ) (1/10:ℝ) := by
 have heps : 0<p341.toReal.eps := by norm_num [p341,Params.toReal]
 have hcap : p341.toReal.cap=1/10 := by norm_num [p341,Params.toReal]
 have hi : GlobalSource (p341.toReal.state (((cells341 0).2:ℝ)/(p341.den:ℝ))).B (p341.toReal.state (((cells341 0).2:ℝ)/(p341.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p341,cells341,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells341 0).1 < (cells341 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p341) hw0 heps hcap (commonSigns341 0) (highSigns341 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns341 0)
   (u:=((cells341 0).1:ℝ)/(p341.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p341.toReal.state (((cells341 0).1:ℝ)/(p341.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(481277452076050845911964175081/1000000000000000000000000000000:ℝ)) (by norm_num [p341,cells341,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p341,cells341,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source342 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (387596500000000000000000000000000000/397332557607493981317153471699196899:ℝ) (1000000000000000000000000000000/481277452076050845911964175081:ℝ) (1/10:ℝ)) :
 GlobalSource (64557750000000000000000000000000000/66193563840732809086014529404012803:ℝ) (500000000000000000000000000000/240972881874430033113383047271:ℝ) (1/10:ℝ) := by
 have heps : 0<p342.toReal.eps := by norm_num [p342,Params.toReal]
 have hcap : p342.toReal.cap=1/10 := by norm_num [p342,Params.toReal]
 have hi : GlobalSource (p342.toReal.state (((cells342 0).2:ℝ)/(p342.den:ℝ))).B (p342.toReal.state (((cells342 0).2:ℝ)/(p342.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p342,cells342,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells342 0).1 < (cells342 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p342) hw0 heps hcap (commonSigns342 0) (highSigns342 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns342 0)
   (u:=((cells342 0).1:ℝ)/(p342.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p342.toReal.state (((cells342 0).1:ℝ)/(p342.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(240972881874430033113383047271/500000000000000000000000000000:ℝ)) (by norm_num [p342,cells342,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p342,cells342,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source343 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (64557750000000000000000000000000000/66193563840732809086014529404012803:ℝ) (500000000000000000000000000000/240972881874430033113383047271:ℝ) (1/10:ℝ)) :
 GlobalSource (387096500000000000000000000000000000/396990535728139342151985895201743801:ℝ) (1000000000000000000000000000000/482616910628814183381761381219:ℝ) (1/10:ℝ) := by
 have heps : 0<p343.toReal.eps := by norm_num [p343,Params.toReal]
 have hcap : p343.toReal.cap=1/10 := by norm_num [p343,Params.toReal]
 have hi : GlobalSource (p343.toReal.state (((cells343 0).2:ℝ)/(p343.den:ℝ))).B (p343.toReal.state (((cells343 0).2:ℝ)/(p343.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p343,cells343,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells343 0).1 < (cells343 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p343) hw0 heps hcap (commonSigns343 0) (highSigns343 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns343 0)
   (u:=((cells343 0).1:ℝ)/(p343.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p343.toReal.state (((cells343 0).1:ℝ)/(p343.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(482616910628814183381761381219/1000000000000000000000000000000:ℝ)) (by norm_num [p343,cells343,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p343,cells343,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source344 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (387096500000000000000000000000000000/396990535728139342151985895201743801:ℝ) (1000000000000000000000000000000/482616910628814183381761381219:ℝ) (1/10:ℝ)) :
 GlobalSource (9671162500000000000000000000000000/9920500403575894949678045762553129:ℝ) (25000000000000000000000000000/12082272721109533856885933951:ℝ) (1/10:ℝ) := by
 have heps : 0<p344.toReal.eps := by norm_num [p344,Params.toReal]
 have hcap : p344.toReal.cap=1/10 := by norm_num [p344,Params.toReal]
 have hi : GlobalSource (p344.toReal.state (((cells344 0).2:ℝ)/(p344.den:ℝ))).B (p344.toReal.state (((cells344 0).2:ℝ)/(p344.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p344,cells344,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells344 0).1 < (cells344 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p344) hw0 heps hcap (commonSigns344 0) (highSigns344 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns344 0)
   (u:=((cells344 0).1:ℝ)/(p344.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p344.toReal.state (((cells344 0).1:ℝ)/(p344.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(12082272721109533856885933951/25000000000000000000000000000:ℝ)) (by norm_num [p344,cells344,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p344,cells344,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (48480812500000000000000000000000000/49688007366832014763457972717312319:ℝ) (125000000000000000000000000000/60076494950097892418327599561:ℝ) (1/10:ℝ)) :
 GlobalSource (9671162500000000000000000000000000/9920500403575894949678045762553129:ℝ) (25000000000000000000000000000/12082272721109533856885933951:ℝ) (1/10:ℝ) := by
 have h341 := source341 hβ hp
 have h342 := source342 hβ h341
 have h343 := source343 hβ h342
 have h344 := source344 hβ h343
 exact h344
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0341_0344
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0345_0348
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0345_0348

theorem source345 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (9671162500000000000000000000000000/9920500403575894949678045762553129:ℝ) (25000000000000000000000000000/12082272721109533856885933951:ℝ) (1/10:ℝ)) :
 GlobalSource (8054093750000000000000000000000000/8263538016144792631516771005028833:ℝ) (62500000000000000000000000000/30247985915249631694504511481:ℝ) (1/10:ℝ) := by
 have heps : 0<p345.toReal.eps := by norm_num [p345,Params.toReal]
 have hcap : p345.toReal.cap=1/10 := by norm_num [p345,Params.toReal]
 have hi : GlobalSource (p345.toReal.state (((cells345 0).2:ℝ)/(p345.den:ℝ))).B (p345.toReal.state (((cells345 0).2:ℝ)/(p345.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p345,cells345,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells345 0).1 < (cells345 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p345) hw0 heps hcap (commonSigns345 0) (highSigns345 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns345 0)
   (u:=((cells345 0).1:ℝ)/(p345.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p345.toReal.state (((cells345 0).1:ℝ)/(p345.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(30247985915249631694504511481/62500000000000000000000000000:ℝ)) (by norm_num [p345,cells345,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p345,cells345,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source346 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (8054093750000000000000000000000000/8263538016144792631516771005028833:ℝ) (62500000000000000000000000000/30247985915249631694504511481:ℝ) (1/10:ℝ)) :
 GlobalSource (19317325000000000000000000000000000/19823998105565261503122363136741281:ℝ) (50000000000000000000000000000/24232376219858059555522587839:ℝ) (1/10:ℝ) := by
 have heps : 0<p346.toReal.eps := by norm_num [p346,Params.toReal]
 have hcap : p346.toReal.cap=1/10 := by norm_num [p346,Params.toReal]
 have hi : GlobalSource (p346.toReal.state (((cells346 0).2:ℝ)/(p346.den:ℝ))).B (p346.toReal.state (((cells346 0).2:ℝ)/(p346.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p346,cells346,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells346 0).1 < (cells346 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p346) hw0 heps hcap (commonSigns346 0) (highSigns346 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns346 0)
   (u:=((cells346 0).1:ℝ)/(p346.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p346.toReal.state (((cells346 0).1:ℝ)/(p346.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(24232376219858059555522587839/50000000000000000000000000000:ℝ)) (by norm_num [p346,cells346,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p346,cells346,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source347 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19317325000000000000000000000000000/19823998105565261503122363136741281:ℝ) (50000000000000000000000000000/24232376219858059555522587839:ℝ) (1/10:ℝ)) :
 GlobalSource (386096500000000000000000000000000000/396310428641093788647565181164542987:ℝ) (1000000000000000000000000000000/485330174595591839427128521753:ℝ) (1/10:ℝ) := by
 have heps : 0<p347.toReal.eps := by norm_num [p347,Params.toReal]
 have hcap : p347.toReal.cap=1/10 := by norm_num [p347,Params.toReal]
 have hi : GlobalSource (p347.toReal.state (((cells347 0).2:ℝ)/(p347.den:ℝ))).B (p347.toReal.state (((cells347 0).2:ℝ)/(p347.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p347,cells347,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells347 0).1 < (cells347 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p347) hw0 heps hcap (commonSigns347 0) (highSigns347 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns347 0)
   (u:=((cells347 0).1:ℝ)/(p347.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p347.toReal.state (((cells347 0).1:ℝ)/(p347.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(485330174595591839427128521753/1000000000000000000000000000000:ℝ)) (by norm_num [p347,cells347,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p347,cells347,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source348 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (386096500000000000000000000000000000/396310428641093788647565181164542987:ℝ) (1000000000000000000000000000000/485330174595591839427128521753:ℝ) (1/10:ℝ)) :
 GlobalSource (803846875000000000000000000000000/825294218447682434219556369161547:ℝ) (6250000000000000000000000000/3037598386589578804825874679:ℝ) (1/10:ℝ) := by
 have heps : 0<p348.toReal.eps := by norm_num [p348,Params.toReal]
 have hcap : p348.toReal.cap=1/10 := by norm_num [p348,Params.toReal]
 have hi : GlobalSource (p348.toReal.state (((cells348 0).2:ℝ)/(p348.den:ℝ))).B (p348.toReal.state (((cells348 0).2:ℝ)/(p348.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p348,cells348,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells348 0).1 < (cells348 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p348) hw0 heps hcap (commonSigns348 0) (highSigns348 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns348 0)
   (u:=((cells348 0).1:ℝ)/(p348.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p348.toReal.state (((cells348 0).1:ℝ)/(p348.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(3037598386589578804825874679/6250000000000000000000000000:ℝ)) (by norm_num [p348,cells348,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p348,cells348,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (9671162500000000000000000000000000/9920500403575894949678045762553129:ℝ) (25000000000000000000000000000/12082272721109533856885933951:ℝ) (1/10:ℝ)) :
 GlobalSource (803846875000000000000000000000000/825294218447682434219556369161547:ℝ) (6250000000000000000000000000/3037598386589578804825874679:ℝ) (1/10:ℝ) := by
 have h345 := source345 hβ hp
 have h346 := source346 hβ h345
 have h347 := source347 hβ h346
 have h348 := source348 hβ h347
 exact h348
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0345_0348
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0349_0352
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0349_0352

theorem source349 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (803846875000000000000000000000000/825294218447682434219556369161547:ℝ) (6250000000000000000000000000/3037598386589578804825874679:ℝ) (1/10:ℝ)) :
 GlobalSource (385596500000000000000000000000000000/395972351244848068794263384517269769:ℝ) (1000000000000000000000000000000/486704242912916961713937287611:ℝ) (1/10:ℝ) := by
 have heps : 0<p349.toReal.eps := by norm_num [p349,Params.toReal]
 have hcap : p349.toReal.cap=1/10 := by norm_num [p349,Params.toReal]
 have hi : GlobalSource (p349.toReal.state (((cells349 0).2:ℝ)/(p349.den:ℝ))).B (p349.toReal.state (((cells349 0).2:ℝ)/(p349.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p349,cells349,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells349 0).1 < (cells349 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p349) hw0 heps hcap (commonSigns349 0) (highSigns349 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns349 0)
   (u:=((cells349 0).1:ℝ)/(p349.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p349.toReal.state (((cells349 0).1:ℝ)/(p349.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(486704242912916961713937287611/1000000000000000000000000000000:ℝ)) (by norm_num [p349,cells349,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p349,cells349,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source350 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (385596500000000000000000000000000000/395972351244848068794263384517269769:ℝ) (1000000000000000000000000000000/486704242912916961713937287611:ℝ) (1/10:ℝ)) :
 GlobalSource (385346500000000000000000000000000000/395803808304736827003770605163992209:ℝ) (1000000000000000000000000000000/487395694636527760234867057471:ℝ) (1/10:ℝ) := by
 have heps : 0<p350.toReal.eps := by norm_num [p350,Params.toReal]
 have hcap : p350.toReal.cap=1/10 := by norm_num [p350,Params.toReal]
 have hi : GlobalSource (p350.toReal.state (((cells350 0).2:ℝ)/(p350.den:ℝ))).B (p350.toReal.state (((cells350 0).2:ℝ)/(p350.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p350,cells350,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells350 0).1 < (cells350 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p350) hw0 heps hcap (commonSigns350 0) (highSigns350 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns350 0)
   (u:=((cells350 0).1:ℝ)/(p350.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p350.toReal.state (((cells350 0).1:ℝ)/(p350.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(487395694636527760234867057471/1000000000000000000000000000000:ℝ)) (by norm_num [p350,cells350,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p350,cells350,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source351 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (385346500000000000000000000000000000/395803808304736827003770605163992209:ℝ) (1000000000000000000000000000000/487395694636527760234867057471:ℝ) (1/10:ℝ)) :
 GlobalSource (16045687500000000000000000000000000/16484816522080247702515589729716961:ℝ) (125000000000000000000000000000/61011264252146605213738289777:ℝ) (1/10:ℝ) := by
 have heps : 0<p351.toReal.eps := by norm_num [p351,Params.toReal]
 have hcap : p351.toReal.cap=1/10 := by norm_num [p351,Params.toReal]
 have hi : GlobalSource (p351.toReal.state (((cells351 0).2:ℝ)/(p351.den:ℝ))).B (p351.toReal.state (((cells351 0).2:ℝ)/(p351.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p351,cells351,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells351 0).1 < (cells351 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p351) hw0 heps hcap (commonSigns351 0) (highSigns351 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns351 0)
   (u:=((cells351 0).1:ℝ)/(p351.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p351.toReal.state (((cells351 0).1:ℝ)/(p351.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(61011264252146605213738289777/125000000000000000000000000000:ℝ)) (by norm_num [p351,cells351,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p351,cells351,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source352 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (16045687500000000000000000000000000/16484816522080247702515589729716961:ℝ) (125000000000000000000000000000/61011264252146605213738289777:ℝ) (1/10:ℝ)) :
 GlobalSource (19242325000000000000000000000000000/19773385820870438030345790051037881:ℝ) (50000000000000000000000000000/24439375908743692557025692239:ℝ) (1/10:ℝ) := by
 have heps : 0<p352.toReal.eps := by norm_num [p352,Params.toReal]
 have hcap : p352.toReal.cap=1/10 := by norm_num [p352,Params.toReal]
 have hi : GlobalSource (p352.toReal.state (((cells352 0).2:ℝ)/(p352.den:ℝ))).B (p352.toReal.state (((cells352 0).2:ℝ)/(p352.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p352,cells352,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells352 0).1 < (cells352 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p352) hw0 heps hcap (commonSigns352 0) (highSigns352 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns352 0)
   (u:=((cells352 0).1:ℝ)/(p352.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p352.toReal.state (((cells352 0).1:ℝ)/(p352.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(24439375908743692557025692239/50000000000000000000000000000:ℝ)) (by norm_num [p352,cells352,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p352,cells352,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (803846875000000000000000000000000/825294218447682434219556369161547:ℝ) (6250000000000000000000000000/3037598386589578804825874679:ℝ) (1/10:ℝ)) :
 GlobalSource (19242325000000000000000000000000000/19773385820870438030345790051037881:ℝ) (50000000000000000000000000000/24439375908743692557025692239:ℝ) (1/10:ℝ) := by
 have h349 := source349 hβ hp
 have h350 := source350 hβ h349
 have h351 := source351 hβ h350
 have h352 := source352 hβ h351
 exact h352
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0349_0352
