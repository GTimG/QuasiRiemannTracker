/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0097_0100
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0101_0104
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0105_0108
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0109_0112
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0097_0100
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0097_0100

theorem source97 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (2568404795306719866343750000000000000000000000000/2572168170095162355964623380844470495836196698533:ℝ) (1000000000000000000000000000000/397555440780379977592457133387:ℝ) (1/10:ℝ)) :
 GlobalSource (246531098478085162972843750000000000000000000000000/246896542986659476400064540694079490864316786694907:ℝ) (62500000000000000000000000000/24852620757378329522809389099:ℝ) (1/10:ℝ) := by
 have heps : 0<p97.toReal.eps := by norm_num [p97,Params.toReal]
 have hcap : p97.toReal.cap=1/10 := by norm_num [p97,Params.toReal]
 have hi : GlobalSource (p97.toReal.state (((cells97 0).2:ℝ)/(p97.den:ℝ))).B (p97.toReal.state (((cells97 0).2:ℝ)/(p97.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p97,cells97,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells97 0).1 < (cells97 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p97) hw0 heps hcap (commonSigns97 0) (highSigns97 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns97 0)
   (u:=((cells97 0).1:ℝ)/(p97.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p97.toReal.state (((cells97 0).1:ℝ)/(p97.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(24852620757378329522809389099/62500000000000000000000000000:ℝ)) (by norm_num [p97,cells97,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p97,cells97,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source98 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (246531098478085162972843750000000000000000000000000/246896542986659476400064540694079490864316786694907:ℝ) (62500000000000000000000000000/24852620757378329522809389099:ℝ) (1/10:ℝ)) :
 GlobalSource (394392538570760350042700000000000000000000000000000/394983919631966602537605326069691117208883056648077:ℝ) (200000000000000000000000000000/79545699269473217795446116317:ℝ) (1/10:ℝ) := by
 have heps : 0<p98.toReal.eps := by norm_num [p98,Params.toReal]
 have hcap : p98.toReal.cap=1/10 := by norm_num [p98,Params.toReal]
 have hi : GlobalSource (p98.toReal.state (((cells98 0).2:ℝ)/(p98.den:ℝ))).B (p98.toReal.state (((cells98 0).2:ℝ)/(p98.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p98,cells98,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells98 0).1 < (cells98 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p98) hw0 heps hcap (commonSigns98 0) (highSigns98 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns98 0)
   (u:=((cells98 0).1:ℝ)/(p98.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p98.toReal.state (((cells98 0).1:ℝ)/(p98.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(79545699269473217795446116317/200000000000000000000000000000:ℝ)) (by norm_num [p98,cells98,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p98,cells98,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source99 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (394392538570760350042700000000000000000000000000000/394983919631966602537605326069691117208883056648077:ℝ) (200000000000000000000000000000/79545699269473217795446116317:ℝ) (1/10:ℝ)) :
 GlobalSource (109537588771273455369125000000000000000000000000000/109703717634420381502448730564782092782325336986113:ℝ) (250000000000000000000000000000/99453783385320812101794857907:ℝ) (1/10:ℝ) := by
 have heps : 0<p99.toReal.eps := by norm_num [p99,Params.toReal]
 have hcap : p99.toReal.cap=1/10 := by norm_num [p99,Params.toReal]
 have hi : GlobalSource (p99.toReal.state (((cells99 0).2:ℝ)/(p99.den:ℝ))).B (p99.toReal.state (((cells99 0).2:ℝ)/(p99.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p99,cells99,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells99 0).1 < (cells99 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p99) hw0 heps hcap (commonSigns99 0) (highSigns99 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns99 0)
   (u:=((cells99 0).1:ℝ)/(p99.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p99.toReal.state (((cells99 0).1:ℝ)/(p99.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(99453783385320812101794857907/250000000000000000000000000000:ℝ)) (by norm_num [p99,cells99,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p99,cells99,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source100 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (109537588771273455369125000000000000000000000000000/109703717634420381502448730564782092782325336986113:ℝ) (250000000000000000000000000000/99453783385320812101794857907:ℝ) (1/10:ℝ)) :
 GlobalSource (19713905029120426430750000000000000000000000000000/19744143016593751030050802453549221422505831611403:ℝ) (500000000000000000000000000000/198950921886444050711885079107:ℝ) (1/10:ℝ) := by
 have heps : 0<p100.toReal.eps := by norm_num [p100,Params.toReal]
 have hcap : p100.toReal.cap=1/10 := by norm_num [p100,Params.toReal]
 have hi : GlobalSource (p100.toReal.state (((cells100 0).2:ℝ)/(p100.den:ℝ))).B (p100.toReal.state (((cells100 0).2:ℝ)/(p100.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p100,cells100,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells100 0).1 < (cells100 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p100) hw0 heps hcap (commonSigns100 0) (highSigns100 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns100 0)
   (u:=((cells100 0).1:ℝ)/(p100.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p100.toReal.state (((cells100 0).1:ℝ)/(p100.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(198950921886444050711885079107/500000000000000000000000000000:ℝ)) (by norm_num [p100,cells100,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p100,cells100,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (2568404795306719866343750000000000000000000000000/2572168170095162355964623380844470495836196698533:ℝ) (1000000000000000000000000000000/397555440780379977592457133387:ℝ) (1/10:ℝ)) :
 GlobalSource (19713905029120426430750000000000000000000000000000/19744143016593751030050802453549221422505831611403:ℝ) (500000000000000000000000000000/198950921886444050711885079107:ℝ) (1/10:ℝ) := by
 have h97 := source97 hβ hp
 have h98 := source98 hβ h97
 have h99 := source99 hβ h98
 have h100 := source100 hβ h99
 exact h100
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0097_0100
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0101_0104
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0101_0104

theorem source101 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19713905029120426430750000000000000000000000000000/19744143016593751030050802453549221422505831611403:ℝ) (500000000000000000000000000000/198950921886444050711885079107:ℝ) (1/10:ℝ)) :
 GlobalSource (281586343991594727072250000000000000000000000000000/282023107266606066908679116943081574405002373056129:ℝ) (500000000000000000000000000000/198994313557691353081767770187:ℝ) (1/10:ℝ) := by
 have heps : 0<p101.toReal.eps := by norm_num [p101,Params.toReal]
 have hcap : p101.toReal.cap=1/10 := by norm_num [p101,Params.toReal]
 have hi : GlobalSource (p101.toReal.state (((cells101 0).2:ℝ)/(p101.den:ℝ))).B (p101.toReal.state (((cells101 0).2:ℝ)/(p101.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p101,cells101,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells101 0).1 < (cells101 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p101) hw0 heps hcap (commonSigns101 0) (highSigns101 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns101 0)
   (u:=((cells101 0).1:ℝ)/(p101.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p101.toReal.state (((cells101 0).1:ℝ)/(p101.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(198994313557691353081767770187/500000000000000000000000000000:ℝ)) (by norm_num [p101,cells101,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p101,cells101,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source102 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (281586343991594727072250000000000000000000000000000/282023107266606066908679116943081574405002373056129:ℝ) (500000000000000000000000000000/198994313557691353081767770187:ℝ) (1/10:ℝ)) :
 GlobalSource (41058714853547573665343750000000000000000000000000/41123109688067512369446845042302400958013975492781:ℝ) (62500000000000000000000000000/24879717727630500383040876797:ℝ) (1/10:ℝ) := by
 have heps : 0<p102.toReal.eps := by norm_num [p102,Params.toReal]
 have hcap : p102.toReal.cap=1/10 := by norm_num [p102,Params.toReal]
 have hi : GlobalSource (p102.toReal.state (((cells102 0).2:ℝ)/(p102.den:ℝ))).B (p102.toReal.state (((cells102 0).2:ℝ)/(p102.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p102,cells102,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells102 0).1 < (cells102 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p102) hw0 heps hcap (commonSigns102 0) (highSigns102 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns102 0)
   (u:=((cells102 0).1:ℝ)/(p102.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p102.toReal.state (((cells102 0).1:ℝ)/(p102.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(24879717727630500383040876797/62500000000000000000000000000:ℝ)) (by norm_num [p102,cells102,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p102,cells102,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source103 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (41058714853547573665343750000000000000000000000000/41123109688067512369446845042302400958013975492781:ℝ) (62500000000000000000000000000/24879717727630500383040876797:ℝ) (1/10:ℝ)) :
 GlobalSource (3941064435998807964734500000000000000000000000000000/3947313688259055713349195521528609897356269276183501:ℝ) (1000000000000000000000000000000/398162413426444008618854202043:ℝ) (1/10:ℝ) := by
 have heps : 0<p103.toReal.eps := by norm_num [p103,Params.toReal]
 have hcap : p103.toReal.cap=1/10 := by norm_num [p103,Params.toReal]
 have hi : GlobalSource (p103.toReal.state (((cells103 0).2:ℝ)/(p103.den:ℝ))).B (p103.toReal.state (((cells103 0).2:ℝ)/(p103.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p103,cells103,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells103 0).1 < (cells103 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p103) hw0 heps hcap (commonSigns103 0) (highSigns103 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns103 0)
   (u:=((cells103 0).1:ℝ)/(p103.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p103.toReal.state (((cells103 0).1:ℝ)/(p103.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(398162413426444008618854202043/1000000000000000000000000000000:ℝ)) (by norm_num [p103,cells103,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p103,cells103,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source104 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3941064435998807964734500000000000000000000000000000/3947313688259055713349195521528609897356269276183501:ℝ) (1000000000000000000000000000000/398162413426444008618854202043:ℝ) (1/10:ℝ)) :
 GlobalSource (492561530757131107199500000000000000000000000000000/493351122040087311475251329393759278349106843849471:ℝ) (1000000000000000000000000000000/398249416542009963562411930543:ℝ) (1/10:ℝ) := by
 have heps : 0<p104.toReal.eps := by norm_num [p104,Params.toReal]
 have hcap : p104.toReal.cap=1/10 := by norm_num [p104,Params.toReal]
 have hi : GlobalSource (p104.toReal.state (((cells104 0).2:ℝ)/(p104.den:ℝ))).B (p104.toReal.state (((cells104 0).2:ℝ)/(p104.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p104,cells104,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells104 0).1 < (cells104 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p104) hw0 heps hcap (commonSigns104 0) (highSigns104 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns104 0)
   (u:=((cells104 0).1:ℝ)/(p104.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p104.toReal.state (((cells104 0).1:ℝ)/(p104.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(398249416542009963562411930543/1000000000000000000000000000000:ℝ)) (by norm_num [p104,cells104,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p104,cells104,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19713905029120426430750000000000000000000000000000/19744143016593751030050802453549221422505831611403:ℝ) (500000000000000000000000000000/198950921886444050711885079107:ℝ) (1/10:ℝ)) :
 GlobalSource (492561530757131107199500000000000000000000000000000/493351122040087311475251329393759278349106843849471:ℝ) (1000000000000000000000000000000/398249416542009963562411930543:ℝ) (1/10:ℝ) := by
 have h101 := source101 hβ hp
 have h102 := source102 hβ h101
 have h103 := source103 hβ h102
 have h104 := source104 hβ h103
 exact h104
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0101_0104
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0105_0108
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0105_0108

theorem source105 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (492561530757131107199500000000000000000000000000000/493351122040087311475251329393759278349106843849471:ℝ) (1000000000000000000000000000000/398249416542009963562411930543:ℝ) (1/10:ℝ)) :
 GlobalSource (262661337074352650030500000000000000000000000000000/263086959614271496778512546568607142361733412796303:ℝ) (1000000000000000000000000000000/398336493062464542781098076841:ℝ) (1/10:ℝ) := by
 have heps : 0<p105.toReal.eps := by norm_num [p105,Params.toReal]
 have hcap : p105.toReal.cap=1/10 := by norm_num [p105,Params.toReal]
 have hi : GlobalSource (p105.toReal.state (((cells105 0).2:ℝ)/(p105.den:ℝ))).B (p105.toReal.state (((cells105 0).2:ℝ)/(p105.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p105,cells105,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells105 0).1 < (cells105 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p105) hw0 heps hcap (commonSigns105 0) (highSigns105 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns105 0)
   (u:=((cells105 0).1:ℝ)/(p105.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p105.toReal.state (((cells105 0).1:ℝ)/(p105.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(398336493062464542781098076841/1000000000000000000000000000000:ℝ)) (by norm_num [p105,cells105,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p105,cells105,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source106 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (262661337074352650030500000000000000000000000000000/263086959614271496778512546568607142361733412796303:ℝ) (1000000000000000000000000000000/398336493062464542781098076841:ℝ) (1/10:ℝ)) :
 GlobalSource (984836966543382660829750000000000000000000000000000/986449985478503300738900489908543047155051221751091:ℝ) (500000000000000000000000000000/199211821530803009845310891463:ℝ) (1/10:ℝ) := by
 have heps : 0<p106.toReal.eps := by norm_num [p106,Params.toReal]
 have hcap : p106.toReal.cap=1/10 := by norm_num [p106,Params.toReal]
 have hi : GlobalSource (p106.toReal.state (((cells106 0).2:ℝ)/(p106.den:ℝ))).B (p106.toReal.state (((cells106 0).2:ℝ)/(p106.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p106,cells106,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells106 0).1 < (cells106 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p106) hw0 heps hcap (commonSigns106 0) (highSigns106 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns106 0)
   (u:=((cells106 0).1:ℝ)/(p106.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p106.toReal.state (((cells106 0).1:ℝ)/(p106.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(199211821530803009845310891463/500000000000000000000000000000:ℝ)) (by norm_num [p106,cells106,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p106,cells106,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source107 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (984836966543382660829750000000000000000000000000000/986449985478503300738900489908543047155051221751091:ℝ) (500000000000000000000000000000/199211821530803009845310891463:ℝ) (1/10:ℝ)) :
 GlobalSource (1969387838115885768090250000000000000000000000000000/1972647809697764383361749260758703019783372303699377:ℝ) (500000000000000000000000000000/199255433306676224701276107619:ℝ) (1/10:ℝ) := by
 have heps : 0<p107.toReal.eps := by norm_num [p107,Params.toReal]
 have hcap : p107.toReal.cap=1/10 := by norm_num [p107,Params.toReal]
 have hi : GlobalSource (p107.toReal.state (((cells107 0).2:ℝ)/(p107.den:ℝ))).B (p107.toReal.state (((cells107 0).2:ℝ)/(p107.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p107,cells107,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells107 0).1 < (cells107 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p107) hw0 heps hcap (commonSigns107 0) (highSigns107 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns107 0)
   (u:=((cells107 0).1:ℝ)/(p107.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p107.toReal.state (((cells107 0).1:ℝ)/(p107.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(199255433306676224701276107619/500000000000000000000000000000:ℝ)) (by norm_num [p107,cells107,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p107,cells107,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source108 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1969387838115885768090250000000000000000000000000000/1972647809697764383361749260758703019783372303699377:ℝ) (500000000000000000000000000000/199255433306676224701276107619:ℝ) (1/10:ℝ)) :
 GlobalSource (109394541285833678584500000000000000000000000000000/109577539628716647383716102419495534643273101577637:ℝ) (1000000000000000000000000000000/398598163791741849267280698591:ℝ) (1/10:ℝ) := by
 have heps : 0<p108.toReal.eps := by norm_num [p108,Params.toReal]
 have hcap : p108.toReal.cap=1/10 := by norm_num [p108,Params.toReal]
 have hi : GlobalSource (p108.toReal.state (((cells108 0).2:ℝ)/(p108.den:ℝ))).B (p108.toReal.state (((cells108 0).2:ℝ)/(p108.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p108,cells108,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells108 0).1 < (cells108 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p108) hw0 heps hcap (commonSigns108 0) (highSigns108 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns108 0)
   (u:=((cells108 0).1:ℝ)/(p108.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p108.toReal.state (((cells108 0).1:ℝ)/(p108.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(398598163791741849267280698591/1000000000000000000000000000000:ℝ)) (by norm_num [p108,cells108,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p108,cells108,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (492561530757131107199500000000000000000000000000000/493351122040087311475251329393759278349106843849471:ℝ) (1000000000000000000000000000000/398249416542009963562411930543:ℝ) (1/10:ℝ)) :
 GlobalSource (109394541285833678584500000000000000000000000000000/109577539628716647383716102419495534643273101577637:ℝ) (1000000000000000000000000000000/398598163791741849267280698591:ℝ) (1/10:ℝ) := by
 have h105 := source105 hβ hp
 have h106 := source106 hβ h105
 have h107 := source107 hβ h106
 have h108 := source108 hβ h107
 exact h108
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0105_0108
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0109_0112
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0109_0112

theorem source109 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (109394541285833678584500000000000000000000000000000/109577539628716647383716102419495534643273101577637:ℝ) (1000000000000000000000000000000/398598163791741849267280698591:ℝ) (1/10:ℝ)) :
 GlobalSource (98440782408706333047587500000000000000000000000000/98607184090104421398863292817076672321474255503227:ℝ) (25000000000000000000000000000/9967138366773309496123105687:ℝ) (1/10:ℝ) := by
 have heps : 0<p109.toReal.eps := by norm_num [p109,Params.toReal]
 have hcap : p109.toReal.cap=1/10 := by norm_num [p109,Params.toReal]
 have hi : GlobalSource (p109.toReal.state (((cells109 0).2:ℝ)/(p109.den:ℝ))).B (p109.toReal.state (((cells109 0).2:ℝ)/(p109.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p109,cells109,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells109 0).1 < (cells109 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p109) hw0 heps hcap (commonSigns109 0) (highSigns109 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns109 0)
   (u:=((cells109 0).1:ℝ)/(p109.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p109.toReal.state (((cells109 0).1:ℝ)/(p109.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(9967138366773309496123105687/25000000000000000000000000000:ℝ)) (by norm_num [p109,cells109,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p109,cells109,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source110 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (98440782408706333047587500000000000000000000000000/98607184090104421398863292817076672321474255503227:ℝ) (25000000000000000000000000000/9967138366773309496123105687:ℝ) (1/10:ℝ)) :
 GlobalSource (393705910640649421476500000000000000000000000000000/394378343028218505740200449775401638349292780432233:ℝ) (1000000000000000000000000000000/398772979325202526301843441787:ℝ) (1/10:ℝ) := by
 have heps : 0<p110.toReal.eps := by norm_num [p110,Params.toReal]
 have hcap : p110.toReal.cap=1/10 := by norm_num [p110,Params.toReal]
 have hi : GlobalSource (p110.toReal.state (((cells110 0).2:ℝ)/(p110.den:ℝ))).B (p110.toReal.state (((cells110 0).2:ℝ)/(p110.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p110,cells110,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells110 0).1 < (cells110 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p110) hw0 heps hcap (commonSigns110 0) (highSigns110 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns110 0)
   (u:=((cells110 0).1:ℝ)/(p110.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p110.toReal.state (((cells110 0).1:ℝ)/(p110.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(398772979325202526301843441787/1000000000000000000000000000000:ℝ)) (by norm_num [p110,cells110,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p110,cells110,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source111 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (393705910640649421476500000000000000000000000000000/394378343028218505740200449775401638349292780432233:ℝ) (1000000000000000000000000000000/398772979325202526301843441787:ℝ) (1/10:ℝ)) :
 GlobalSource (1312162305488245035875500000000000000000000000000000/1314426542214506295642353260480165155931608774894293:ℝ) (1000000000000000000000000000000/398860497828951280220915035681:ℝ) (1/10:ℝ) := by
 have heps : 0<p111.toReal.eps := by norm_num [p111,Params.toReal]
 have hcap : p111.toReal.cap=1/10 := by norm_num [p111,Params.toReal]
 have hi : GlobalSource (p111.toReal.state (((cells111 0).2:ℝ)/(p111.den:ℝ))).B (p111.toReal.state (((cells111 0).2:ℝ)/(p111.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p111,cells111,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells111 0).1 < (cells111 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p111) hw0 heps hcap (commonSigns111 0) (highSigns111 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns111 0)
   (u:=((cells111 0).1:ℝ)/(p111.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p111.toReal.state (((cells111 0).1:ℝ)/(p111.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(398860497828951280220915035681/1000000000000000000000000000000:ℝ)) (by norm_num [p111,cells111,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p111,cells111,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source112 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1312162305488245035875500000000000000000000000000000/1314426542214506295642353260480165155931608774894293:ℝ) (1000000000000000000000000000000/398860497828951280220915035681:ℝ) (1/10:ℝ)) :
 GlobalSource (491989340815372000061000000000000000000000000000/492846994083005548839543323154054453672026355171:ℝ) (2000000000000000000000000000/797896180513396643766609587:ℝ) (1/10:ℝ) := by
 have heps : 0<p112.toReal.eps := by norm_num [p112,Params.toReal]
 have hcap : p112.toReal.cap=1/10 := by norm_num [p112,Params.toReal]
 have hi : GlobalSource (p112.toReal.state (((cells112 0).2:ℝ)/(p112.den:ℝ))).B (p112.toReal.state (((cells112 0).2:ℝ)/(p112.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p112,cells112,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells112 0).1 < (cells112 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p112) hw0 heps hcap (commonSigns112 0) (highSigns112 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns112 0)
   (u:=((cells112 0).1:ℝ)/(p112.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p112.toReal.state (((cells112 0).1:ℝ)/(p112.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(797896180513396643766609587/2000000000000000000000000000:ℝ)) (by norm_num [p112,cells112,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p112,cells112,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (109394541285833678584500000000000000000000000000000/109577539628716647383716102419495534643273101577637:ℝ) (1000000000000000000000000000000/398598163791741849267280698591:ℝ) (1/10:ℝ)) :
 GlobalSource (491989340815372000061000000000000000000000000000/492846994083005548839543323154054453672026355171:ℝ) (2000000000000000000000000000/797896180513396643766609587:ℝ) (1/10:ℝ) := by
 have h109 := source109 hβ hp
 have h110 := source110 hβ h109
 have h111 := source111 hβ h110
 have h112 := source112 hβ h111
 exact h112
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0109_0112
