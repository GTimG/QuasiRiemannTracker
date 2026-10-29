/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0161_0164
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0165_0168
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0169_0172
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0173_0176
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0161_0164
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0161_0164

theorem source161 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (6106952514560216965375000000000000000000000000000/6123049452969895540942021533550017368223516921897:ℝ) (500000000000000000000000000000/201620476320088292773616622101:ℝ) (1/10:ℝ)) :
 GlobalSource (244242338711048734418843750000000000000000000000000/244890893946826436103747483657865032358143626535891:ℝ) (62500000000000000000000000000/25208266324650060538194792899:ℝ) (1/10:ℝ) := by
 have heps : 0<p161.toReal.eps := by norm_num [p161,Params.toReal]
 have hcap : p161.toReal.cap=1/10 := by norm_num [p161,Params.toReal]
 have hi : GlobalSource (p161.toReal.state (((cells161 0).2:ℝ)/(p161.den:ℝ))).B (p161.toReal.state (((cells161 0).2:ℝ)/(p161.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p161,cells161,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells161 0).1 < (cells161 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p161) hw0 heps hcap (commonSigns161 0) (highSigns161 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns161 0)
   (u:=((cells161 0).1:ℝ)/(p161.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p161.toReal.state (((cells161 0).1:ℝ)/(p161.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(25208266324650060538194792899/62500000000000000000000000000:ℝ)) (by norm_num [p161,cells161,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p161,cells161,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source162 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (244242338711048734418843750000000000000000000000000/244890893946826436103747483657865032358143626535891:ℝ) (62500000000000000000000000000/25208266324650060538194792899:ℝ) (1/10:ℝ)) :
 GlobalSource (325608769119585053630250000000000000000000000000000/326479757088547345719176488314340919102765698754047:ℝ) (500000000000000000000000000000/201711823778321901958297623469:ℝ) (1/10:ℝ) := by
 have heps : 0<p162.toReal.eps := by norm_num [p162,Params.toReal]
 have hcap : p162.toReal.cap=1/10 := by norm_num [p162,Params.toReal]
 have hi : GlobalSource (p162.toReal.state (((cells162 0).2:ℝ)/(p162.den:ℝ))).B (p162.toReal.state (((cells162 0).2:ℝ)/(p162.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p162,cells162,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells162 0).1 < (cells162 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p162) hw0 heps hcap (commonSigns162 0) (highSigns162 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns162 0)
   (u:=((cells162 0).1:ℝ)/(p162.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p162.toReal.state (((cells162 0).1:ℝ)/(p162.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(201711823778321901958297623469/500000000000000000000000000000:ℝ)) (by norm_num [p162,cells162,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p162,cells162,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source163 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (325608769119585053630250000000000000000000000000000/326479757088547345719176488314340919102765698754047:ℝ) (500000000000000000000000000000/201711823778321901958297623469:ℝ) (1/10:ℝ)) :
 GlobalSource (3906733039493261536424500000000000000000000000000000/3917259995625017331791350737650653444695461578691823:ℝ) (1000000000000000000000000000000/403515111807832062043707414709:ℝ) (1/10:ℝ) := by
 have heps : 0<p163.toReal.eps := by norm_num [p163,Params.toReal]
 have hcap : p163.toReal.cap=1/10 := by norm_num [p163,Params.toReal]
 have hi : GlobalSource (p163.toReal.state (((cells163 0).2:ℝ)/(p163.den:ℝ))).B (p163.toReal.state (((cells163 0).2:ℝ)/(p163.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p163,cells163,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells163 0).1 < (cells163 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p163) hw0 heps hcap (commonSigns163 0) (highSigns163 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns163 0)
   (u:=((cells163 0).1:ℝ)/(p163.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p163.toReal.state (((cells163 0).1:ℝ)/(p163.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(403515111807832062043707414709/1000000000000000000000000000000:ℝ)) (by norm_num [p163,cells163,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p163,cells163,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source164 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3906733039493261536424500000000000000000000000000000/3917259995625017331791350737650653444695461578691823:ℝ) (1000000000000000000000000000000/403515111807832062043707414709:ℝ) (1/10:ℝ)) :
 GlobalSource (976540212387875607321500000000000000000000000000000/979190758705244278900539596012481734742532011501987:ℝ) (1000000000000000000000000000000/403606654029023504687553680803:ℝ) (1/10:ℝ) := by
 have heps : 0<p164.toReal.eps := by norm_num [p164,Params.toReal]
 have hcap : p164.toReal.cap=1/10 := by norm_num [p164,Params.toReal]
 have hi : GlobalSource (p164.toReal.state (((cells164 0).2:ℝ)/(p164.den:ℝ))).B (p164.toReal.state (((cells164 0).2:ℝ)/(p164.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p164,cells164,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells164 0).1 < (cells164 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p164) hw0 heps hcap (commonSigns164 0) (highSigns164 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns164 0)
   (u:=((cells164 0).1:ℝ)/(p164.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p164.toReal.state (((cells164 0).1:ℝ)/(p164.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(403606654029023504687553680803/1000000000000000000000000000000:ℝ)) (by norm_num [p164,cells164,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p164,cells164,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (6106952514560216965375000000000000000000000000000/6123049452969895540942021533550017368223516921897:ℝ) (500000000000000000000000000000/201620476320088292773616622101:ℝ) (1/10:ℝ)) :
 GlobalSource (976540212387875607321500000000000000000000000000000/979190758705244278900539596012481734742532011501987:ℝ) (1000000000000000000000000000000/403606654029023504687553680803:ℝ) (1/10:ℝ) := by
 have h161 := source161 hβ hp
 have h162 := source162 hβ h161
 have h163 := source163 hβ h162
 have h164 := source164 hβ h163
 exact h164
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0161_0164
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0165_0168
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0165_0168

theorem source165 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (976540212387875607321500000000000000000000000000000/979190758705244278900539596012481734742532011501987:ℝ) (1000000000000000000000000000000/403606654029023504687553680803:ℝ) (1/10:ℝ)) :
 GlobalSource (52074515461463244295300000000000000000000000000000/52216882701800156883171899180617814348344865538053:ℝ) (200000000000000000000000000000/80739654860281378310128786367:ℝ) (1/10:ℝ) := by
 have heps : 0<p165.toReal.eps := by norm_num [p165,Params.toReal]
 have hcap : p165.toReal.cap=1/10 := by norm_num [p165,Params.toReal]
 have hi : GlobalSource (p165.toReal.state (((cells165 0).2:ℝ)/(p165.den:ℝ))).B (p165.toReal.state (((cells165 0).2:ℝ)/(p165.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p165,cells165,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells165 0).1 < (cells165 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p165) hw0 heps hcap (commonSigns165 0) (highSigns165 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns165 0)
   (u:=((cells165 0).1:ℝ)/(p165.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p165.toReal.state (((cells165 0).1:ℝ)/(p165.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(80739654860281378310128786367/200000000000000000000000000000:ℝ)) (by norm_num [p165,cells165,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p165,cells165,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source166 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (52074515461463244295300000000000000000000000000000/52216882701800156883171899180617814348344865538053:ℝ) (200000000000000000000000000000/80739654860281378310128786367:ℝ) (1/10:ℝ)) :
 GlobalSource (976254117416996053752250000000000000000000000000000/978942374762960747538237144764923133459773356222681:ℝ) (500000000000000000000000000000/201894986353151093869624476803:ℝ) (1/10:ℝ) := by
 have heps : 0<p166.toReal.eps := by norm_num [p166,Params.toReal]
 have hcap : p166.toReal.cap=1/10 := by norm_num [p166,Params.toReal]
 have hi : GlobalSource (p166.toReal.state (((cells166 0).2:ℝ)/(p166.den:ℝ))).B (p166.toReal.state (((cells166 0).2:ℝ)/(p166.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p166,cells166,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells166 0).1 < (cells166 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p166) hw0 heps hcap (commonSigns166 0) (highSigns166 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns166 0)
   (u:=((cells166 0).1:ℝ)/(p166.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p166.toReal.state (((cells166 0).1:ℝ)/(p166.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(201894986353151093869624476803/500000000000000000000000000000:ℝ)) (by norm_num [p166,cells166,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p166,cells166,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source167 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (976254117416996053752250000000000000000000000000000/978942374762960747538237144764923133459773356222681:ℝ) (500000000000000000000000000000/201894986353151093869624476803:ℝ) (1/10:ℝ)) :
 GlobalSource (122013883741444534620953125000000000000000000000000/122352278876760928038271394278009775676144639378399:ℝ) (31250000000000000000000000000/12621304666411274114389155513:ℝ) (1/10:ℝ) := by
 have heps : 0<p167.toReal.eps := by norm_num [p167,Params.toReal]
 have hcap : p167.toReal.cap=1/10 := by norm_num [p167,Params.toReal]
 have hi : GlobalSource (p167.toReal.state (((cells167 0).2:ℝ)/(p167.den:ℝ))).B (p167.toReal.state (((cells167 0).2:ℝ)/(p167.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p167,cells167,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells167 0).1 < (cells167 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p167) hw0 heps hcap (commonSigns167 0) (highSigns167 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns167 0)
   (u:=((cells167 0).1:ℝ)/(p167.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p167.toReal.state (((cells167 0).1:ℝ)/(p167.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(12621304666411274114389155513/31250000000000000000000000000:ℝ)) (by norm_num [p167,cells167,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p167,cells167,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source168 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (122013883741444534620953125000000000000000000000000/122352278876760928038271394278009775676144639378399:ℝ) (31250000000000000000000000000/12621304666411274114389155513:ℝ) (1/10:ℝ)) :
 GlobalSource (40665334268588187507625000000000000000000000000000/40778921642016330879334158419839272142189452499429:ℝ) (250000000000000000000000000000/100993401059891410853662349863:ℝ) (1/10:ℝ) := by
 have heps : 0<p168.toReal.eps := by norm_num [p168,Params.toReal]
 have hcap : p168.toReal.cap=1/10 := by norm_num [p168,Params.toReal]
 have hi : GlobalSource (p168.toReal.state (((cells168 0).2:ℝ)/(p168.den:ℝ))).B (p168.toReal.state (((cells168 0).2:ℝ)/(p168.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p168,cells168,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells168 0).1 < (cells168 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p168) hw0 heps hcap (commonSigns168 0) (highSigns168 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns168 0)
   (u:=((cells168 0).1:ℝ)/(p168.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p168.toReal.state (((cells168 0).1:ℝ)/(p168.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(100993401059891410853662349863/250000000000000000000000000000:ℝ)) (by norm_num [p168,cells168,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p168,cells168,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (976540212387875607321500000000000000000000000000000/979190758705244278900539596012481734742532011501987:ℝ) (1000000000000000000000000000000/403606654029023504687553680803:ℝ) (1/10:ℝ)) :
 GlobalSource (40665334268588187507625000000000000000000000000000/40778921642016330879334158419839272142189452499429:ℝ) (250000000000000000000000000000/100993401059891410853662349863:ℝ) (1/10:ℝ) := by
 have h165 := source165 hβ hp
 have h166 := source166 hβ h165
 have h167 := source167 hβ h166
 have h168 := source168 hβ h167
 exact h168
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0165_0168
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0169_0172
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0169_0172

theorem source169 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (40665334268588187507625000000000000000000000000000/40778921642016330879334158419839272142189452499429:ℝ) (250000000000000000000000000000/100993401059891410853662349863:ℝ) (1/10:ℝ)) :
 GlobalSource (39032998998427068935935000000000000000000000000000/39142801597686898000298209499150401760273705978157:ℝ) (10000000000000000000000000000/4040655375312316336922124437:ℝ) (1/10:ℝ) := by
 have heps : 0<p169.toReal.eps := by norm_num [p169,Params.toReal]
 have hcap : p169.toReal.cap=1/10 := by norm_num [p169,Params.toReal]
 have hi : GlobalSource (p169.toReal.state (((cells169 0).2:ℝ)/(p169.den:ℝ))).B (p169.toReal.state (((cells169 0).2:ℝ)/(p169.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p169,cells169,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells169 0).1 < (cells169 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p169) hw0 heps hcap (commonSigns169 0) (highSigns169 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns169 0)
   (u:=((cells169 0).1:ℝ)/(p169.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p169.toReal.state (((cells169 0).1:ℝ)/(p169.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(4040655375312316336922124437/10000000000000000000000000000:ℝ)) (by norm_num [p169,cells169,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p169,cells169,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source170 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (39032998998427068935935000000000000000000000000000/39142801597686898000298209499150401760273705978157:ℝ) (10000000000000000000000000000/4040655375312316336922124437:ℝ) (1/10:ℝ)) :
 GlobalSource (39027277099009477864550000000000000000000000000000/39137839704470649086194661866264118564286071628561:ℝ) (100000000000000000000000000000/40415754928200561318237408257:ℝ) (1/10:ℝ) := by
 have heps : 0<p170.toReal.eps := by norm_num [p170,Params.toReal]
 have hcap : p170.toReal.cap=1/10 := by norm_num [p170,Params.toReal]
 have hi : GlobalSource (p170.toReal.state (((cells170 0).2:ℝ)/(p170.den:ℝ))).B (p170.toReal.state (((cells170 0).2:ℝ)/(p170.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p170,cells170,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells170 0).1 < (cells170 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p170) hw0 heps hcap (commonSigns170 0) (highSigns170 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns170 0)
   (u:=((cells170 0).1:ℝ)/(p170.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p170.toReal.state (((cells170 0).1:ℝ)/(p170.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(40415754928200561318237408257/100000000000000000000000000000:ℝ)) (by norm_num [p170,cells170,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p170,cells170,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source171 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (39027277099009477864550000000000000000000000000000/39137839704470649086194661866264118564286071628561:ℝ) (100000000000000000000000000000/40415754928200561318237408257:ℝ) (1/10:ℝ)) :
 GlobalSource (130071850665306289310550000000000000000000000000000/130442930321806615211312269296792486503584244234359:ℝ) (100000000000000000000000000000/40424963957386670247302730623:ℝ) (1/10:ℝ) := by
 have heps : 0<p171.toReal.eps := by norm_num [p171,Params.toReal]
 have hcap : p171.toReal.cap=1/10 := by norm_num [p171,Params.toReal]
 have hi : GlobalSource (p171.toReal.state (((cells171 0).2:ℝ)/(p171.den:ℝ))).B (p171.toReal.state (((cells171 0).2:ℝ)/(p171.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p171,cells171,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells171 0).1 < (cells171 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p171) hw0 heps hcap (commonSigns171 0) (highSigns171 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns171 0)
   (u:=((cells171 0).1:ℝ)/(p171.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p171.toReal.state (((cells171 0).1:ℝ)/(p171.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(40424963957386670247302730623/100000000000000000000000000000:ℝ)) (by norm_num [p171,cells171,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p171,cells171,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source172 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (130071850665306289310550000000000000000000000000000/130442930321806615211312269296792486503584244234359:ℝ) (100000000000000000000000000000/40424963957386670247302730623:ℝ) (1/10:ℝ)) :
 GlobalSource (975395832504357393044500000000000000000000000000000/978197994343937959248125948808361897625058414883779:ℝ) (1000000000000000000000000000000/404341808488926482469452664737:ℝ) (1/10:ℝ) := by
 have heps : 0<p172.toReal.eps := by norm_num [p172,Params.toReal]
 have hcap : p172.toReal.cap=1/10 := by norm_num [p172,Params.toReal]
 have hi : GlobalSource (p172.toReal.state (((cells172 0).2:ℝ)/(p172.den:ℝ))).B (p172.toReal.state (((cells172 0).2:ℝ)/(p172.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p172,cells172,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells172 0).1 < (cells172 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p172) hw0 heps hcap (commonSigns172 0) (highSigns172 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns172 0)
   (u:=((cells172 0).1:ℝ)/(p172.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p172.toReal.state (((cells172 0).1:ℝ)/(p172.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(404341808488926482469452664737/1000000000000000000000000000000:ℝ)) (by norm_num [p172,cells172,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p172,cells172,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (40665334268588187507625000000000000000000000000000/40778921642016330879334158419839272142189452499429:ℝ) (250000000000000000000000000000/100993401059891410853662349863:ℝ) (1/10:ℝ)) :
 GlobalSource (975395832504357393044500000000000000000000000000000/978197994343937959248125948808361897625058414883779:ℝ) (1000000000000000000000000000000/404341808488926482469452664737:ℝ) (1/10:ℝ) := by
 have h169 := source169 hβ hp
 have h170 := source170 hβ h169
 have h171 := source171 hβ h170
 have h172 := source172 hβ h171
 exact h172
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0169_0172
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0173_0176
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0173_0176

theorem source173 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (975395832504357393044500000000000000000000000000000/978197994343937959248125948808361897625058414883779:ℝ) (1000000000000000000000000000000/404341808488926482469452664737:ℝ) (1/10:ℝ)) :
 GlobalSource (975252785018917616259875000000000000000000000000000/978074043399385559648355772793707726048320858697719:ℝ) (250000000000000000000000000000/101108514027357301328590672387:ℝ) (1/10:ℝ) := by
 have heps : 0<p173.toReal.eps := by norm_num [p173,Params.toReal]
 have hcap : p173.toReal.cap=1/10 := by norm_num [p173,Params.toReal]
 have hi : GlobalSource (p173.toReal.state (((cells173 0).2:ℝ)/(p173.den:ℝ))).B (p173.toReal.state (((cells173 0).2:ℝ)/(p173.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p173,cells173,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells173 0).1 < (cells173 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p173) hw0 heps hcap (commonSigns173 0) (highSigns173 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns173 0)
   (u:=((cells173 0).1:ℝ)/(p173.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p173.toReal.state (((cells173 0).1:ℝ)/(p173.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(101108514027357301328590672387/250000000000000000000000000000:ℝ)) (by norm_num [p173,cells173,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p173,cells173,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source174 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (975252785018917616259875000000000000000000000000000/978074043399385559648355772793707726048320858697719:ℝ) (250000000000000000000000000000/101108514027357301328590672387:ℝ) (1/10:ℝ)) :
 GlobalSource (650073158355651892983500000000000000000000000000000/651966749717590401760917210861736603499047447303819:ℝ) (1000000000000000000000000000000/404526382517752005822835199719:ℝ) (1/10:ℝ) := by
 have heps : 0<p174.toReal.eps := by norm_num [p174,Params.toReal]
 have hcap : p174.toReal.cap=1/10 := by norm_num [p174,Params.toReal]
 have hi : GlobalSource (p174.toReal.state (((cells174 0).2:ℝ)/(p174.den:ℝ))).B (p174.toReal.state (((cells174 0).2:ℝ)/(p174.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p174,cells174,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells174 0).1 < (cells174 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p174) hw0 heps hcap (commonSigns174 0) (highSigns174 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns174 0)
   (u:=((cells174 0).1:ℝ)/(p174.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p174.toReal.state (((cells174 0).1:ℝ)/(p174.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(404526382517752005822835199719/1000000000000000000000000000000:ℝ)) (by norm_num [p174,cells174,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p174,cells174,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source175 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (650073158355651892983500000000000000000000000000000/651966749717590401760917210861736603499047447303819:ℝ) (1000000000000000000000000000000/404526382517752005822835199719:ℝ) (1/10:ℝ)) :
 GlobalSource (19499333800960761253812500000000000000000000000000/19556524757429402157525627494489318367687366409659:ℝ) (125000000000000000000000000000/50577348474550639178305583133:ℝ) (1/10:ℝ) := by
 have heps : 0<p175.toReal.eps := by norm_num [p175,Params.toReal]
 have hcap : p175.toReal.cap=1/10 := by norm_num [p175,Params.toReal]
 have hi : GlobalSource (p175.toReal.state (((cells175 0).2:ℝ)/(p175.den:ℝ))).B (p175.toReal.state (((cells175 0).2:ℝ)/(p175.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p175,cells175,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells175 0).1 < (cells175 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p175) hw0 heps hcap (commonSigns175 0) (highSigns175 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns175 0)
   (u:=((cells175 0).1:ℝ)/(p175.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p175.toReal.state (((cells175 0).1:ℝ)/(p175.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(50577348474550639178305583133/125000000000000000000000000000:ℝ)) (by norm_num [p175,cells175,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p175,cells175,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source176 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19499333800960761253812500000000000000000000000000/19556524757429402157525627494489318367687366409659:ℝ) (125000000000000000000000000000/50577348474550639178305583133:ℝ) (1/10:ℝ)) :
 GlobalSource (1523161941504059821728125000000000000000000000000/1527659973876890420832012479858899452870647470611:ℝ) (6250000000000000000000000000/2529445450175200403805867079:ℝ) (1/10:ℝ) := by
 have heps : 0<p176.toReal.eps := by norm_num [p176,Params.toReal]
 have hcap : p176.toReal.cap=1/10 := by norm_num [p176,Params.toReal]
 have hi : GlobalSource (p176.toReal.state (((cells176 0).2:ℝ)/(p176.den:ℝ))).B (p176.toReal.state (((cells176 0).2:ℝ)/(p176.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p176,cells176,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells176 0).1 < (cells176 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p176) hw0 heps hcap (commonSigns176 0) (highSigns176 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns176 0)
   (u:=((cells176 0).1:ℝ)/(p176.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p176.toReal.state (((cells176 0).1:ℝ)/(p176.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(2529445450175200403805867079/6250000000000000000000000000:ℝ)) (by norm_num [p176,cells176,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p176,cells176,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (975395832504357393044500000000000000000000000000000/978197994343937959248125948808361897625058414883779:ℝ) (1000000000000000000000000000000/404341808488926482469452664737:ℝ) (1/10:ℝ)) :
 GlobalSource (1523161941504059821728125000000000000000000000000/1527659973876890420832012479858899452870647470611:ℝ) (6250000000000000000000000000/2529445450175200403805867079:ℝ) (1/10:ℝ) := by
 have h173 := source173 hβ hp
 have h174 := source174 hβ h173
 have h175 := source175 hβ h174
 have h176 := source176 hβ h175
 exact h176
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0173_0176
