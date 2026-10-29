/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0321_0324
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0325_0328
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0329_0332
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0333_0336
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0321_0324
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0321_0324

theorem source321 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (392846500000000000000000000000000000/401001975700734720734842210504414119:ℝ) (1000000000000000000000000000000/467870494669376709422167863761:ℝ) (1/10:ℝ)) :
 GlobalSource (26173100000000000000000000000000000/26721602545657570815489199317916851:ℝ) (200000000000000000000000000000/93696558280384058569071468507:ℝ) (1/10:ℝ) := by
 have heps : 0<p321.toReal.eps := by norm_num [p321,Params.toReal]
 have hcap : p321.toReal.cap=1/10 := by norm_num [p321,Params.toReal]
 have hi : GlobalSource (p321.toReal.state (((cells321 0).2:ℝ)/(p321.den:ℝ))).B (p321.toReal.state (((cells321 0).2:ℝ)/(p321.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p321,cells321,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells321 0).1 < (cells321 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p321) hw0 heps hcap (commonSigns321 0) (highSigns321 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns321 0)
   (u:=((cells321 0).1:ℝ)/(p321.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p321.toReal.state (((cells321 0).1:ℝ)/(p321.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(93696558280384058569071468507/200000000000000000000000000000:ℝ)) (by norm_num [p321,cells321,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p321,cells321,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source322 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (26173100000000000000000000000000000/26721602545657570815489199317916851:ℝ) (200000000000000000000000000000/93696558280384058569071468507:ℝ) (1/10:ℝ)) :
 GlobalSource (49043312500000000000000000000000000/50080802260869859406629819470075423:ℝ) (125000000000000000000000000000/58637201313777600674679765537:ℝ) (1/10:ℝ) := by
 have heps : 0<p322.toReal.eps := by norm_num [p322,Params.toReal]
 have hcap : p322.toReal.cap=1/10 := by norm_num [p322,Params.toReal]
 have hi : GlobalSource (p322.toReal.state (((cells322 0).2:ℝ)/(p322.den:ℝ))).B (p322.toReal.state (((cells322 0).2:ℝ)/(p322.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p322,cells322,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells322 0).1 < (cells322 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p322) hw0 heps hcap (commonSigns322 0) (highSigns322 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns322 0)
   (u:=((cells322 0).1:ℝ)/(p322.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p322.toReal.state (((cells322 0).1:ℝ)/(p322.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(58637201313777600674679765537/125000000000000000000000000000:ℝ)) (by norm_num [p322,cells322,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p322,cells322,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source323 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (49043312500000000000000000000000000/50080802260869859406629819470075423:ℝ) (125000000000000000000000000000/58637201313777600674679765537:ℝ) (1/10:ℝ)) :
 GlobalSource (78419300000000000000000000000000000/80093823172173638173675707318570357:ℝ) (200000000000000000000000000000/93942993167992219106588019783:ℝ) (1/10:ℝ) := by
 have heps : 0<p323.toReal.eps := by norm_num [p323,Params.toReal]
 have hcap : p323.toReal.cap=1/10 := by norm_num [p323,Params.toReal]
 have hi : GlobalSource (p323.toReal.state (((cells323 0).2:ℝ)/(p323.den:ℝ))).B (p323.toReal.state (((cells323 0).2:ℝ)/(p323.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p323,cells323,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells323 0).1 < (cells323 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p323) hw0 heps hcap (commonSigns323 0) (highSigns323 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns323 0)
   (u:=((cells323 0).1:ℝ)/(p323.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p323.toReal.state (((cells323 0).1:ℝ)/(p323.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(93942993167992219106588019783/200000000000000000000000000000:ℝ)) (by norm_num [p323,cells323,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p323,cells323,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source324 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (78419300000000000000000000000000000/80093823172173638173675707318570357:ℝ) (200000000000000000000000000000/93942993167992219106588019783:ℝ) (1/10:ℝ)) :
 GlobalSource (6874500000000000000000000000000000/7022668981786093035241743856508501:ℝ) (1000000000000000000000000000000/470334871336042016086379055083:ℝ) (1/10:ℝ) := by
 have heps : 0<p324.toReal.eps := by norm_num [p324,Params.toReal]
 have hcap : p324.toReal.cap=1/10 := by norm_num [p324,Params.toReal]
 have hi : GlobalSource (p324.toReal.state (((cells324 0).2:ℝ)/(p324.den:ℝ))).B (p324.toReal.state (((cells324 0).2:ℝ)/(p324.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p324,cells324,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells324 0).1 < (cells324 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p324) hw0 heps hcap (commonSigns324 0) (highSigns324 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns324 0)
   (u:=((cells324 0).1:ℝ)/(p324.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p324.toReal.state (((cells324 0).1:ℝ)/(p324.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(470334871336042016086379055083/1000000000000000000000000000000:ℝ)) (by norm_num [p324,cells324,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p324,cells324,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (392846500000000000000000000000000000/401001975700734720734842210504414119:ℝ) (1000000000000000000000000000000/467870494669376709422167863761:ℝ) (1/10:ℝ)) :
 GlobalSource (6874500000000000000000000000000000/7022668981786093035241743856508501:ℝ) (1000000000000000000000000000000/470334871336042016086379055083:ℝ) (1/10:ℝ) := by
 have h321 := source321 hβ hp
 have h322 := source322 hβ h321
 have h323 := source323 hβ h322
 have h324 := source324 hβ h323
 exact h324
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0321_0324
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0325_0328
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0325_0328

theorem source325 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (6874500000000000000000000000000000/7022668981786093035241743856508501:ℝ) (1000000000000000000000000000000/470334871336042016086379055083:ℝ) (1/10:ℝ)) :
 GlobalSource (391596500000000000000000000000000000/400115466846367937038636130442823743:ℝ) (1000000000000000000000000000000/470957341043467337397271037117:ℝ) (1/10:ℝ) := by
 have heps : 0<p325.toReal.eps := by norm_num [p325,Params.toReal]
 have hcap : p325.toReal.cap=1/10 := by norm_num [p325,Params.toReal]
 have hi : GlobalSource (p325.toReal.state (((cells325 0).2:ℝ)/(p325.den:ℝ))).B (p325.toReal.state (((cells325 0).2:ℝ)/(p325.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p325,cells325,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells325 0).1 < (cells325 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p325) hw0 heps hcap (commonSigns325 0) (highSigns325 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns325 0)
   (u:=((cells325 0).1:ℝ)/(p325.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p325.toReal.state (((cells325 0).1:ℝ)/(p325.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(470957341043467337397271037117/1000000000000000000000000000000:ℝ)) (by norm_num [p325,cells325,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p325,cells325,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source326 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (391596500000000000000000000000000000/400115466846367937038636130442823743:ℝ) (1000000000000000000000000000000/470957341043467337397271037117:ℝ) (1/10:ℝ)) :
 GlobalSource (391346500000000000000000000000000000/399939120972525502727150010891701139:ℝ) (1000000000000000000000000000000/471582389108238150841077318141:ℝ) (1/10:ℝ) := by
 have heps : 0<p326.toReal.eps := by norm_num [p326,Params.toReal]
 have hcap : p326.toReal.cap=1/10 := by norm_num [p326,Params.toReal]
 have hi : GlobalSource (p326.toReal.state (((cells326 0).2:ℝ)/(p326.den:ℝ))).B (p326.toReal.state (((cells326 0).2:ℝ)/(p326.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p326,cells326,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells326 0).1 < (cells326 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p326) hw0 heps hcap (commonSigns326 0) (highSigns326 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns326 0)
   (u:=((cells326 0).1:ℝ)/(p326.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p326.toReal.state (((cells326 0).1:ℝ)/(p326.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(471582389108238150841077318141/1000000000000000000000000000000:ℝ)) (by norm_num [p326,cells326,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p326,cells326,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source327 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (391346500000000000000000000000000000/399939120972525502727150010891701139:ℝ) (1000000000000000000000000000000/471582389108238150841077318141:ℝ) (1/10:ℝ)) :
 GlobalSource (32591375000000000000000000000000000/33313591233303911102873148484181619:ℝ) (250000000000000000000000000000/118052507444564220596801297283:ℝ) (1/10:ℝ) := by
 have heps : 0<p327.toReal.eps := by norm_num [p327,Params.toReal]
 have hcap : p327.toReal.cap=1/10 := by norm_num [p327,Params.toReal]
 have hi : GlobalSource (p327.toReal.state (((cells327 0).2:ℝ)/(p327.den:ℝ))).B (p327.toReal.state (((cells327 0).2:ℝ)/(p327.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p327,cells327,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells327 0).1 < (cells327 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p327) hw0 heps hcap (commonSigns327 0) (highSigns327 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns327 0)
   (u:=((cells327 0).1:ℝ)/(p327.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p327.toReal.state (((cells327 0).1:ℝ)/(p327.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(118052507444564220596801297283/250000000000000000000000000000:ℝ)) (by norm_num [p327,cells327,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p327,cells327,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source328 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (32591375000000000000000000000000000/33313591233303911102873148484181619:ℝ) (250000000000000000000000000000/118052507444564220596801297283:ℝ) (1/10:ℝ)) :
 GlobalSource (390846500000000000000000000000000000/399587388788498611775912643165857913:ℝ) (1000000000000000000000000000000/472840277404241037554965444847:ℝ) (1/10:ℝ) := by
 have heps : 0<p328.toReal.eps := by norm_num [p328,Params.toReal]
 have hcap : p328.toReal.cap=1/10 := by norm_num [p328,Params.toReal]
 have hi : GlobalSource (p328.toReal.state (((cells328 0).2:ℝ)/(p328.den:ℝ))).B (p328.toReal.state (((cells328 0).2:ℝ)/(p328.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p328,cells328,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells328 0).1 < (cells328 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p328) hw0 heps hcap (commonSigns328 0) (highSigns328 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns328 0)
   (u:=((cells328 0).1:ℝ)/(p328.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p328.toReal.state (((cells328 0).1:ℝ)/(p328.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(472840277404241037554965444847/1000000000000000000000000000000:ℝ)) (by norm_num [p328,cells328,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p328,cells328,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (6874500000000000000000000000000000/7022668981786093035241743856508501:ℝ) (1000000000000000000000000000000/470334871336042016086379055083:ℝ) (1/10:ℝ)) :
 GlobalSource (390846500000000000000000000000000000/399587388788498611775912643165857913:ℝ) (1000000000000000000000000000000/472840277404241037554965444847:ℝ) (1/10:ℝ) := by
 have h325 := source325 hβ hp
 have h326 := source326 hβ h325
 have h327 := source327 hβ h326
 have h328 := source328 hβ h327
 exact h328
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0325_0328
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0329_0332
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0329_0332

theorem source329 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (390846500000000000000000000000000000/399587388788498611775912643165857913:ℝ) (1000000000000000000000000000000/472840277404241037554965444847:ℝ) (1/10:ℝ)) :
 GlobalSource (3124772000000000000000000000000000/3195296027210035101371709736865853:ℝ) (8000000000000000000000000000/3787785171525174407342655207:ℝ) (1/10:ℝ) := by
 have heps : 0<p329.toReal.eps := by norm_num [p329,Params.toReal]
 have hcap : p329.toReal.cap=1/10 := by norm_num [p329,Params.toReal]
 have hi : GlobalSource (p329.toReal.state (((cells329 0).2:ℝ)/(p329.den:ℝ))).B (p329.toReal.state (((cells329 0).2:ℝ)/(p329.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p329,cells329,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells329 0).1 < (cells329 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p329) hw0 heps hcap (commonSigns329 0) (highSigns329 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns329 0)
   (u:=((cells329 0).1:ℝ)/(p329.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p329.toReal.state (((cells329 0).1:ℝ)/(p329.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(3787785171525174407342655207/8000000000000000000000000000:ℝ)) (by norm_num [p329,cells329,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p329,cells329,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source330 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3124772000000000000000000000000000/3195296027210035101371709736865853:ℝ) (8000000000000000000000000000/3787785171525174407342655207:ℝ) (1/10:ℝ)) :
 GlobalSource (130115500000000000000000000000000000/133078979700501227844770138164245607:ℝ) (1000000000000000000000000000000/474108651446602615116052549099:ℝ) (1/10:ℝ) := by
 have heps : 0<p330.toReal.eps := by norm_num [p330,Params.toReal]
 have hcap : p330.toReal.cap=1/10 := by norm_num [p330,Params.toReal]
 have hi : GlobalSource (p330.toReal.state (((cells330 0).2:ℝ)/(p330.den:ℝ))).B (p330.toReal.state (((cells330 0).2:ℝ)/(p330.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p330,cells330,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells330 0).1 < (cells330 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p330) hw0 heps hcap (commonSigns330 0) (highSigns330 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns330 0)
   (u:=((cells330 0).1:ℝ)/(p330.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p330.toReal.state (((cells330 0).1:ℝ)/(p330.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(474108651446602615116052549099/1000000000000000000000000000000:ℝ)) (by norm_num [p330,cells330,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p330,cells330,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source331 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (130115500000000000000000000000000000/133078979700501227844770138164245607:ℝ) (1000000000000000000000000000000/474108651446602615116052549099:ℝ) (1/10:ℝ)) :
 GlobalSource (390096500000000000000000000000000000/399062196354259695399231523900321779:ℝ) (1000000000000000000000000000000/474746807086852866178231342801:ℝ) (1/10:ℝ) := by
 have heps : 0<p331.toReal.eps := by norm_num [p331,Params.toReal]
 have hcap : p331.toReal.cap=1/10 := by norm_num [p331,Params.toReal]
 have hi : GlobalSource (p331.toReal.state (((cells331 0).2:ℝ)/(p331.den:ℝ))).B (p331.toReal.state (((cells331 0).2:ℝ)/(p331.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p331,cells331,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells331 0).1 < (cells331 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p331) hw0 heps hcap (commonSigns331 0) (highSigns331 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns331 0)
   (u:=((cells331 0).1:ℝ)/(p331.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p331.toReal.state (((cells331 0).1:ℝ)/(p331.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(474746807086852866178231342801/1000000000000000000000000000000:ℝ)) (by norm_num [p331,cells331,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p331,cells331,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source332 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (390096500000000000000000000000000000/399062196354259695399231523900321779:ℝ) (1000000000000000000000000000000/474746807086852866178231342801:ℝ) (1/10:ℝ)) :
 GlobalSource (389846500000000000000000000000000000/398887775625967687641302996974152291:ℝ) (1000000000000000000000000000000/475387628132711803824554061029:ℝ) (1/10:ℝ) := by
 have heps : 0<p332.toReal.eps := by norm_num [p332,Params.toReal]
 have hcap : p332.toReal.cap=1/10 := by norm_num [p332,Params.toReal]
 have hi : GlobalSource (p332.toReal.state (((cells332 0).2:ℝ)/(p332.den:ℝ))).B (p332.toReal.state (((cells332 0).2:ℝ)/(p332.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p332,cells332,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells332 0).1 < (cells332 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p332) hw0 heps hcap (commonSigns332 0) (highSigns332 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns332 0)
   (u:=((cells332 0).1:ℝ)/(p332.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p332.toReal.state (((cells332 0).1:ℝ)/(p332.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(475387628132711803824554061029/1000000000000000000000000000000:ℝ)) (by norm_num [p332,cells332,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p332,cells332,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (390846500000000000000000000000000000/399587388788498611775912643165857913:ℝ) (1000000000000000000000000000000/472840277404241037554965444847:ℝ) (1/10:ℝ)) :
 GlobalSource (389846500000000000000000000000000000/398887775625967687641302996974152291:ℝ) (1000000000000000000000000000000/475387628132711803824554061029:ℝ) (1/10:ℝ) := by
 have h329 := source329 hβ hp
 have h330 := source330 hβ h329
 have h331 := source331 hβ h330
 have h332 := source332 hβ h331
 exact h332
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0329_0332
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0333_0336
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0333_0336

theorem source333 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (389846500000000000000000000000000000/398887775625967687641302996974152291:ℝ) (1000000000000000000000000000000/475387628132711803824554061029:ℝ) (1/10:ℝ)) :
 GlobalSource (21644250000000000000000000000000000/22150759854695188032554610654516749:ℝ) (500000000000000000000000000000/238015564731513913664253158079:ℝ) (1/10:ℝ) := by
 have heps : 0<p333.toReal.eps := by norm_num [p333,Params.toReal]
 have hcap : p333.toReal.cap=1/10 := by norm_num [p333,Params.toReal]
 have hi : GlobalSource (p333.toReal.state (((cells333 0).2:ℝ)/(p333.den:ℝ))).B (p333.toReal.state (((cells333 0).2:ℝ)/(p333.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p333,cells333,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells333 0).1 < (cells333 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p333) hw0 heps hcap (commonSigns333 0) (highSigns333 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns333 0)
   (u:=((cells333 0).1:ℝ)/(p333.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p333.toReal.state (((cells333 0).1:ℝ)/(p333.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(238015564731513913664253158079/500000000000000000000000000000:ℝ)) (by norm_num [p333,cells333,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p333,cells333,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source334 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (21644250000000000000000000000000000/22150759854695188032554610654516749:ℝ) (500000000000000000000000000000/238015564731513913664253158079:ℝ) (1/10:ℝ)) :
 GlobalSource (15573860000000000000000000000000000/15941596083969258430568798375903397:ℝ) (40000000000000000000000000000/19067093042606330778035088043:ℝ) (1/10:ℝ) := by
 have heps : 0<p334.toReal.eps := by norm_num [p334,Params.toReal]
 have hcap : p334.toReal.cap=1/10 := by norm_num [p334,Params.toReal]
 have hi : GlobalSource (p334.toReal.state (((cells334 0).2:ℝ)/(p334.den:ℝ))).B (p334.toReal.state (((cells334 0).2:ℝ)/(p334.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p334,cells334,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells334 0).1 < (cells334 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p334) hw0 heps hcap (commonSigns334 0) (highSigns334 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns334 0)
   (u:=((cells334 0).1:ℝ)/(p334.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p334.toReal.state (((cells334 0).1:ℝ)/(p334.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(19067093042606330778035088043/40000000000000000000000000000:ℝ)) (by norm_num [p334,cells334,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p334,cells334,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source335 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (15573860000000000000000000000000000/15941596083969258430568798375903397:ℝ) (40000000000000000000000000000/19067093042606330778035088043:ℝ) (1/10:ℝ)) :
 GlobalSource (19454825000000000000000000000000000/19918322512045706591024714472506913:ℝ) (50000000000000000000000000000/23866311651797740646511252347:ℝ) (1/10:ℝ) := by
 have heps : 0<p335.toReal.eps := by norm_num [p335,Params.toReal]
 have hcap : p335.toReal.cap=1/10 := by norm_num [p335,Params.toReal]
 have hi : GlobalSource (p335.toReal.state (((cells335 0).2:ℝ)/(p335.den:ℝ))).B (p335.toReal.state (((cells335 0).2:ℝ)/(p335.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p335,cells335,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells335 0).1 < (cells335 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p335) hw0 heps hcap (commonSigns335 0) (highSigns335 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns335 0)
   (u:=((cells335 0).1:ℝ)/(p335.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p335.toReal.state (((cells335 0).1:ℝ)/(p335.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(23866311651797740646511252347/50000000000000000000000000000:ℝ)) (by norm_num [p335,cells335,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p335,cells335,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source336 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19454825000000000000000000000000000/19918322512045706591024714472506913:ℝ) (50000000000000000000000000000/23866311651797740646511252347:ℝ) (1/10:ℝ)) :
 GlobalSource (129615500000000000000000000000000000/132731107427273282712601311684141901:ℝ) (1000000000000000000000000000000/477977865582759676018485563857:ℝ) (1/10:ℝ) := by
 have heps : 0<p336.toReal.eps := by norm_num [p336,Params.toReal]
 have hcap : p336.toReal.cap=1/10 := by norm_num [p336,Params.toReal]
 have hi : GlobalSource (p336.toReal.state (((cells336 0).2:ℝ)/(p336.den:ℝ))).B (p336.toReal.state (((cells336 0).2:ℝ)/(p336.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p336,cells336,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells336 0).1 < (cells336 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p336) hw0 heps hcap (commonSigns336 0) (highSigns336 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns336 0)
   (u:=((cells336 0).1:ℝ)/(p336.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p336.toReal.state (((cells336 0).1:ℝ)/(p336.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(477977865582759676018485563857/1000000000000000000000000000000:ℝ)) (by norm_num [p336,cells336,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p336,cells336,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem prefix0333 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (389846500000000000000000000000000000/398887775625967687641302996974152291:ℝ) (1000000000000000000000000000000/475387628132711803824554061029:ℝ) (1/10:ℝ)) :
 GlobalSource (21644250000000000000000000000000000/22150759854695188032554610654516749:ℝ) (500000000000000000000000000000/238015564731513913664253158079:ℝ) (1/10:ℝ) := by
 have h333 := source333 hβ hp
 exact h333

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (389846500000000000000000000000000000/398887775625967687641302996974152291:ℝ) (1000000000000000000000000000000/475387628132711803824554061029:ℝ) (1/10:ℝ)) :
 GlobalSource (129615500000000000000000000000000000/132731107427273282712601311684141901:ℝ) (1000000000000000000000000000000/477977865582759676018485563857:ℝ) (1/10:ℝ) := by
 have h333 := source333 hβ hp
 have h334 := source334 hβ h333
 have h335 := source335 hβ h334
 have h336 := source336 hβ h335
 exact h336
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0333_0336
