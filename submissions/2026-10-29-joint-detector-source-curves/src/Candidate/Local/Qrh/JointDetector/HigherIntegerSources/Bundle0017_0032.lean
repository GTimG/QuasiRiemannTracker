/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0017_0020
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0021_0024
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0025_0028
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0029_0032
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0017_0020
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0017_0020

theorem source17 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (249427810058240642861500000000000000000000000000000/249482745871424222346616694579569159348819328087937:ℝ) (1000000000000000000000000000000/390866053420751406423907382723:ℝ) (1/10:ℝ)) :
 GlobalSource (3990272770990091178645500000000000000000000000000000/3991207810024625266069690875386847017603289994803519:ℝ) (1000000000000000000000000000000/390946939650239859562394526303:ℝ) (1/10:ℝ) := by
 have heps : 0<p17.toReal.eps := by norm_num [p17,Params.toReal]
 have hcap : p17.toReal.cap=1/10 := by norm_num [p17,Params.toReal]
 have hi : GlobalSource (p17.toReal.state (((cells17 0).2:ℝ)/(p17.den:ℝ))).B (p17.toReal.state (((cells17 0).2:ℝ)/(p17.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p17,cells17,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells17 0).1 < (cells17 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p17) hw0 heps hcap (commonSigns17 0) (highSigns17 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns17 0)
   (u:=((cells17 0).1:ℝ)/(p17.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p17.toReal.state (((cells17 0).1:ℝ)/(p17.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(390946939650239859562394526303/1000000000000000000000000000000:ℝ)) (by norm_num [p17,cells17,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p17,cells17,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source18 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3990272770990091178645500000000000000000000000000000/3991207810024625266069690875386847017603289994803519:ℝ) (1000000000000000000000000000000/390946939650239859562394526303:ℝ) (1/10:ℝ)) :
 GlobalSource (166237524210347169646125000000000000000000000000000/166278825784135680681921129030197628398474641237871:ℝ) (250000000000000000000000000000/97756973325805579052032830053:ℝ) (1/10:ℝ) := by
 have heps : 0<p18.toReal.eps := by norm_num [p18,Params.toReal]
 have hcap : p18.toReal.cap=1/10 := by norm_num [p18,Params.toReal]
 have hi : GlobalSource (p18.toReal.state (((cells18 0).2:ℝ)/(p18.den:ℝ))).B (p18.toReal.state (((cells18 0).2:ℝ)/(p18.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p18,cells18,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells18 0).1 < (cells18 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p18) hw0 heps hcap (commonSigns18 0) (highSigns18 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns18 0)
   (u:=((cells18 0).1:ℝ)/(p18.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p18.toReal.state (((cells18 0).1:ℝ)/(p18.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(97756973325805579052032830053/250000000000000000000000000000:ℝ)) (by norm_num [p18,cells18,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p18,cells18,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source19 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (166237524210347169646125000000000000000000000000000/166278825784135680681921129030197628398474641237871:ℝ) (250000000000000000000000000000/97756973325805579052032830053:ℝ) (1/10:ℝ)) :
 GlobalSource (79782567822131459287370000000000000000000000000000/79803519205708695251258719703712577090009475779767:ℝ) (20000000000000000000000000000/7822178288874436710381262397:ℝ) (1/10:ℝ) := by
 have heps : 0<p19.toReal.eps := by norm_num [p19,Params.toReal]
 have hcap : p19.toReal.cap=1/10 := by norm_num [p19,Params.toReal]
 have hi : GlobalSource (p19.toReal.state (((cells19 0).2:ℝ)/(p19.den:ℝ))).B (p19.toReal.state (((cells19 0).2:ℝ)/(p19.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p19,cells19,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells19 0).1 < (cells19 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p19) hw0 heps hcap (commonSigns19 0) (highSigns19 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns19 0)
   (u:=((cells19 0).1:ℝ)/(p19.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p19.toReal.state (((cells19 0).1:ℝ)/(p19.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(7822178288874436710381262397/20000000000000000000000000000:ℝ)) (by norm_num [p19,cells19,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p19,cells19,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source20 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (79782567822131459287370000000000000000000000000000/79803519205708695251258719703712577090009475779767:ℝ) (20000000000000000000000000000/7822178288874436710381262397:ℝ) (1/10:ℝ)) :
 GlobalSource (24928476257280086607687500000000000000000000000000/24935376464888199928047048365441255425990385858949:ℝ) (125000000000000000000000000000/48898750391983380403330869421:ℝ) (1/10:ℝ) := by
 have heps : 0<p20.toReal.eps := by norm_num [p20,Params.toReal]
 have hcap : p20.toReal.cap=1/10 := by norm_num [p20,Params.toReal]
 have hi : GlobalSource (p20.toReal.state (((cells20 0).2:ℝ)/(p20.den:ℝ))).B (p20.toReal.state (((cells20 0).2:ℝ)/(p20.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p20,cells20,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells20 0).1 < (cells20 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p20) hw0 heps hcap (commonSigns20 0) (highSigns20 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns20 0)
   (u:=((cells20 0).1:ℝ)/(p20.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p20.toReal.state (((cells20 0).1:ℝ)/(p20.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(48898750391983380403330869421/125000000000000000000000000000:ℝ)) (by norm_num [p20,cells20,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p20,cells20,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (249427810058240642861500000000000000000000000000000/249482745871424222346616694579569159348819328087937:ℝ) (1000000000000000000000000000000/390866053420751406423907382723:ℝ) (1/10:ℝ)) :
 GlobalSource (24928476257280086607687500000000000000000000000000/24935376464888199928047048365441255425990385858949:ℝ) (125000000000000000000000000000/48898750391983380403330869421:ℝ) (1/10:ℝ) := by
 have h17 := source17 hβ hp
 have h18 := source18 hβ h17
 have h19 := source19 hβ h18
 have h20 := source20 hβ h19
 exact h20
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0017_0020
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0021_0024
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0021_0024

theorem source21 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24928476257280086607687500000000000000000000000000/24935376464888199928047048365441255425990385858949:ℝ) (125000000000000000000000000000/48898750391983380403330869421:ℝ) (1/10:ℝ)) :
 GlobalSource (1329328003741018250030500000000000000000000000000000/1329714880356145535738964730221293558850575012834627:ℝ) (1000000000000000000000000000000/391271159443892279906852578069:ℝ) (1/10:ℝ) := by
 have heps : 0<p21.toReal.eps := by norm_num [p21,Params.toReal]
 have hcap : p21.toReal.cap=1/10 := by norm_num [p21,Params.toReal]
 have hi : GlobalSource (p21.toReal.state (((cells21 0).2:ℝ)/(p21.den:ℝ))).B (p21.toReal.state (((cells21 0).2:ℝ)/(p21.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p21,cells21,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells21 0).1 < (cells21 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p21) hw0 heps hcap (commonSigns21 0) (highSigns21 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns21 0)
   (u:=((cells21 0).1:ℝ)/(p21.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p21.toReal.state (((cells21 0).1:ℝ)/(p21.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(391271159443892279906852578069/1000000000000000000000000000000:ℝ)) (by norm_num [p21,cells21,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p21,cells21,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source22 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1329328003741018250030500000000000000000000000000000/1329714880356145535738964730221293558850575012834627:ℝ) (1000000000000000000000000000000/391271159443892279906852578069:ℝ) (1/10:ℝ)) :
 GlobalSource (1993705910640647821476500000000000000000000000000000/1994314590151877030469595917024733045397805995035551:ℝ) (1000000000000000000000000000000/391352383432137749581382368989:ℝ) (1/10:ℝ) := by
 have heps : 0<p22.toReal.eps := by norm_num [p22,Params.toReal]
 have hcap : p22.toReal.cap=1/10 := by norm_num [p22,Params.toReal]
 have hi : GlobalSource (p22.toReal.state (((cells22 0).2:ℝ)/(p22.den:ℝ))).B (p22.toReal.state (((cells22 0).2:ℝ)/(p22.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p22,cells22,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells22 0).1 < (cells22 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p22) hw0 heps hcap (commonSigns22 0) (highSigns22 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns22 0)
   (u:=((cells22 0).1:ℝ)/(p22.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p22.toReal.state (((cells22 0).1:ℝ)/(p22.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(391352383432137749581382368989/1000000000000000000000000000000:ℝ)) (by norm_num [p22,cells22,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p22,cells22,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source23 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1993705910640647821476500000000000000000000000000000/1994314590151877030469595917024733045397805995035551:ℝ) (1000000000000000000000000000000/391352383432137749581382368989:ℝ) (1/10:ℝ)) :
 GlobalSource (3986839631339536535814500000000000000000000000000000/3988113852047606340720141323580370220502528726221091:ℝ) (1000000000000000000000000000000/391433675165049668609999357893:ℝ) (1/10:ℝ) := by
 have heps : 0<p23.toReal.eps := by norm_num [p23,Params.toReal]
 have hcap : p23.toReal.cap=1/10 := by norm_num [p23,Params.toReal]
 have hi : GlobalSource (p23.toReal.state (((cells23 0).2:ℝ)/(p23.den:ℝ))).B (p23.toReal.state (((cells23 0).2:ℝ)/(p23.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p23,cells23,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells23 0).1 < (cells23 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p23) hw0 heps hcap (commonSigns23 0) (highSigns23 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns23 0)
   (u:=((cells23 0).1:ℝ)/(p23.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p23.toReal.state (((cells23 0).1:ℝ)/(p23.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(391433675165049668609999357893/1000000000000000000000000000000:ℝ)) (by norm_num [p23,cells23,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p23,cells23,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source24 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3986839631339536535814500000000000000000000000000000/3988113852047606340720141323580370220502528726221091:ℝ) (1000000000000000000000000000000/391433675165049668609999357893:ℝ) (1/10:ℝ)) :
 GlobalSource (5190452397653356026921875000000000000000000000000/5192185750338192300304732542674959943884817567299:ℝ) (31250000000000000000000000000/12234844834599387966243132271:ℝ) (1/10:ℝ) := by
 have heps : 0<p24.toReal.eps := by norm_num [p24,Params.toReal]
 have hcap : p24.toReal.cap=1/10 := by norm_num [p24,Params.toReal]
 have hi : GlobalSource (p24.toReal.state (((cells24 0).2:ℝ)/(p24.den:ℝ))).B (p24.toReal.state (((cells24 0).2:ℝ)/(p24.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p24,cells24,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells24 0).1 < (cells24 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p24) hw0 heps hcap (commonSigns24 0) (highSigns24 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns24 0)
   (u:=((cells24 0).1:ℝ)/(p24.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p24.toReal.state (((cells24 0).1:ℝ)/(p24.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(12234844834599387966243132271/31250000000000000000000000000:ℝ)) (by norm_num [p24,cells24,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p24,cells24,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24928476257280086607687500000000000000000000000000/24935376464888199928047048365441255425990385858949:ℝ) (125000000000000000000000000000/48898750391983380403330869421:ℝ) (1/10:ℝ)) :
 GlobalSource (5190452397653356026921875000000000000000000000000/5192185750338192300304732542674959943884817567299:ℝ) (31250000000000000000000000000/12234844834599387966243132271:ℝ) (1/10:ℝ) := by
 have h21 := source21 hβ hp
 have h22 := source22 hβ h21
 have h23 := source23 hβ h22
 have h24 := source24 hβ h23
 exact h24
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0021_0024
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0025_0028
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0025_0028

theorem source25 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (5190452397653356026921875000000000000000000000000/5192185750338192300304732542674959943884817567299:ℝ) (31250000000000000000000000000/12234844834599387966243132271:ℝ) (1/10:ℝ)) :
 GlobalSource (15942781005824073286150000000000000000000000000000/15948334371600257151451517848987078315616333041269:ℝ) (100000000000000000000000000000/39159646212318867753315074341:ℝ) (1/10:ℝ) := by
 have heps : 0<p25.toReal.eps := by norm_num [p25,Params.toReal]
 have hcap : p25.toReal.cap=1/10 := by norm_num [p25,Params.toReal]
 have hi : GlobalSource (p25.toReal.state (((cells25 0).2:ℝ)/(p25.den:ℝ))).B (p25.toReal.state (((cells25 0).2:ℝ)/(p25.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p25,cells25,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells25 0).1 < (cells25 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p25) hw0 heps hcap (commonSigns25 0) (highSigns25 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns25 0)
   (u:=((cells25 0).1:ℝ)/(p25.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p25.toReal.state (((cells25 0).1:ℝ)/(p25.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(39159646212318867753315074341/100000000000000000000000000000:ℝ)) (by norm_num [p25,cells25,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p25,cells25,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source26 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (15942781005824073286150000000000000000000000000000/15948334371600257151451517848987078315616333041269:ℝ) (100000000000000000000000000000/39159646212318867753315074341:ℝ) (1/10:ℝ)) :
 GlobalSource (1992561530757129607199500000000000000000000000000000/1993284330964366991538058914466908826498680558800193:ℝ) (1000000000000000000000000000000/391677957477839606426105620869:ℝ) (1/10:ℝ) := by
 have heps : 0<p26.toReal.eps := by norm_num [p26,Params.toReal]
 have hcap : p26.toReal.cap=1/10 := by norm_num [p26,Params.toReal]
 have hi : GlobalSource (p26.toReal.state (((cells26 0).2:ℝ)/(p26.den:ℝ))).B (p26.toReal.state (((cells26 0).2:ℝ)/(p26.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p26,cells26,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells26 0).1 < (cells26 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p26) hw0 heps hcap (commonSigns26 0) (highSigns26 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns26 0)
   (u:=((cells26 0).1:ℝ)/(p26.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p26.toReal.state (((cells26 0).1:ℝ)/(p26.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(391677957477839606426105620869/1000000000000000000000000000000:ℝ)) (by norm_num [p26,cells26,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p26,cells26,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source27 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1992561530757129607199500000000000000000000000000000/1993284330964366991538058914466908826498680558800193:ℝ) (1000000000000000000000000000000/391677957477839606426105620869:ℝ) (1/10:ℝ)) :
 GlobalSource (1328183623857500035753500000000000000000000000000000/1328684621102021986961521074649627181840125287407909:ℝ) (1000000000000000000000000000000/391759520836004962697111862829:ℝ) (1/10:ℝ) := by
 have heps : 0<p27.toReal.eps := by norm_num [p27,Params.toReal]
 have hcap : p27.toReal.cap=1/10 := by norm_num [p27,Params.toReal]
 have hi : GlobalSource (p27.toReal.state (((cells27 0).2:ℝ)/(p27.den:ℝ))).B (p27.toReal.state (((cells27 0).2:ℝ)/(p27.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p27,cells27,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells27 0).1 < (cells27 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p27) hw0 heps hcap (commonSigns27 0) (highSigns27 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns27 0)
   (u:=((cells27 0).1:ℝ)/(p27.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p27.toReal.state (((cells27 0).1:ℝ)/(p27.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(391759520836004962697111862829/1000000000000000000000000000000:ℝ)) (by norm_num [p27,cells27,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p27,cells27,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source28 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1328183623857500035753500000000000000000000000000000/1328684621102021986961521074649627181840125287407909:ℝ) (1000000000000000000000000000000/391759520836004962697111862829:ℝ) (1/10:ℝ)) :
 GlobalSource (995994670407685250030500000000000000000000000000000/996384799248145115156210239359985609310584640958429:ℝ) (1000000000000000000000000000000/391841152262663269072626115363:ℝ) (1/10:ℝ) := by
 have heps : 0<p28.toReal.eps := by norm_num [p28,Params.toReal]
 have hcap : p28.toReal.cap=1/10 := by norm_num [p28,Params.toReal]
 have hi : GlobalSource (p28.toReal.state (((cells28 0).2:ℝ)/(p28.den:ℝ))).B (p28.toReal.state (((cells28 0).2:ℝ)/(p28.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p28,cells28,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells28 0).1 < (cells28 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p28) hw0 heps hcap (commonSigns28 0) (highSigns28 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns28 0)
   (u:=((cells28 0).1:ℝ)/(p28.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p28.toReal.state (((cells28 0).1:ℝ)/(p28.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(391841152262663269072626115363/1000000000000000000000000000000:ℝ)) (by norm_num [p28,cells28,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p28,cells28,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (5190452397653356026921875000000000000000000000000/5192185750338192300304732542674959943884817567299:ℝ) (31250000000000000000000000000/12234844834599387966243132271:ℝ) (1/10:ℝ)) :
 GlobalSource (995994670407685250030500000000000000000000000000000/996384799248145115156210239359985609310584640958429:ℝ) (1000000000000000000000000000000/391841152262663269072626115363:ℝ) (1/10:ℝ) := by
 have h25 := source25 hβ hp
 have h26 := source26 hβ h25
 have h27 := source27 hβ h26
 have h28 := source28 hβ h27
 exact h28
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0025_0028
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0029_0032
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0029_0032

theorem source29 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (995994670407685250030500000000000000000000000000000/996384799248145115156210239359985609310584640958429:ℝ) (1000000000000000000000000000000/391841152262663269072626115363:ℝ) (1/10:ℝ)) :
 GlobalSource (3983406491688981892983500000000000000000000000000000/3985024662948992473082927384127594021482972528071491:ℝ) (1000000000000000000000000000000/391922851822899960711527636591:ℝ) (1/10:ℝ) := by
 have heps : 0<p29.toReal.eps := by norm_num [p29,Params.toReal]
 have hcap : p29.toReal.cap=1/10 := by norm_num [p29,Params.toReal]
 have hi : GlobalSource (p29.toReal.state (((cells29 0).2:ℝ)/(p29.den:ℝ))).B (p29.toReal.state (((cells29 0).2:ℝ)/(p29.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p29,cells29,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells29 0).1 < (cells29 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p29) hw0 heps hcap (commonSigns29 0) (highSigns29 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns29 0)
   (u:=((cells29 0).1:ℝ)/(p29.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p29.toReal.state (((cells29 0).1:ℝ)/(p29.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(391922851822899960711527636591/1000000000000000000000000000000:ℝ)) (by norm_num [p29,cells29,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p29,cells29,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source30 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3983406491688981892983500000000000000000000000000000/3985024662948992473082927384127594021482972528071491:ℝ) (1000000000000000000000000000000/391922851822899960711527636591:ℝ) (1/10:ℝ)) :
 GlobalSource (132761143391574092861500000000000000000000000000000/132817008704540381386128197061593848308135223785579:ℝ) (1000000000000000000000000000000/392004619581907536351188414091:ℝ) (1/10:ℝ) := by
 have heps : 0<p30.toReal.eps := by norm_num [p30,Params.toReal]
 have hcap : p30.toReal.cap=1/10 := by norm_num [p30,Params.toReal]
 have hi : GlobalSource (p30.toReal.state (((cells30 0).2:ℝ)/(p30.den:ℝ))).B (p30.toReal.state (((cells30 0).2:ℝ)/(p30.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p30,cells30,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells30 0).1 < (cells30 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p30) hw0 heps hcap (commonSigns30 0) (highSigns30 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns30 0)
   (u:=((cells30 0).1:ℝ)/(p30.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p30.toReal.state (((cells30 0).1:ℝ)/(p30.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(392004619581907536351188414091/1000000000000000000000000000000:ℝ)) (by norm_num [p30,cells30,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p30,cells30,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source31 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (132761143391574092861500000000000000000000000000000/132817008704540381386128197061593848308135223785579:ℝ) (1000000000000000000000000000000/392004619581907536351188414091:ℝ) (1/10:ℝ)) :
 GlobalSource (796452422361092735741300000000000000000000000000000/796799198303068192648994040499013779906439885746299:ℝ) (200000000000000000000000000000/78417291120997141955210891541:ℝ) (1/10:ℝ) := by
 have heps : 0<p31.toReal.eps := by norm_num [p31,Params.toReal]
 have hcap : p31.toReal.cap=1/10 := by norm_num [p31,Params.toReal]
 have hi : GlobalSource (p31.toReal.state (((cells31 0).2:ℝ)/(p31.den:ℝ))).B (p31.toReal.state (((cells31 0).2:ℝ)/(p31.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p31,cells31,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells31 0).1 < (cells31 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p31) hw0 heps hcap (commonSigns31 0) (highSigns31 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns31 0)
   (u:=((cells31 0).1:ℝ)/(p31.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p31.toReal.state (((cells31 0).1:ℝ)/(p31.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(78417291120997141955210891541/200000000000000000000000000000:ℝ)) (by norm_num [p31,cells31,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p31,cells31,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source32 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (796452422361092735741300000000000000000000000000000/796799198303068192648994040499013779906439885746299:ℝ) (200000000000000000000000000000/78417291120997141955210891541:ℝ) (1/10:ℝ)) :
 GlobalSource (1555347625728009598268750000000000000000000000000/1556047599237374410304202537662077569863341297107:ℝ) (25000000000000000000000000000/9804208998938539040202642181:ℝ) (1/10:ℝ) := by
 have heps : 0<p32.toReal.eps := by norm_num [p32,Params.toReal]
 have hcap : p32.toReal.cap=1/10 := by norm_num [p32,Params.toReal]
 have hi : GlobalSource (p32.toReal.state (((cells32 0).2:ℝ)/(p32.den:ℝ))).B (p32.toReal.state (((cells32 0).2:ℝ)/(p32.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p32,cells32,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells32 0).1 < (cells32 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p32) hw0 heps hcap (commonSigns32 0) (highSigns32 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns32 0)
   (u:=((cells32 0).1:ℝ)/(p32.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p32.toReal.state (((cells32 0).1:ℝ)/(p32.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(9804208998938539040202642181/25000000000000000000000000000:ℝ)) (by norm_num [p32,cells32,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p32,cells32,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (995994670407685250030500000000000000000000000000000/996384799248145115156210239359985609310584640958429:ℝ) (1000000000000000000000000000000/391841152262663269072626115363:ℝ) (1/10:ℝ)) :
 GlobalSource (1555347625728009598268750000000000000000000000000/1556047599237374410304202537662077569863341297107:ℝ) (25000000000000000000000000000/9804208998938539040202642181:ℝ) (1/10:ℝ) := by
 have h29 := source29 hβ hp
 have h30 := source30 hβ h29
 have h31 := source31 hβ h30
 have h32 := source32 hβ h31
 exact h32
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0029_0032
