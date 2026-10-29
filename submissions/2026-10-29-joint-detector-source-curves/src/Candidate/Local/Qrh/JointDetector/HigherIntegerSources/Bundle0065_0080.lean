/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0065_0068
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0069_0072
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0073_0076
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0077_0080
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0065_0068
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0065_0068

theorem source65 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (30963905029120415180750000000000000000000000000000/30992961018894556927328612637507048370377852346167:ℝ) (250000000000000000000000000000/98706443569810839246098004009:ℝ) (1/10:ℝ)) :
 GlobalSource (1268098449211409291519200000000000000000000000000/1269308548334679930838535492545208193423639989259:ℝ) (1600000000000000000000000000/631855953455581553428771847:ℝ) (1/10:ℝ) := by
 have heps : 0<p65.toReal.eps := by norm_num [p65,Params.toReal]
 have hcap : p65.toReal.cap=1/10 := by norm_num [p65,Params.toReal]
 have hi : GlobalSource (p65.toReal.state (((cells65 0).2:ℝ)/(p65.den:ℝ))).B (p65.toReal.state (((cells65 0).2:ℝ)/(p65.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p65,cells65,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells65 0).1 < (cells65 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p65) hw0 heps hcap (commonSigns65 0) (highSigns65 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns65 0)
   (u:=((cells65 0).1:ℝ)/(p65.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p65.toReal.state (((cells65 0).1:ℝ)/(p65.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(631855953455581553428771847/1600000000000000000000000000:ℝ)) (by norm_num [p65,cells65,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p65,cells65,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source66 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1268098449211409291519200000000000000000000000000/1269308548334679930838535492545208193423639989259:ℝ) (1600000000000000000000000000/631855953455581553428771847:ℝ) (1/10:ℝ)) :
 GlobalSource (41273286081707238842281250000000000000000000000000/41313328621081207897049959943503059078326364543031:ℝ) (62500000000000000000000000000/24687139884908835000221952709:ℝ) (1/10:ℝ) := by
 have heps : 0<p66.toReal.eps := by norm_num [p66,Params.toReal]
 have hcap : p66.toReal.cap=1/10 := by norm_num [p66,Params.toReal]
 have hi : GlobalSource (p66.toReal.state (((cells66 0).2:ℝ)/(p66.den:ℝ))).B (p66.toReal.state (((cells66 0).2:ℝ)/(p66.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p66,cells66,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells66 0).1 < (cells66 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p66) hw0 heps hcap (commonSigns66 0) (highSigns66 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns66 0)
   (u:=((cells66 0).1:ℝ)/(p66.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p66.toReal.state (((cells66 0).1:ℝ)/(p66.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(24687139884908835000221952709/62500000000000000000000000000:ℝ)) (by norm_num [p66,cells66,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p66,cells66,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source67 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (41273286081707238842281250000000000000000000000000/41313328621081207897049959943503059078326364543031:ℝ) (62500000000000000000000000000/24687139884908835000221952709:ℝ) (1/10:ℝ)) :
 GlobalSource (990415818475533955430125000000000000000000000000000/991392503155040771906628592930277857901169664557993:ℝ) (250000000000000000000000000000/98769644023728803951068666291:ℝ) (1/10:ℝ) := by
 have heps : 0<p67.toReal.eps := by norm_num [p67,Params.toReal]
 have hcap : p67.toReal.cap=1/10 := by norm_num [p67,Params.toReal]
 have hi : GlobalSource (p67.toReal.state (((cells67 0).2:ℝ)/(p67.den:ℝ))).B (p67.toReal.state (((cells67 0).2:ℝ)/(p67.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p67,cells67,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells67 0).1 < (cells67 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p67) hw0 heps hcap (commonSigns67 0) (highSigns67 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns67 0)
   (u:=((cells67 0).1:ℝ)/(p67.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p67.toReal.state (((cells67 0).1:ℝ)/(p67.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(98769644023728803951068666291/250000000000000000000000000000:ℝ)) (by norm_num [p67,cells67,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p67,cells67,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source68 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (990415818475533955430125000000000000000000000000000/991392503155040771906628592930277857901169664557993:ℝ) (250000000000000000000000000000/98769644023728803951068666291:ℝ) (1/10:ℝ)) :
 GlobalSource (990272770990094178645500000000000000000000000000000/991265152125763934890840402193300924542372087228713:ℝ) (1000000000000000000000000000000/395162984788236290494749766081:ℝ) (1/10:ℝ) := by
 have heps : 0<p68.toReal.eps := by norm_num [p68,Params.toReal]
 have hcap : p68.toReal.cap=1/10 := by norm_num [p68,Params.toReal]
 have hi : GlobalSource (p68.toReal.state (((cells68 0).2:ℝ)/(p68.den:ℝ))).B (p68.toReal.state (((cells68 0).2:ℝ)/(p68.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p68,cells68,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells68 0).1 < (cells68 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p68) hw0 heps hcap (commonSigns68 0) (highSigns68 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns68 0)
   (u:=((cells68 0).1:ℝ)/(p68.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p68.toReal.state (((cells68 0).1:ℝ)/(p68.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(395162984788236290494749766081/1000000000000000000000000000000:ℝ)) (by norm_num [p68,cells68,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p68,cells68,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (30963905029120415180750000000000000000000000000000/30992961018894556927328612637507048370377852346167:ℝ) (250000000000000000000000000000/98706443569810839246098004009:ℝ) (1/10:ℝ)) :
 GlobalSource (990272770990094178645500000000000000000000000000000/991265152125763934890840402193300924542372087228713:ℝ) (1000000000000000000000000000000/395162984788236290494749766081:ℝ) (1/10:ℝ) := by
 have h65 := source65 hβ hp
 have h66 := source66 hβ h65
 have h67 := source67 hβ h66
 have h68 := source68 hβ h67
 exact h68
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0065_0068
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0069_0072
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0069_0072

theorem source69 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (990272770990094178645500000000000000000000000000000/991265152125763934890840402193300924542372087228713:ℝ) (1000000000000000000000000000000/395162984788236290494749766081:ℝ) (1/10:ℝ)) :
 GlobalSource (1320172964672872535814500000000000000000000000000000/1321517111746912160918571555617375798170681701230189:ℝ) (1000000000000000000000000000000/395247464307994061827943949547:ℝ) (1/10:ℝ) := by
 have heps : 0<p69.toReal.eps := by norm_num [p69,Params.toReal]
 have hcap : p69.toReal.cap=1/10 := by norm_num [p69,Params.toReal]
 have hi : GlobalSource (p69.toReal.state (((cells69 0).2:ℝ)/(p69.den:ℝ))).B (p69.toReal.state (((cells69 0).2:ℝ)/(p69.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p69,cells69,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells69 0).1 < (cells69 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p69) hw0 heps hcap (commonSigns69 0) (highSigns69 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns69 0)
   (u:=((cells69 0).1:ℝ)/(p69.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p69.toReal.state (((cells69 0).1:ℝ)/(p69.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(395247464307994061827943949547/1000000000000000000000000000000:ℝ)) (by norm_num [p69,cells69,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p69,cells69,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source70 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1320172964672872535814500000000000000000000000000000/1321517111746912160918571555617375798170681701230189:ℝ) (1000000000000000000000000000000/395247464307994061827943949547:ℝ) (1/10:ℝ)) :
 GlobalSource (24749666900480365626906250000000000000000000000000/24775263705010316255489646094078715074538821082997:ℝ) (62500000000000000000000000000/24708250920236962396238358659:ℝ) (1/10:ℝ) := by
 have heps : 0<p70.toReal.eps := by norm_num [p70,Params.toReal]
 have hcap : p70.toReal.cap=1/10 := by norm_num [p70,Params.toReal]
 have hi : GlobalSource (p70.toReal.state (((cells70 0).2:ℝ)/(p70.den:ℝ))).B (p70.toReal.state (((cells70 0).2:ℝ)/(p70.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p70,cells70,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells70 0).1 < (cells70 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p70) hw0 heps hcap (commonSigns70 0) (highSigns70 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns70 0)
   (u:=((cells70 0).1:ℝ)/(p70.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p70.toReal.state (((cells70 0).1:ℝ)/(p70.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(24708250920236962396238358659/62500000000000000000000000000:ℝ)) (by norm_num [p70,cells70,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p70,cells70,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source71 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24749666900480365626906250000000000000000000000000/24775263705010316255489646094078715074538821082997:ℝ) (62500000000000000000000000000/24708250920236962396238358659:ℝ) (1/10:ℝ)) :
 GlobalSource (3959374514135099393166500000000000000000000000000000/3963533181154425806038840477801570525314034004997273:ℝ) (1000000000000000000000000000000/395416636105344724958840447727:ℝ) (1/10:ℝ) := by
 have heps : 0<p71.toReal.eps := by norm_num [p71,Params.toReal]
 have hcap : p71.toReal.cap=1/10 := by norm_num [p71,Params.toReal]
 have hi : GlobalSource (p71.toReal.state (((cells71 0).2:ℝ)/(p71.den:ℝ))).B (p71.toReal.state (((cells71 0).2:ℝ)/(p71.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p71,cells71,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells71 0).1 < (cells71 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p71) hw0 heps hcap (commonSigns71 0) (highSigns71 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns71 0)
   (u:=((cells71 0).1:ℝ)/(p71.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p71.toReal.state (((cells71 0).1:ℝ)/(p71.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(395416636105344724958840447727/1000000000000000000000000000000:ℝ)) (by norm_num [p71,cells71,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p71,cells71,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source72 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3959374514135099393166500000000000000000000000000000/3963533181154425806038840477801570525314034004997273:ℝ) (1000000000000000000000000000000/395416636105344724958840447727:ℝ) (1/10:ℝ)) :
 GlobalSource (13745841403449098215375000000000000000000000000000/13760501042596777613625948596716643077578433953297:ℝ) (250000000000000000000000000000/98875332130621047247990504413:ℝ) (1/10:ℝ) := by
 have heps : 0<p72.toReal.eps := by norm_num [p72,Params.toReal]
 have hcap : p72.toReal.cap=1/10 := by norm_num [p72,Params.toReal]
 have hi : GlobalSource (p72.toReal.state (((cells72 0).2:ℝ)/(p72.den:ℝ))).B (p72.toReal.state (((cells72 0).2:ℝ)/(p72.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p72,cells72,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells72 0).1 < (cells72 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p72) hw0 heps hcap (commonSigns72 0) (highSigns72 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns72 0)
   (u:=((cells72 0).1:ℝ)/(p72.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p72.toReal.state (((cells72 0).1:ℝ)/(p72.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(98875332130621047247990504413/250000000000000000000000000000:ℝ)) (by norm_num [p72,cells72,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p72,cells72,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (990272770990094178645500000000000000000000000000000/991265152125763934890840402193300924542372087228713:ℝ) (1000000000000000000000000000000/395162984788236290494749766081:ℝ) (1/10:ℝ)) :
 GlobalSource (13745841403449098215375000000000000000000000000000/13760501042596777613625948596716643077578433953297:ℝ) (250000000000000000000000000000/98875332130621047247990504413:ℝ) (1/10:ℝ) := by
 have h69 := source69 hβ hp
 have h70 := source70 hβ h69
 have h71 := source71 hβ h70
 have h72 := source72 hβ h71
 exact h72
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0069_0072
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0073_0076
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0073_0076

theorem source73 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (13745841403449098215375000000000000000000000000000/13760501042596777613625948596716643077578433953297:ℝ) (250000000000000000000000000000/98875332130621047247990504413:ℝ) (1/10:ℝ)) :
 GlobalSource (123694691695361911840296875000000000000000000000000/123828610940968148503738135520074671701445340995201:ℝ) (31250000000000000000000000000/12362065376411057077779952873:ℝ) (1/10:ℝ) := by
 have heps : 0<p73.toReal.eps := by norm_num [p73,Params.toReal]
 have hcap : p73.toReal.cap=1/10 := by norm_num [p73,Params.toReal]
 have hi : GlobalSource (p73.toReal.state (((cells73 0).2:ℝ)/(p73.den:ℝ))).B (p73.toReal.state (((cells73 0).2:ℝ)/(p73.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p73,cells73,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells73 0).1 < (cells73 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p73) hw0 heps hcap (commonSigns73 0) (highSigns73 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns73 0)
   (u:=((cells73 0).1:ℝ)/(p73.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p73.toReal.state (((cells73 0).1:ℝ)/(p73.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(12362065376411057077779952873/31250000000000000000000000000:ℝ)) (by norm_num [p73,cells73,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p73,cells73,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source74 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (123694691695361911840296875000000000000000000000000/123828610940968148503738135520074671701445340995201:ℝ) (31250000000000000000000000000/12362065376411057077779952873:ℝ) (1/10:ℝ)) :
 GlobalSource (1978828972154911035875500000000000000000000000000000/1981003465326462743472134763150471963330697895248689:ℝ) (1000000000000000000000000000000/395670926743411729000807318813:ℝ) (1/10:ℝ) := by
 have heps : 0<p74.toReal.eps := by norm_num [p74,Params.toReal]
 have hcap : p74.toReal.cap=1/10 := by norm_num [p74,Params.toReal]
 have hi : GlobalSource (p74.toReal.state (((cells74 0).2:ℝ)/(p74.den:ℝ))).B (p74.toReal.state (((cells74 0).2:ℝ)/(p74.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p74,cells74,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells74 0).1 < (cells74 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p74) hw0 heps hcap (commonSigns74 0) (highSigns74 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns74 0)
   (u:=((cells74 0).1:ℝ)/(p74.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p74.toReal.state (((cells74 0).1:ℝ)/(p74.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(395670926743411729000807318813/1000000000000000000000000000000:ℝ)) (by norm_num [p74,cells74,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p74,cells74,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source75 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1978828972154911035875500000000000000000000000000000/1981003465326462743472134763150471963330697895248689:ℝ) (1000000000000000000000000000000/395670926743411729000807318813:ℝ) (1/10:ℝ)) :
 GlobalSource (52761143391574172861500000000000000000000000000000/52819979224840809689094930950953216670382558179553:ℝ) (1000000000000000000000000000000/395755832687430210720521226897:ℝ) (1/10:ℝ) := by
 have heps : 0<p75.toReal.eps := by norm_num [p75,Params.toReal]
 have hcap : p75.toReal.cap=1/10 := by norm_num [p75,Params.toReal]
 have hi : GlobalSource (p75.toReal.state (((cells75 0).2:ℝ)/(p75.den:ℝ))).B (p75.toReal.state (((cells75 0).2:ℝ)/(p75.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p75,cells75,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells75 0).1 < (cells75 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p75) hw0 heps hcap (commonSigns75 0) (highSigns75 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns75 0)
   (u:=((cells75 0).1:ℝ)/(p75.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p75.toReal.state (((cells75 0).1:ℝ)/(p75.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(395755832687430210720521226897/1000000000000000000000000000000:ℝ)) (by norm_num [p75,cells75,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p75,cells75,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source76 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (52761143391574172861500000000000000000000000000000/52819979224840809689094930950953216670382558179553:ℝ) (1000000000000000000000000000000/395755832687430210720521226897:ℝ) (1/10:ℝ)) :
 GlobalSource (989128391106575964368500000000000000000000000000000/990247520927730510769933940232461519910667483744719:ℝ) (1000000000000000000000000000000/395840809947495975994840047629:ℝ) (1/10:ℝ) := by
 have heps : 0<p76.toReal.eps := by norm_num [p76,Params.toReal]
 have hcap : p76.toReal.cap=1/10 := by norm_num [p76,Params.toReal]
 have hi : GlobalSource (p76.toReal.state (((cells76 0).2:ℝ)/(p76.den:ℝ))).B (p76.toReal.state (((cells76 0).2:ℝ)/(p76.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p76,cells76,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells76 0).1 < (cells76 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p76) hw0 heps hcap (commonSigns76 0) (highSigns76 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns76 0)
   (u:=((cells76 0).1:ℝ)/(p76.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p76.toReal.state (((cells76 0).1:ℝ)/(p76.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(395840809947495975994840047629/1000000000000000000000000000000:ℝ)) (by norm_num [p76,cells76,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p76,cells76,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (13745841403449098215375000000000000000000000000000/13760501042596777613625948596716643077578433953297:ℝ) (250000000000000000000000000000/98875332130621047247990504413:ℝ) (1/10:ℝ)) :
 GlobalSource (989128391106575964368500000000000000000000000000000/990247520927730510769933940232461519910667483744719:ℝ) (1000000000000000000000000000000/395840809947495975994840047629:ℝ) (1/10:ℝ) := by
 have h73 := source73 hβ hp
 have h74 := source74 hβ h73
 have h75 := source75 hβ h74
 have h76 := source76 hβ h75
 exact h76
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0073_0076
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0077_0080
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0077_0080

theorem source77 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (989128391106575964368500000000000000000000000000000/990247520927730510769933940232461519910667483744719:ℝ) (1000000000000000000000000000000/395840809947495975994840047629:ℝ) (1/10:ℝ)) :
 GlobalSource (1977970687242272375167750000000000000000000000000000/1980240928083112863143420183950727912477552396891511:ℝ) (500000000000000000000000000000/197962929297005143622542317347:ℝ) (1/10:ℝ) := by
 have heps : 0<p77.toReal.eps := by norm_num [p77,Params.toReal]
 have hcap : p77.toReal.cap=1/10 := by norm_num [p77,Params.toReal]
 have hi : GlobalSource (p77.toReal.state (((cells77 0).2:ℝ)/(p77.den:ℝ))).B (p77.toReal.state (((cells77 0).2:ℝ)/(p77.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p77,cells77,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells77 0).1 < (cells77 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p77) hw0 heps hcap (commonSigns77 0) (highSigns77 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns77 0)
   (u:=((cells77 0).1:ℝ)/(p77.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p77.toReal.state (((cells77 0).1:ℝ)/(p77.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(197962929297005143622542317347/500000000000000000000000000000:ℝ)) (by norm_num [p77,cells77,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p77,cells77,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source78 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1977970687242272375167750000000000000000000000000000/1980240928083112863143420183950727912477552396891511:ℝ) (500000000000000000000000000000/197962929297005143622542317347:ℝ) (1/10:ℝ)) :
 GlobalSource (82403524677974700899937500000000000000000000000000/82499453316643093776696686740865409197684942206657:ℝ) (125000000000000000000000000000/49501372337186141657798046181:ℝ) (1/10:ℝ) := by
 have heps : 0<p78.toReal.eps := by norm_num [p78,Params.toReal]
 have hcap : p78.toReal.cap=1/10 := by norm_num [p78,Params.toReal]
 have hi : GlobalSource (p78.toReal.state (((cells78 0).2:ℝ)/(p78.den:ℝ))).B (p78.toReal.state (((cells78 0).2:ℝ)/(p78.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p78,cells78,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells78 0).1 < (cells78 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p78) hw0 heps hcap (commonSigns78 0) (highSigns78 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns78 0)
   (u:=((cells78 0).1:ℝ)/(p78.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p78.toReal.state (((cells78 0).1:ℝ)/(p78.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(49501372337186141657798046181/125000000000000000000000000000:ℝ)) (by norm_num [p78,cells78,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p78,cells78,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source79 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (82403524677974700899937500000000000000000000000000/82499453316643093776696686740865409197684942206657:ℝ) (125000000000000000000000000000/49501372337186141657798046181:ℝ) (1/10:ℝ)) :
 GlobalSource (3954796994601026536058500000000000000000000000000000/3959465792778927244693448246258645912431288985384223:ℝ) (1000000000000000000000000000000/396096170328563397889568632673:ℝ) (1/10:ℝ) := by
 have heps : 0<p79.toReal.eps := by norm_num [p79,Params.toReal]
 have hcap : p79.toReal.cap=1/10 := by norm_num [p79,Params.toReal]
 have hi : GlobalSource (p79.toReal.state (((cells79 0).2:ℝ)/(p79.den:ℝ))).B (p79.toReal.state (((cells79 0).2:ℝ)/(p79.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p79,cells79,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells79 0).1 < (cells79 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p79) hw0 heps hcap (commonSigns79 0) (highSigns79 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns79 0)
   (u:=((cells79 0).1:ℝ)/(p79.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p79.toReal.state (((cells79 0).1:ℝ)/(p79.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(396096170328563397889568632673/1000000000000000000000000000000:ℝ)) (by norm_num [p79,cells79,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p79,cells79,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source80 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3954796994601026536058500000000000000000000000000000/3959465792778927244693448246258645912431288985384223:ℝ) (1000000000000000000000000000000/396096170328563397889568632673:ℝ) (1/10:ℝ)) :
 GlobalSource (24713905029120421430750000000000000000000000000000/24743487230479116889132888517929618159389814282161:ℝ) (500000000000000000000000000000/198090716778989514557058206619:ℝ) (1/10:ℝ) := by
 have heps : 0<p80.toReal.eps := by norm_num [p80,Params.toReal]
 have hcap : p80.toReal.cap=1/10 := by norm_num [p80,Params.toReal]
 have hi : GlobalSource (p80.toReal.state (((cells80 0).2:ℝ)/(p80.den:ℝ))).B (p80.toReal.state (((cells80 0).2:ℝ)/(p80.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p80,cells80,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells80 0).1 < (cells80 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p80) hw0 heps hcap (commonSigns80 0) (highSigns80 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns80 0)
   (u:=((cells80 0).1:ℝ)/(p80.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p80.toReal.state (((cells80 0).1:ℝ)/(p80.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(198090716778989514557058206619/500000000000000000000000000000:ℝ)) (by norm_num [p80,cells80,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p80,cells80,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (989128391106575964368500000000000000000000000000000/990247520927730510769933940232461519910667483744719:ℝ) (1000000000000000000000000000000/395840809947495975994840047629:ℝ) (1/10:ℝ)) :
 GlobalSource (24713905029120421430750000000000000000000000000000/24743487230479116889132888517929618159389814282161:ℝ) (500000000000000000000000000000/198090716778989514557058206619:ℝ) (1/10:ℝ) := by
 have h77 := source77 hβ hp
 have h78 := source78 hβ h77
 have h79 := source79 hβ h78
 have h80 := source80 hβ h79
 exact h80
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0077_0080
