/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0113_0116
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0117_0120
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0121_0124
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0125_0128
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0113_0116
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0113_0116

theorem source113 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (491989340815372000061000000000000000000000000000/492846994083005548839543323154054453672026355171:ℝ) (2000000000000000000000000000/797896180513396643766609587:ℝ) (1/10:ℝ)) :
 GlobalSource (1967671268290608446674750000000000000000000000000000/1971136204159899208676064597889586437085083015837119:ℝ) (500000000000000000000000000000/199517878341542101469130462527:ℝ) (1/10:ℝ) := by
 have heps : 0<p113.toReal.eps := by norm_num [p113,Params.toReal]
 have hcap : p113.toReal.cap=1/10 := by norm_num [p113,Params.toReal]
 have hi : GlobalSource (p113.toReal.state (((cells113 0).2:ℝ)/(p113.den:ℝ))).B (p113.toReal.state (((cells113 0).2:ℝ)/(p113.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p113,cells113,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells113 0).1 < (cells113 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p113) hw0 heps hcap (commonSigns113 0) (highSigns113 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns113 0)
   (u:=((cells113 0).1:ℝ)/(p113.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p113.toReal.state (((cells113 0).1:ℝ)/(p113.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(199517878341542101469130462527/500000000000000000000000000000:ℝ)) (by norm_num [p113,cells113,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p113,cells113,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source114 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1967671268290608446674750000000000000000000000000000/1971136204159899208676064597889586437085083015837119:ℝ) (500000000000000000000000000000/199517878341542101469130462527:ℝ) (1/10:ℝ)) :
 GlobalSource (655795057773242964368500000000000000000000000000000/656961498931164725260158141335794464313154595544589:ℝ) (1000000000000000000000000000000/399123497182870529531756128799:ℝ) (1/10:ℝ) := by
 have heps : 0<p114.toReal.eps := by norm_num [p114,Params.toReal]
 have hcap : p114.toReal.cap=1/10 := by norm_num [p114,Params.toReal]
 have hi : GlobalSource (p114.toReal.state (((cells114 0).2:ℝ)/(p114.den:ℝ))).B (p114.toReal.state (((cells114 0).2:ℝ)/(p114.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p114,cells114,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells114 0).1 < (cells114 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p114) hw0 heps hcap (commonSigns114 0) (highSigns114 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns114 0)
   (u:=((cells114 0).1:ℝ)/(p114.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p114.toReal.state (((cells114 0).1:ℝ)/(p114.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(399123497182870529531756128799/1000000000000000000000000000000:ℝ)) (by norm_num [p114,cells114,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p114,cells114,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source115 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (655795057773242964368500000000000000000000000000000/656961498931164725260158141335794464313154595544589:ℝ) (1000000000000000000000000000000/399123497182870529531756128799:ℝ) (1/10:ℝ)) :
 GlobalSource (786839631339539735814500000000000000000000000000000/788253141688398369704887957101698464665813396167571:ℝ) (1000000000000000000000000000000/399211311830940145874160738133:ℝ) (1/10:ℝ) := by
 have heps : 0<p115.toReal.eps := by norm_num [p115,Params.toReal]
 have hcap : p115.toReal.cap=1/10 := by norm_num [p115,Params.toReal]
 have hi : GlobalSource (p115.toReal.state (((cells115 0).2:ℝ)/(p115.den:ℝ))).B (p115.toReal.state (((cells115 0).2:ℝ)/(p115.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p115,cells115,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells115 0).1 < (cells115 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p115) hw0 heps hcap (commonSigns115 0) (highSigns115 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns115 0)
   (u:=((cells115 0).1:ℝ)/(p115.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p115.toReal.state (((cells115 0).1:ℝ)/(p115.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(399211311830940145874160738133/1000000000000000000000000000000:ℝ)) (by norm_num [p115,cells115,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p115,cells115,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source116 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (786839631339539735814500000000000000000000000000000/788253141688398369704887957101698464665813396167571:ℝ) (1000000000000000000000000000000/399211311830940145874160738133:ℝ) (1/10:ℝ)) :
 GlobalSource (491703245844492446491750000000000000000000000000000/492595319107669571059958397613541492453446123424841:ℝ) (500000000000000000000000000000/199649600351148659110195711941:ℝ) (1/10:ℝ) := by
 have heps : 0<p116.toReal.eps := by norm_num [p116,Params.toReal]
 have hcap : p116.toReal.cap=1/10 := by norm_num [p116,Params.toReal]
 have hi : GlobalSource (p116.toReal.state (((cells116 0).2:ℝ)/(p116.den:ℝ))).B (p116.toReal.state (((cells116 0).2:ℝ)/(p116.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p116,cells116,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells116 0).1 < (cells116 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p116) hw0 heps hcap (commonSigns116 0) (highSigns116 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns116 0)
   (u:=((cells116 0).1:ℝ)/(p116.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p116.toReal.state (((cells116 0).1:ℝ)/(p116.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(199649600351148659110195711941/500000000000000000000000000000:ℝ)) (by norm_num [p116,cells116,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p116,cells116,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (491989340815372000061000000000000000000000000000/492846994083005548839543323154054453672026355171:ℝ) (2000000000000000000000000000/797896180513396643766609587:ℝ) (1/10:ℝ)) :
 GlobalSource (491703245844492446491750000000000000000000000000000/492595319107669571059958397613541492453446123424841:ℝ) (500000000000000000000000000000/199649600351148659110195711941:ℝ) (1/10:ℝ) := by
 have h113 := source113 hβ hp
 have h114 := source114 hβ h113
 have h115 := source115 hβ h114
 have h116 := source116 hβ h115
 exact h116
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0113_0116
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0117_0120
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0117_0120

theorem source117 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (491703245844492446491750000000000000000000000000000/492595319107669571059958397613541492453446123424841:ℝ) (500000000000000000000000000000/199649600351148659110195711941:ℝ) (1/10:ℝ)) :
 GlobalSource (262203585120945364319700000000000000000000000000000/262683968454786660802828762899230189155771801742651:ℝ) (200000000000000000000000000000/79877432774413583861494881661:ℝ) (1/10:ℝ) := by
 have heps : 0<p117.toReal.eps := by norm_num [p117,Params.toReal]
 have hcap : p117.toReal.cap=1/10 := by norm_num [p117,Params.toReal]
 have hi : GlobalSource (p117.toReal.state (((cells117 0).2:ℝ)/(p117.den:ℝ))).B (p117.toReal.state (((cells117 0).2:ℝ)/(p117.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p117,cells117,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells117 0).1 < (cells117 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p117) hw0 heps hcap (commonSigns117 0) (highSigns117 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns117 0)
   (u:=((cells117 0).1:ℝ)/(p117.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p117.toReal.state (((cells117 0).1:ℝ)/(p117.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(79877432774413583861494881661/200000000000000000000000000000:ℝ)) (by norm_num [p117,cells117,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p117,cells117,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source118 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (262203585120945364319700000000000000000000000000000/262683968454786660802828762899230189155771801742651:ℝ) (200000000000000000000000000000/79877432774413583861494881661:ℝ) (1/10:ℝ)) :
 GlobalSource (1966240793436210678828500000000000000000000000000000/1969878315150104378006032359493119341206345977995703:ℝ) (1000000000000000000000000000000/399475201415499613226153297493:ℝ) (1/10:ℝ) := by
 have heps : 0<p118.toReal.eps := by norm_num [p118,Params.toReal]
 have hcap : p118.toReal.cap=1/10 := by norm_num [p118,Params.toReal]
 have hi : GlobalSource (p118.toReal.state (((cells118 0).2:ℝ)/(p118.den:ℝ))).B (p118.toReal.state (((cells118 0).2:ℝ)/(p118.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p118,cells118,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells118 0).1 < (cells118 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p118) hw0 heps hcap (commonSigns118 0) (highSigns118 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns118 0)
   (u:=((cells118 0).1:ℝ)/(p118.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p118.toReal.state (((cells118 0).1:ℝ)/(p118.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(399475201415499613226153297493/1000000000000000000000000000000:ℝ)) (by norm_num [p118,cells118,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p118,cells118,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source119 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1966240793436210678828500000000000000000000000000000/1969878315150104378006032359493119341206345977995703:ℝ) (1000000000000000000000000000000/399475201415499613226153297493:ℝ) (1/10:ℝ)) :
 GlobalSource (1965954698465331125259250000000000000000000000000000/1969626931636819594843128414427211283488670184598007:ℝ) (500000000000000000000000000000/199781656703981020365247061937:ℝ) (1/10:ℝ) := by
 have heps : 0<p119.toReal.eps := by norm_num [p119,Params.toReal]
 have hcap : p119.toReal.cap=1/10 := by norm_num [p119,Params.toReal]
 have hi : GlobalSource (p119.toReal.state (((cells119 0).2:ℝ)/(p119.den:ℝ))).B (p119.toReal.state (((cells119 0).2:ℝ)/(p119.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p119,cells119,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells119 0).1 < (cells119 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p119) hw0 heps hcap (commonSigns119 0) (highSigns119 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns119 0)
   (u:=((cells119 0).1:ℝ)/(p119.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p119.toReal.state (((cells119 0).1:ℝ)/(p119.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(199781656703981020365247061937/500000000000000000000000000000:ℝ)) (by norm_num [p119,cells119,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p119,cells119,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source120 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1965954698465331125259250000000000000000000000000000/1969626931636819594843128414427211283488670184598007:ℝ) (500000000000000000000000000000/199781656703981020365247061937:ℝ) (1/10:ℝ)) :
 GlobalSource (32761143391574192861500000000000000000000000000000/32822926880994302097233226645224386957058852187909:ℝ) (1000000000000000000000000000000/399651499924947004984736998761:ℝ) (1/10:ℝ) := by
 have heps : 0<p120.toReal.eps := by norm_num [p120,Params.toReal]
 have hcap : p120.toReal.cap=1/10 := by norm_num [p120,Params.toReal]
 have hi : GlobalSource (p120.toReal.state (((cells120 0).2:ℝ)/(p120.den:ℝ))).B (p120.toReal.state (((cells120 0).2:ℝ)/(p120.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p120,cells120,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells120 0).1 < (cells120 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p120) hw0 heps hcap (commonSigns120 0) (highSigns120 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns120 0)
   (u:=((cells120 0).1:ℝ)/(p120.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p120.toReal.state (((cells120 0).1:ℝ)/(p120.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(399651499924947004984736998761/1000000000000000000000000000000:ℝ)) (by norm_num [p120,cells120,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p120,cells120,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (491703245844492446491750000000000000000000000000000/492595319107669571059958397613541492453446123424841:ℝ) (500000000000000000000000000000/199649600351148659110195711941:ℝ) (1/10:ℝ)) :
 GlobalSource (32761143391574192861500000000000000000000000000000/32822926880994302097233226645224386957058852187909:ℝ) (1000000000000000000000000000000/399651499924947004984736998761:ℝ) (1/10:ℝ) := by
 have h117 := source117 hβ hp
 have h118 := source118 hβ h117
 have h119 := source119 hβ h118
 have h120 := source120 hβ h119
 exact h120
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0117_0120
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0121_0124
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0121_0124

theorem source121 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (32761143391574192861500000000000000000000000000000/32822926880994302097233226645224386957058852187909:ℝ) (1000000000000000000000000000000/399651499924947004984736998761:ℝ) (1/10:ℝ)) :
 GlobalSource (3930765017047144036241500000000000000000000000000000/3938248717614633667340703180142558875563861356977429:ℝ) (1000000000000000000000000000000/399739761042068657766339535021:ℝ) (1/10:ℝ) := by
 have heps : 0<p121.toReal.eps := by norm_num [p121,Params.toReal]
 have hcap : p121.toReal.cap=1/10 := by norm_num [p121,Params.toReal]
 have hi : GlobalSource (p121.toReal.state (((cells121 0).2:ℝ)/(p121.den:ℝ))).B (p121.toReal.state (((cells121 0).2:ℝ)/(p121.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p121,cells121,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells121 0).1 < (cells121 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p121) hw0 heps hcap (commonSigns121 0) (highSigns121 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns121 0)
   (u:=((cells121 0).1:ℝ)/(p121.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p121.toReal.state (((cells121 0).1:ℝ)/(p121.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(399739761042068657766339535021/1000000000000000000000000000000:ℝ)) (by norm_num [p121,cells121,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p121,cells121,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source122 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3930765017047144036241500000000000000000000000000000/3938248717614633667340703180142558875563861356977429:ℝ) (1000000000000000000000000000000/399739761042068657766339535021:ℝ) (1/10:ℝ)) :
 GlobalSource (280728059078956066364500000000000000000000000000000/281267595638368113334143365231808498080856478739037:ℝ) (1000000000000000000000000000000/399828096835063686092438392551:ℝ) (1/10:ℝ) := by
 have heps : 0<p122.toReal.eps := by norm_num [p122,Params.toReal]
 have hcap : p122.toReal.cap=1/10 := by norm_num [p122,Params.toReal]
 have hi : GlobalSource (p122.toReal.state (((cells122 0).2:ℝ)/(p122.den:ℝ))).B (p122.toReal.state (((cells122 0).2:ℝ)/(p122.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p122,cells122,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells122 0).1 < (cells122 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p122) hw0 heps hcap (commonSigns122 0) (highSigns122 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns122 0)
   (u:=((cells122 0).1:ℝ)/(p122.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p122.toReal.state (((cells122 0).1:ℝ)/(p122.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(399828096835063686092438392551/1000000000000000000000000000000:ℝ)) (by norm_num [p122,cells122,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p122,cells122,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source123 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (280728059078956066364500000000000000000000000000000/281267595638368113334143365231808498080856478739037:ℝ) (1000000000000000000000000000000/399828096835063686092438392551:ℝ) (1/10:ℝ)) :
 GlobalSource (654936772860604303660750000000000000000000000000000/656207348277434387131777541907110502472775064768969:ℝ) (500000000000000000000000000000/199958253689895749655838663761:ℝ) (1/10:ℝ) := by
 have heps : 0<p123.toReal.eps := by norm_num [p123,Params.toReal]
 have hcap : p123.toReal.cap=1/10 := by norm_num [p123,Params.toReal]
 have hi : GlobalSource (p123.toReal.state (((cells123 0).2:ℝ)/(p123.den:ℝ))).B (p123.toReal.state (((cells123 0).2:ℝ)/(p123.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p123,cells123,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells123 0).1 < (cells123 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p123) hw0 heps hcap (commonSigns123 0) (highSigns123 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns123 0)
   (u:=((cells123 0).1:ℝ)/(p123.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p123.toReal.state (((cells123 0).1:ℝ)/(p123.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(199958253689895749655838663761/500000000000000000000000000000:ℝ)) (by norm_num [p123,cells123,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p123,cells123,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source124 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (654936772860604303660750000000000000000000000000000/656207348277434387131777541907110502472775064768969:ℝ) (500000000000000000000000000000/199958253689895749655838663761:ℝ) (1/10:ℝ)) :
 GlobalSource (10676762084842029116375000000000000000000000000000/10697668396127418725063179733715203122876656035817:ℝ) (250000000000000000000000000000/100001248188058604155786449769:ℝ) (1/10:ℝ) := by
 have heps : 0<p124.toReal.eps := by norm_num [p124,Params.toReal]
 have hcap : p124.toReal.cap=1/10 := by norm_num [p124,Params.toReal]
 have hi : GlobalSource (p124.toReal.state (((cells124 0).2:ℝ)/(p124.den:ℝ))).B (p124.toReal.state (((cells124 0).2:ℝ)/(p124.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p124,cells124,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells124 0).1 < (cells124 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p124) hw0 heps hcap (commonSigns124 0) (highSigns124 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns124 0)
   (u:=((cells124 0).1:ℝ)/(p124.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p124.toReal.state (((cells124 0).1:ℝ)/(p124.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(100001248188058604155786449769/250000000000000000000000000000:ℝ)) (by norm_num [p124,cells124,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p124,cells124,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (32761143391574192861500000000000000000000000000000/32822926880994302097233226645224386957058852187909:ℝ) (1000000000000000000000000000000/399651499924947004984736998761:ℝ) (1/10:ℝ)) :
 GlobalSource (10676762084842029116375000000000000000000000000000/10697668396127418725063179733715203122876656035817:ℝ) (250000000000000000000000000000/100001248188058604155786449769:ℝ) (1/10:ℝ) := by
 have h121 := source121 hβ hp
 have h122 := source122 hβ h121
 have h123 := source123 hβ h122
 have h124 := source124 hβ h123
 exact h124
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0121_0124
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0125_0128
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0125_0128

theorem source125 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (10676762084842029116375000000000000000000000000000/10697668396127418725063179733715203122876656035817:ℝ) (250000000000000000000000000000/100001248188058604155786449769:ℝ) (1/10:ℝ)) :
 GlobalSource (7856952514560215215375000000000000000000000000000/7872479958492141495106714459241936765259577541643:ℝ) (250000000000000000000000000000/100023388257124463764836400859:ℝ) (1/10:ℝ) := by
 have heps : 0<p125.toReal.eps := by norm_num [p125,Params.toReal]
 have hcap : p125.toReal.cap=1/10 := by norm_num [p125,Params.toReal]
 have hi : GlobalSource (p125.toReal.state (((cells125 0).2:ℝ)/(p125.den:ℝ))).B (p125.toReal.state (((cells125 0).2:ℝ)/(p125.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p125,cells125,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells125 0).1 < (cells125 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p125) hw0 heps hcap (commonSigns125 0) (highSigns125 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns125 0)
   (u:=((cells125 0).1:ℝ)/(p125.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p125.toReal.state (((cells125 0).1:ℝ)/(p125.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(100023388257124463764836400859/250000000000000000000000000000:ℝ)) (by norm_num [p125,cells125,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p125,cells125,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source126 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (7856952514560215215375000000000000000000000000000/7872479958492141495106714459241936765259577541643:ℝ) (250000000000000000000000000000/100023388257124463764836400859:ℝ) (1/10:ℝ)) :
 GlobalSource (130930135577944950018300000000000000000000000000000/131191270601879384379986382168389248559026574343371:ℝ) (200000000000000000000000000000/80036437656962103580889134079:ℝ) (1/10:ℝ) := by
 have heps : 0<p126.toReal.eps := by norm_num [p126,Params.toReal]
 have hcap : p126.toReal.cap=1/10 := by norm_num [p126,Params.toReal]
 have hi : GlobalSource (p126.toReal.state (((cells126 0).2:ℝ)/(p126.den:ℝ))).B (p126.toReal.state (((cells126 0).2:ℝ)/(p126.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p126,cells126,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells126 0).1 < (cells126 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p126) hw0 heps hcap (commonSigns126 0) (highSigns126 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns126 0)
   (u:=((cells126 0).1:ℝ)/(p126.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p126.toReal.state (((cells126 0).1:ℝ)/(p126.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(80036437656962103580889134079/200000000000000000000000000000:ℝ)) (by norm_num [p126,cells126,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p126,cells126,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source127 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (130930135577944950018300000000000000000000000000000/131191270601879384379986382168389248559026574343371:ℝ) (200000000000000000000000000000/80036437656962103580889134079:ℝ) (1/10:ℝ)) :
 GlobalSource (785466375479317878682100000000000000000000000000000/787047277236844560640466418094682174463106513843377:ℝ) (200000000000000000000000000000/80054179719504916717182795679:ℝ) (1/10:ℝ) := by
 have heps : 0<p127.toReal.eps := by norm_num [p127,Params.toReal]
 have hcap : p127.toReal.cap=1/10 := by norm_num [p127,Params.toReal]
 have hi : GlobalSource (p127.toReal.state (((cells127 0).2:ℝ)/(p127.den:ℝ))).B (p127.toReal.state (((cells127 0).2:ℝ)/(p127.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p127,cells127,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells127 0).1 < (cells127 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p127) hw0 heps hcap (commonSigns127 0) (highSigns127 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns127 0)
   (u:=((cells127 0).1:ℝ)/(p127.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p127.toReal.state (((cells127 0).1:ℝ)/(p127.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(80054179719504916717182795679/200000000000000000000000000000:ℝ)) (by norm_num [p127,cells127,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p127,cells127,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source128 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (785466375479317878682100000000000000000000000000000/787047277236844560640466418094682174463106513843377:ℝ) (200000000000000000000000000000/80054179719504916717182795679:ℝ) (1/10:ℝ)) :
 GlobalSource (61355620116481723223000000000000000000000000000000/61480230993877527921947485316178157028806293251433:ℝ) (500000000000000000000000000000/200179842021557947481034133033:ℝ) (1/10:ℝ) := by
 have heps : 0<p128.toReal.eps := by norm_num [p128,Params.toReal]
 have hcap : p128.toReal.cap=1/10 := by norm_num [p128,Params.toReal]
 have hi : GlobalSource (p128.toReal.state (((cells128 0).2:ℝ)/(p128.den:ℝ))).B (p128.toReal.state (((cells128 0).2:ℝ)/(p128.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p128,cells128,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells128 0).1 < (cells128 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p128) hw0 heps hcap (commonSigns128 0) (highSigns128 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns128 0)
   (u:=((cells128 0).1:ℝ)/(p128.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p128.toReal.state (((cells128 0).1:ℝ)/(p128.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(200179842021557947481034133033/500000000000000000000000000000:ℝ)) (by norm_num [p128,cells128,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p128,cells128,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (10676762084842029116375000000000000000000000000000/10697668396127418725063179733715203122876656035817:ℝ) (250000000000000000000000000000/100001248188058604155786449769:ℝ) (1/10:ℝ)) :
 GlobalSource (61355620116481723223000000000000000000000000000000/61480230993877527921947485316178157028806293251433:ℝ) (500000000000000000000000000000/200179842021557947481034133033:ℝ) (1/10:ℝ) := by
 have h125 := source125 hβ hp
 have h126 := source126 hβ h125
 have h127 := source127 hβ h126
 have h128 := source128 hβ h127
 exact h128
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0125_0128
