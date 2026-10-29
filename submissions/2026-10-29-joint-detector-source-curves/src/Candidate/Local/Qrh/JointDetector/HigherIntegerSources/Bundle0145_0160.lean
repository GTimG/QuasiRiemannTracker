/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0145_0148
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0149_0152
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0153_0156
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0157_0160
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0145_0148
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0145_0148

theorem source145 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (20404190877013982146125000000000000000000000000000/20451701613615147980541431400315629750785834406299:ℝ) (250000000000000000000000000000/100447633032613371288347966507:ℝ) (1/10:ℝ)) :
 GlobalSource (12240726432640392077867187500000000000000000000000/12269460319227942114862893649018758705353895971763:ℝ) (15625000000000000000000000000/6279384479008114700107666463:ℝ) (1/10:ℝ) := by
 have heps : 0<p145.toReal.eps := by norm_num [p145,Params.toReal]
 have hcap : p145.toReal.cap=1/10 := by norm_num [p145,Params.toReal]
 have hi : GlobalSource (p145.toReal.state (((cells145 0).2:ℝ)/(p145.den:ℝ))).B (p145.toReal.state (((cells145 0).2:ℝ)/(p145.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p145,cells145,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells145 0).1 < (cells145 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p145) hw0 heps hcap (commonSigns145 0) (highSigns145 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns145 0)
   (u:=((cells145 0).1:ℝ)/(p145.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p145.toReal.state (((cells145 0).1:ℝ)/(p145.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(6279384479008114700107666463/15625000000000000000000000000:ℝ)) (by norm_num [p145,cells145,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p145,cells145,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source146 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (12240726432640392077867187500000000000000000000000/12269460319227942114862893649018758705353895971763:ℝ) (15625000000000000000000000000/6279384479008114700107666463:ℝ) (1/10:ℝ)) :
 GlobalSource (1958230134251583178889500000000000000000000000000000/1962864011715162064110035612797149431089216326148761:ℝ) (1000000000000000000000000000000/401970757713392798624863476753:ℝ) (1/10:ℝ) := by
 have heps : 0<p146.toReal.eps := by norm_num [p146,Params.toReal]
 have hcap : p146.toReal.cap=1/10 := by norm_num [p146,Params.toReal]
 have hi : GlobalSource (p146.toReal.state (((cells146 0).2:ℝ)/(p146.den:ℝ))).B (p146.toReal.state (((cells146 0).2:ℝ)/(p146.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p146,cells146,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells146 0).1 < (cells146 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p146) hw0 heps hcap (commonSigns146 0) (highSigns146 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns146 0)
   (u:=((cells146 0).1:ℝ)/(p146.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p146.toReal.state (((cells146 0).1:ℝ)/(p146.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(401970757713392798624863476753/1000000000000000000000000000000:ℝ)) (by norm_num [p146,cells146,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p146,cells146,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source147 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1958230134251583178889500000000000000000000000000000/1962864011715162064110035612797149431089216326148761:ℝ) (1000000000000000000000000000000/401970757713392798624863476753:ℝ) (1/10:ℝ)) :
 GlobalSource (652648013093567875106750000000000000000000000000000/654204812271324257608515155386894274940579732489551:ℝ) (500000000000000000000000000000/201030492689967953465767358671:ℝ) (1/10:ℝ) := by
 have heps : 0<p147.toReal.eps := by norm_num [p147,Params.toReal]
 have hcap : p147.toReal.cap=1/10 := by norm_num [p147,Params.toReal]
 have hi : GlobalSource (p147.toReal.state (((cells147 0).2:ℝ)/(p147.den:ℝ))).B (p147.toReal.state (((cells147 0).2:ℝ)/(p147.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p147,cells147,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells147 0).1 < (cells147 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p147) hw0 heps hcap (commonSigns147 0) (highSigns147 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns147 0)
   (u:=((cells147 0).1:ℝ)/(p147.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p147.toReal.state (((cells147 0).1:ℝ)/(p147.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(201030492689967953465767358671/500000000000000000000000000000:ℝ)) (by norm_num [p147,cells147,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p147,cells147,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source148 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (652648013093567875106750000000000000000000000000000/654204812271324257608515155386894274940579732489551:ℝ) (500000000000000000000000000000/201030492689967953465767358671:ℝ) (1/10:ℝ)) :
 GlobalSource (26454837085267892861500000000000000000000000000000/26518444950862545339825589987259873575922479921299:ℝ) (1000000000000000000000000000000/402151289735138261648297193771:ℝ) (1/10:ℝ) := by
 have heps : 0<p148.toReal.eps := by norm_num [p148,Params.toReal]
 have hcap : p148.toReal.cap=1/10 := by norm_num [p148,Params.toReal]
 have hi : GlobalSource (p148.toReal.state (((cells148 0).2:ℝ)/(p148.den:ℝ))).B (p148.toReal.state (((cells148 0).2:ℝ)/(p148.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p148,cells148,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells148 0).1 < (cells148 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p148) hw0 heps hcap (commonSigns148 0) (highSigns148 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns148 0)
   (u:=((cells148 0).1:ℝ)/(p148.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p148.toReal.state (((cells148 0).1:ℝ)/(p148.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(402151289735138261648297193771/1000000000000000000000000000000:ℝ)) (by norm_num [p148,cells148,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p148,cells148,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (20404190877013982146125000000000000000000000000000/20451701613615147980541431400315629750785834406299:ℝ) (250000000000000000000000000000/100447633032613371288347966507:ℝ) (1/10:ℝ)) :
 GlobalSource (26454837085267892861500000000000000000000000000000/26518444950862545339825589987259873575922479921299:ℝ) (1000000000000000000000000000000/402151289735138261648297193771:ℝ) (1/10:ℝ) := by
 have h145 := source145 hβ hp
 have h146 := source146 hβ h145
 have h147 := source147 hβ h146
 have h148 := source148 hβ h147
 exact h148
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0145_0148
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0149_0152
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0149_0152

theorem source149 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (26454837085267892861500000000000000000000000000000/26518444950862545339825589987259873575922479921299:ℝ) (1000000000000000000000000000000/402151289735138261648297193771:ℝ) (1/10:ℝ)) :
 GlobalSource (3914743698677889036363500000000000000000000000000000/3924230960711470158514421259801647265881201351112597:ℝ) (1000000000000000000000000000000/402241670858117205384847565937:ℝ) (1/10:ℝ) := by
 have heps : 0<p149.toReal.eps := by norm_num [p149,Params.toReal]
 have hcap : p149.toReal.cap=1/10 := by norm_num [p149,Params.toReal]
 have hi : GlobalSource (p149.toReal.state (((cells149 0).2:ℝ)/(p149.den:ℝ))).B (p149.toReal.state (((cells149 0).2:ℝ)/(p149.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p149,cells149,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells149 0).1 < (cells149 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p149) hw0 heps hcap (commonSigns149 0) (highSigns149 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns149 0)
   (u:=((cells149 0).1:ℝ)/(p149.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p149.toReal.state (((cells149 0).1:ℝ)/(p149.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(402241670858117205384847565937/1000000000000000000000000000000:ℝ)) (by norm_num [p149,cells149,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p149,cells149,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source150 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3914743698677889036363500000000000000000000000000000/3924230960711470158514421259801647265881201351112597:ℝ) (1000000000000000000000000000000/402241670858117205384847565937:ℝ) (1/10:ℝ)) :
 GlobalSource (2609447672490753286150000000000000000000000000000/2615821465041039823457027004063360826393908147009:ℝ) (100000000000000000000000000000/40233212882811802700397788001:ℝ) (1/10:ℝ) := by
 have heps : 0<p150.toReal.eps := by norm_num [p150,Params.toReal]
 have hcap : p150.toReal.cap=1/10 := by norm_num [p150,Params.toReal]
 have hi : GlobalSource (p150.toReal.state (((cells150 0).2:ℝ)/(p150.den:ℝ))).B (p150.toReal.state (((cells150 0).2:ℝ)/(p150.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p150,cells150,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells150 0).1 < (cells150 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p150) hw0 heps hcap (commonSigns150 0) (highSigns150 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns150 0)
   (u:=((cells150 0).1:ℝ)/(p150.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p150.toReal.state (((cells150 0).1:ℝ)/(p150.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(40233212882811802700397788001/100000000000000000000000000000:ℝ)) (by norm_num [p150,cells150,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p150,cells150,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source151 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (2609447672490753286150000000000000000000000000000/2615821465041039823457027004063360826393908147009:ℝ) (100000000000000000000000000000/40233212882811802700397788001:ℝ) (1/10:ℝ)) :
 GlobalSource (3913599318794370822086500000000000000000000000000000/3923233563260260347642580623470725806189660646700469:ℝ) (1000000000000000000000000000000/402422663724514161665878614051:ℝ) (1/10:ℝ) := by
 have heps : 0<p151.toReal.eps := by norm_num [p151,Params.toReal]
 have hcap : p151.toReal.cap=1/10 := by norm_num [p151,Params.toReal]
 have hi : GlobalSource (p151.toReal.state (((cells151 0).2:ℝ)/(p151.den:ℝ))).B (p151.toReal.state (((cells151 0).2:ℝ)/(p151.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p151,cells151,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells151 0).1 < (cells151 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p151) hw0 heps hcap (commonSigns151 0) (highSigns151 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns151 0)
   (u:=((cells151 0).1:ℝ)/(p151.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p151.toReal.state (((cells151 0).1:ℝ)/(p151.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(402422663724514161665878614051/1000000000000000000000000000000:ℝ)) (by norm_num [p151,cells151,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p151,cells151,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source152 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3913599318794370822086500000000000000000000000000000/3923233563260260347642580623470725806189660646700469:ℝ) (1000000000000000000000000000000/402422663724514161665878614051:ℝ) (1/10:ℝ)) :
 GlobalSource (489128391106576464368500000000000000000000000000000/490341882223758465028956286573032736635394944481227:ℝ) (1000000000000000000000000000000/402513275626807391356543523757:ℝ) (1/10:ℝ) := by
 have heps : 0<p152.toReal.eps := by norm_num [p152,Params.toReal]
 have hcap : p152.toReal.cap=1/10 := by norm_num [p152,Params.toReal]
 have hi : GlobalSource (p152.toReal.state (((cells152 0).2:ℝ)/(p152.den:ℝ))).B (p152.toReal.state (((cells152 0).2:ℝ)/(p152.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p152,cells152,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells152 0).1 < (cells152 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p152) hw0 heps hcap (commonSigns152 0) (highSigns152 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns152 0)
   (u:=((cells152 0).1:ℝ)/(p152.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p152.toReal.state (((cells152 0).1:ℝ)/(p152.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(402513275626807391356543523757/1000000000000000000000000000000:ℝ)) (by norm_num [p152,cells152,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p152,cells152,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (26454837085267892861500000000000000000000000000000/26518444950862545339825589987259873575922479921299:ℝ) (1000000000000000000000000000000/402151289735138261648297193771:ℝ) (1/10:ℝ)) :
 GlobalSource (489128391106576464368500000000000000000000000000000/490341882223758465028956286573032736635394944481227:ℝ) (1000000000000000000000000000000/402513275626807391356543523757:ℝ) (1/10:ℝ) := by
 have h149 := source149 hβ hp
 have h150 := source150 hβ h149
 have h151 := source151 hβ h150
 have h152 := source152 hβ h151
 exact h152
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0149_0152
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0153_0156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0153_0156

theorem source153 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (489128391106576464368500000000000000000000000000000/490341882223758465028956286573032736635394944481227:ℝ) (1000000000000000000000000000000/402513275626807391356543523757:ℝ) (1/10:ℝ)) :
 GlobalSource (130415164630361753593650000000000000000000000000000/130741222704454604978446978316704993294081163523731:ℝ) (100000000000000000000000000000/40260396461462804589084741649:ℝ) (1/10:ℝ) := by
 have heps : 0<p153.toReal.eps := by norm_num [p153,Params.toReal]
 have hcap : p153.toReal.cap=1/10 := by norm_num [p153,Params.toReal]
 have hi : GlobalSource (p153.toReal.state (((cells153 0).2:ℝ)/(p153.den:ℝ))).B (p153.toReal.state (((cells153 0).2:ℝ)/(p153.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p153,cells153,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells153 0).1 < (cells153 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p153) hw0 heps hcap (commonSigns153 0) (highSigns153 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns153 0)
   (u:=((cells153 0).1:ℝ)/(p153.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p153.toReal.state (((cells153 0).1:ℝ)/(p153.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(40260396461462804589084741649/100000000000000000000000000000:ℝ)) (by norm_num [p153,cells153,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p153,cells153,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source154 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (130415164630361753593650000000000000000000000000000/130741222704454604978446978316704993294081163523731:ℝ) (100000000000000000000000000000/40260396461462804589084741649:ℝ) (1/10:ℝ)) :
 GlobalSource (244492671810568343791937500000000000000000000000000/245108652079611766194255539314916392671853585396647:ℝ) (125000000000000000000000000000/50336841345966900550317802819:ℝ) (1/10:ℝ) := by
 have heps : 0<p154.toReal.eps := by norm_num [p154,Params.toReal]
 have hcap : p154.toReal.cap=1/10 := by norm_num [p154,Params.toReal]
 have hi : GlobalSource (p154.toReal.state (((cells154 0).2:ℝ)/(p154.den:ℝ))).B (p154.toReal.state (((cells154 0).2:ℝ)/(p154.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p154,cells154,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells154 0).1 < (cells154 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p154) hw0 heps hcap (commonSigns154 0) (highSigns154 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns154 0)
   (u:=((cells154 0).1:ℝ)/(p154.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p154.toReal.state (((cells154 0).1:ℝ)/(p154.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(50336841345966900550317802819/125000000000000000000000000000:ℝ)) (by norm_num [p154,cells154,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p154,cells154,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source155 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (244492671810568343791937500000000000000000000000000/245108652079611766194255539314916392671853585396647:ℝ) (125000000000000000000000000000/50336841345966900550317802819:ℝ) (1/10:ℝ)) :
 GlobalSource (3930965385957119993500000000000000000000000000000/3940945039390446992556147750722957349044976331971:ℝ) (1000000000000000000000000000000/402785574166016897327645803611:ℝ) (1/10:ℝ) := by
 have heps : 0<p155.toReal.eps := by norm_num [p155,Params.toReal]
 have hcap : p155.toReal.cap=1/10 := by norm_num [p155,Params.toReal]
 have hi : GlobalSource (p155.toReal.state (((cells155 0).2:ℝ)/(p155.den:ℝ))).B (p155.toReal.state (((cells155 0).2:ℝ)/(p155.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p155,cells155,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells155 0).1 < (cells155 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p155) hw0 heps hcap (commonSigns155 0) (highSigns155 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns155 0)
   (u:=((cells155 0).1:ℝ)/(p155.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p155.toReal.state (((cells155 0).1:ℝ)/(p155.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(402785574166016897327645803611/1000000000000000000000000000000:ℝ)) (by norm_num [p155,cells155,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p155,cells155,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source156 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3930965385957119993500000000000000000000000000000/3940945039390446992556147750722957349044976331971:ℝ) (1000000000000000000000000000000/402785574166016897327645803611:ℝ) (1/10:ℝ)) :
 GlobalSource (81473716022616151799875000000000000000000000000000/81682131747414462368315591663657610680154863270549:ℝ) (250000000000000000000000000000/100719123722372577216089291617:ℝ) (1/10:ℝ) := by
 have heps : 0<p156.toReal.eps := by norm_num [p156,Params.toReal]
 have hcap : p156.toReal.cap=1/10 := by norm_num [p156,Params.toReal]
 have hi : GlobalSource (p156.toReal.state (((cells156 0).2:ℝ)/(p156.den:ℝ))).B (p156.toReal.state (((cells156 0).2:ℝ)/(p156.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p156,cells156,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells156 0).1 < (cells156 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p156) hw0 heps hcap (commonSigns156 0) (highSigns156 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns156 0)
   (u:=((cells156 0).1:ℝ)/(p156.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p156.toReal.state (((cells156 0).1:ℝ)/(p156.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(100719123722372577216089291617/250000000000000000000000000000:ℝ)) (by norm_num [p156,cells156,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p156,cells156,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (489128391106576464368500000000000000000000000000000/490341882223758465028956286573032736635394944481227:ℝ) (1000000000000000000000000000000/402513275626807391356543523757:ℝ) (1/10:ℝ)) :
 GlobalSource (81473716022616151799875000000000000000000000000000/81682131747414462368315591663657610680154863270549:ℝ) (250000000000000000000000000000/100719123722372577216089291617:ℝ) (1/10:ℝ) := by
 have h153 := source153 hβ hp
 have h154 := source154 hβ h153
 have h155 := source155 hβ h154
 have h156 := source156 hβ h155
 exact h156
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0153_0156
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0157_0160
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0157_0160

theorem source157 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (81473716022616151799875000000000000000000000000000/81682131747414462368315591663657610680154863270549:ℝ) (250000000000000000000000000000/100719123722372577216089291617:ℝ) (1/10:ℝ)) :
 GlobalSource (3910166179143816179255500000000000000000000000000000/3920244462304282714297779575903361332977821782072079:ℝ) (1000000000000000000000000000000/402967493018301979914643923563:ℝ) (1/10:ℝ) := by
 have heps : 0<p157.toReal.eps := by norm_num [p157,Params.toReal]
 have hcap : p157.toReal.cap=1/10 := by norm_num [p157,Params.toReal]
 have hi : GlobalSource (p157.toReal.state (((cells157 0).2:ℝ)/(p157.den:ℝ))).B (p157.toReal.state (((cells157 0).2:ℝ)/(p157.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p157,cells157,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells157 0).1 < (cells157 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p157) hw0 heps hcap (commonSigns157 0) (highSigns157 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns157 0)
   (u:=((cells157 0).1:ℝ)/(p157.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p157.toReal.state (((cells157 0).1:ℝ)/(p157.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(402967493018301979914643923563/1000000000000000000000000000000:ℝ)) (by norm_num [p157,cells157,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p157,cells157,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source158 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3910166179143816179255500000000000000000000000000000/3920244462304282714297779575903361332977821782072079:ℝ) (1000000000000000000000000000000/402967493018301979914643923563:ℝ) (1/10:ℝ)) :
 GlobalSource (1954796994601028536058500000000000000000000000000000/1959873364731057911275658974649856761561214491152827:ℝ) (1000000000000000000000000000000/403058568632728011539699037877:ℝ) (1/10:ℝ) := by
 have heps : 0<p158.toReal.eps := by norm_num [p158,Params.toReal]
 have hcap : p158.toReal.cap=1/10 := by norm_num [p158,Params.toReal]
 have hi : GlobalSource (p158.toReal.state (((cells158 0).2:ℝ)/(p158.den:ℝ))).B (p158.toReal.state (((cells158 0).2:ℝ)/(p158.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p158,cells158,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells158 0).1 < (cells158 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p158) hw0 heps hcap (commonSigns158 0) (highSigns158 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns158 0)
   (u:=((cells158 0).1:ℝ)/(p158.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p158.toReal.state (((cells158 0).1:ℝ)/(p158.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(403058568632728011539699037877/1000000000000000000000000000000:ℝ)) (by norm_num [p158,cells158,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p158,cells158,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source159 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1954796994601028536058500000000000000000000000000000/1959873364731057911275658974649856761561214491152827:ℝ) (1000000000000000000000000000000/403058568632728011539699037877:ℝ) (1/10:ℝ)) :
 GlobalSource (1303007266420099321659500000000000000000000000000000/1306416375111002712021385349079434135233230706034467:ℝ) (1000000000000000000000000000000/403149721813174268871734703431:ℝ) (1/10:ℝ) := by
 have heps : 0<p159.toReal.eps := by norm_num [p159,Params.toReal]
 have hcap : p159.toReal.cap=1/10 := by norm_num [p159,Params.toReal]
 have hi : GlobalSource (p159.toReal.state (((cells159 0).2:ℝ)/(p159.den:ℝ))).B (p159.toReal.state (((cells159 0).2:ℝ)/(p159.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p159,cells159,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells159 0).1 < (cells159 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p159) hw0 heps hcap (commonSigns159 0) (highSigns159 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns159 0)
   (u:=((cells159 0).1:ℝ)/(p159.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p159.toReal.state (((cells159 0).1:ℝ)/(p159.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(403149721813174268871734703431/1000000000000000000000000000000:ℝ)) (by norm_num [p159,cells159,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p159,cells159,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source160 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1303007266420099321659500000000000000000000000000000/1306416375111002712021385349079434135233230706034467:ℝ) (1000000000000000000000000000000/403149721813174268871734703431:ℝ) (1/10:ℝ)) :
 GlobalSource (6106952514560216965375000000000000000000000000000/6123049452969895540942021533550017368223516921897:ℝ) (500000000000000000000000000000/201620476320088292773616622101:ℝ) (1/10:ℝ) := by
 have heps : 0<p160.toReal.eps := by norm_num [p160,Params.toReal]
 have hcap : p160.toReal.cap=1/10 := by norm_num [p160,Params.toReal]
 have hi : GlobalSource (p160.toReal.state (((cells160 0).2:ℝ)/(p160.den:ℝ))).B (p160.toReal.state (((cells160 0).2:ℝ)/(p160.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p160,cells160,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells160 0).1 < (cells160 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p160) hw0 heps hcap (commonSigns160 0) (highSigns160 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns160 0)
   (u:=((cells160 0).1:ℝ)/(p160.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p160.toReal.state (((cells160 0).1:ℝ)/(p160.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(201620476320088292773616622101/500000000000000000000000000000:ℝ)) (by norm_num [p160,cells160,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p160,cells160,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (81473716022616151799875000000000000000000000000000/81682131747414462368315591663657610680154863270549:ℝ) (250000000000000000000000000000/100719123722372577216089291617:ℝ) (1/10:ℝ)) :
 GlobalSource (6106952514560216965375000000000000000000000000000/6123049452969895540942021533550017368223516921897:ℝ) (500000000000000000000000000000/201620476320088292773616622101:ℝ) (1/10:ℝ) := by
 have h157 := source157 hβ hp
 have h158 := source158 hβ h157
 have h159 := source159 hβ h158
 have h160 := source160 hβ h159
 exact h160
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0157_0160
