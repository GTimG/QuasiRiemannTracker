/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0193_0196
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0197_0200
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0201_0204
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0205_0208
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0193_0196
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0193_0196

theorem source193 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (31847346383709563846153500000000000000000000000000000/31954758286401105134705797158311006256122268822053619:ℝ) (1000000000000000000000000000000/406616555786611362039041869963:ℝ) (1/10:ℝ)) :
 GlobalSource (663095767993708362988315250000000000000000000000000000/665388172518206823866952525823521421502924660744447337:ℝ) (500000000000000000000000000000/203496983782784598405437298639:ℝ) (1/10:ℝ) := by
 have heps : 0<p193.toReal.eps := by norm_num [p193,Params.toReal]
 have hcap : p193.toReal.cap=1/10 := by norm_num [p193,Params.toReal]
 have hi : GlobalSource (p193.toReal.state (((cells193 0).2:ℝ)/(p193.den:ℝ))).B (p193.toReal.state (((cells193 0).2:ℝ)/(p193.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p193,cells193,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells193 0).1 < (cells193 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p193) hw0 heps hcap (commonSigns193 0) (highSigns193 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns193 0)
   (u:=((cells193 0).1:ℝ)/(p193.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p193.toReal.state (((cells193 0).1:ℝ)/(p193.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(203496983782784598405437298639/500000000000000000000000000000:ℝ)) (by norm_num [p193,cells193,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p193,cells193,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source194 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (663095767993708362988315250000000000000000000000000000/665388172518206823866952525823521421502924660744447337:ℝ) (500000000000000000000000000000/203496983782784598405437298639:ℝ) (1/10:ℝ)) :
 GlobalSource (16098100882432408401176500000000000000000000000000000/16155124714497451898861168049226140925221627982652157:ℝ) (1000000000000000000000000000000/407372720249875585080767218223:ℝ) (1/10:ℝ) := by
 have heps : 0<p194.toReal.eps := by norm_num [p194,Params.toReal]
 have hcap : p194.toReal.cap=1/10 := by norm_num [p194,Params.toReal]
 have hi : GlobalSource (p194.toReal.state (((cells194 0).2:ℝ)/(p194.den:ℝ))).B (p194.toReal.state (((cells194 0).2:ℝ)/(p194.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p194,cells194,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells194 0).1 < (cells194 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p194) hw0 heps hcap (commonSigns194 0) (highSigns194 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns194 0)
   (u:=((cells194 0).1:ℝ)/(p194.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p194.toReal.state (((cells194 0).1:ℝ)/(p194.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(407372720249875585080767218223/1000000000000000000000000000000:ℝ)) (by norm_num [p194,cells194,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p194,cells194,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source195 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (16098100882432408401176500000000000000000000000000000/16155124714497451898861168049226140925221627982652157:ℝ) (1000000000000000000000000000000/407372720249875585080767218223:ℝ) (1/10:ℝ)) :
 GlobalSource (3973887227959359572251299500000000000000000000000000000/3988305096949303405535441697820899871686541082644466943:ℝ) (1000000000000000000000000000000/407752819933095108694406252419:ℝ) (1/10:ℝ) := by
 have heps : 0<p195.toReal.eps := by norm_num [p195,Params.toReal]
 have hcap : p195.toReal.cap=1/10 := by norm_num [p195,Params.toReal]
 have hi : GlobalSource (p195.toReal.state (((cells195 0).2:ℝ)/(p195.den:ℝ))).B (p195.toReal.state (((cells195 0).2:ℝ)/(p195.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p195,cells195,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells195 0).1 < (cells195 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p195) hw0 heps hcap (commonSigns195 0) (highSigns195 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns195 0)
   (u:=((cells195 0).1:ℝ)/(p195.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p195.toReal.state (((cells195 0).1:ℝ)/(p195.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(407752819933095108694406252419/1000000000000000000000000000000:ℝ)) (by norm_num [p195,cells195,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p195,cells195,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source196 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3973887227959359572251299500000000000000000000000000000/3988305096949303405535441697820899871686541082644466943:ℝ) (1000000000000000000000000000000/407752819933095108694406252419:ℝ) (1/10:ℝ)) :
 GlobalSource (1323847845985971423137334500000000000000000000000000000/1328765638518700366237366617165406180859492753784682163:ℝ) (1000000000000000000000000000000/408134272744630933361625856309:ℝ) (1/10:ℝ) := by
 have heps : 0<p196.toReal.eps := by norm_num [p196,Params.toReal]
 have hcap : p196.toReal.cap=1/10 := by norm_num [p196,Params.toReal]
 have hi : GlobalSource (p196.toReal.state (((cells196 0).2:ℝ)/(p196.den:ℝ))).B (p196.toReal.state (((cells196 0).2:ℝ)/(p196.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p196,cells196,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells196 0).1 < (cells196 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p196) hw0 heps hcap (commonSigns196 0) (highSigns196 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns196 0)
   (u:=((cells196 0).1:ℝ)/(p196.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p196.toReal.state (((cells196 0).1:ℝ)/(p196.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(408134272744630933361625856309/1000000000000000000000000000000:ℝ)) (by norm_num [p196,cells196,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p196,cells196,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (31847346383709563846153500000000000000000000000000000/31954758286401105134705797158311006256122268822053619:ℝ) (1000000000000000000000000000000/406616555786611362039041869963:ℝ) (1/10:ℝ)) :
 GlobalSource (1323847845985971423137334500000000000000000000000000000/1328765638518700366237366617165406180859492753784682163:ℝ) (1000000000000000000000000000000/408134272744630933361625856309:ℝ) (1/10:ℝ) := by
 have h193 := source193 hβ hp
 have h194 := source194 hβ h193
 have h195 := source195 hβ h194
 have h196 := source196 hβ h195
 exact h196
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0193_0196
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0197_0200
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0197_0200

theorem source197 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1323847845985971423137334500000000000000000000000000000/1328765638518700366237366617165406180859492753784682163:ℝ) (1000000000000000000000000000000/408134272744630933361625856309:ℝ) (1/10:ℝ)) :
 GlobalSource (793839969591293793314541500000000000000000000000000000/796858252670027693883684292282756176040628351138962599:ℝ) (1000000000000000000000000000000/408517084849985983237122016951:ℝ) (1/10:ℝ) := by
 have heps : 0<p197.toReal.eps := by norm_num [p197,Params.toReal]
 have hcap : p197.toReal.cap=1/10 := by norm_num [p197,Params.toReal]
 have hi : GlobalSource (p197.toReal.state (((cells197 0).2:ℝ)/(p197.den:ℝ))).B (p197.toReal.state (((cells197 0).2:ℝ)/(p197.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p197,cells197,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells197 0).1 < (cells197 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p197) hw0 heps hcap (commonSigns197 0) (highSigns197 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns197 0)
   (u:=((cells197 0).1:ℝ)/(p197.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p197.toReal.state (((cells197 0).1:ℝ)/(p197.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(408517084849985983237122016951/1000000000000000000000000000000:ℝ)) (by norm_num [p197,cells197,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p197,cells197,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source198 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (793839969591293793314541500000000000000000000000000000/796858252670027693883684292282756176040628351138962599:ℝ) (1000000000000000000000000000000/408517084849985983237122016951:ℝ) (1/10:ℝ)) :
 GlobalSource (3966856157955023663733411500000000000000000000000000000/3982288143387630834093315769111709225486138466947542599:ℝ) (1000000000000000000000000000000/408901262451026394124445433771:ℝ) (1/10:ℝ) := by
 have heps : 0<p198.toReal.eps := by norm_num [p198,Params.toReal]
 have hcap : p198.toReal.cap=1/10 := by norm_num [p198,Params.toReal]
 have hi : GlobalSource (p198.toReal.state (((cells198 0).2:ℝ)/(p198.den:ℝ))).B (p198.toReal.state (((cells198 0).2:ℝ)/(p198.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p198,cells198,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells198 0).1 < (cells198 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p198) hw0 heps hcap (commonSigns198 0) (highSigns198 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns198 0)
   (u:=((cells198 0).1:ℝ)/(p198.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p198.toReal.state (((cells198 0).1:ℝ)/(p198.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(408901262451026394124445433771/1000000000000000000000000000000:ℝ)) (by norm_num [p198,cells198,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p198,cells198,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source199 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3966856157955023663733411500000000000000000000000000000/3982288143387630834093315769111709225486138466947542599:ℝ) (1000000000000000000000000000000/408901262451026394124445433771:ℝ) (1/10:ℝ)) :
 GlobalSource (1321504155984526120298038500000000000000000000000000000/1326762519577387260744937345825089286923772524401957701:ℝ) (1000000000000000000000000000000/409286811786247268507804676371:ℝ) (1/10:ℝ) := by
 have heps : 0<p199.toReal.eps := by norm_num [p199,Params.toReal]
 have hcap : p199.toReal.cap=1/10 := by norm_num [p199,Params.toReal]
 have hi : GlobalSource (p199.toReal.state (((cells199 0).2:ℝ)/(p199.den:ℝ))).B (p199.toReal.state (((cells199 0).2:ℝ)/(p199.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p199,cells199,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells199 0).1 < (cells199 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p199) hw0 heps hcap (commonSigns199 0) (highSigns199 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns199 0)
   (u:=((cells199 0).1:ℝ)/(p199.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p199.toReal.state (((cells199 0).1:ℝ)/(p199.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(409286811786247268507804676371/1000000000000000000000000000000:ℝ)) (by norm_num [p199,cells199,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p199,cells199,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source200 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1321504155984526120298038500000000000000000000000000000/1326762519577387260744937345825089286923772524401957701:ℝ) (1000000000000000000000000000000/409286811786247268507804676371:ℝ) (1/10:ℝ)) :
 GlobalSource (3962168777952133058054819500000000000000000000000000000/3978289512454711062104956043597767862066898539016823641:ℝ) (1000000000000000000000000000000/409673739131040755886911757173:ℝ) (1/10:ℝ) := by
 have heps : 0<p200.toReal.eps := by norm_num [p200,Params.toReal]
 have hcap : p200.toReal.cap=1/10 := by norm_num [p200,Params.toReal]
 have hi : GlobalSource (p200.toReal.state (((cells200 0).2:ℝ)/(p200.den:ℝ))).B (p200.toReal.state (((cells200 0).2:ℝ)/(p200.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p200,cells200,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells200 0).1 < (cells200 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p200) hw0 heps hcap (commonSigns200 0) (highSigns200 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns200 0)
   (u:=((cells200 0).1:ℝ)/(p200.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p200.toReal.state (((cells200 0).1:ℝ)/(p200.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(409673739131040755886911757173/1000000000000000000000000000000:ℝ)) (by norm_num [p200,cells200,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p200,cells200,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1323847845985971423137334500000000000000000000000000000/1328765638518700366237366617165406180859492753784682163:ℝ) (1000000000000000000000000000000/408134272744630933361625856309:ℝ) (1/10:ℝ)) :
 GlobalSource (3962168777952133058054819500000000000000000000000000000/3978289512454711062104956043597767862066898539016823641:ℝ) (1000000000000000000000000000000/409673739131040755886911757173:ℝ) (1/10:ℝ) := by
 have h197 := source197 hβ hp
 have h198 := source198 hβ h197
 have h199 := source199 hβ h198
 have h200 := source200 hβ h199
 exact h200
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0197_0200
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0201_0204
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0201_0204

theorem source201 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3962168777952133058054819500000000000000000000000000000/3978289512454711062104956043597767862066898539016823641:ℝ) (1000000000000000000000000000000/409673739131040755886911757173:ℝ) (1/10:ℝ)) :
 GlobalSource (123744533998458992350485109375000000000000000000000000/124259187738552582064153199927814760576020705138322323:ℝ) (31250000000000000000000000000/12814439087436452567636584903:ℝ) (1/10:ℝ) := by
 have heps : 0<p201.toReal.eps := by norm_num [p201,Params.toReal]
 have hcap : p201.toReal.cap=1/10 := by norm_num [p201,Params.toReal]
 have hi : GlobalSource (p201.toReal.state (((cells201 0).2:ℝ)/(p201.den:ℝ))).B (p201.toReal.state (((cells201 0).2:ℝ)/(p201.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p201,cells201,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells201 0).1 < (cells201 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p201) hw0 heps hcap (commonSigns201 0) (highSigns201 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns201 0)
   (u:=((cells201 0).1:ℝ)/(p201.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p201.toReal.state (((cells201 0).1:ℝ)/(p201.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(12814439087436452567636584903/31250000000000000000000000000:ℝ)) (by norm_num [p201,cells201,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p201,cells201,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source202 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (123744533998458992350485109375000000000000000000000000/124259187738552582064153199927814760576020705138322323:ℝ) (31250000000000000000000000000/12814439087436452567636584903:ℝ) (1/10:ℝ)) :
 GlobalSource (65958023299154040872937125000000000000000000000000000/66238350789248880614640499338792823407483724678327059:ℝ) (250000000000000000000000000000/102612938284256088028249700649:ℝ) (1/10:ℝ) := by
 have heps : 0<p202.toReal.eps := by norm_num [p202,Params.toReal]
 have hcap : p202.toReal.cap=1/10 := by norm_num [p202,Params.toReal]
 have hi : GlobalSource (p202.toReal.state (((cells202 0).2:ℝ)/(p202.den:ℝ))).B (p202.toReal.state (((cells202 0).2:ℝ)/(p202.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p202,cells202,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells202 0).1 < (cells202 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p202) hw0 heps hcap (commonSigns202 0) (highSigns202 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns202 0)
   (u:=((cells202 0).1:ℝ)/(p202.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p202.toReal.state (((cells202 0).1:ℝ)/(p202.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(102612938284256088028249700649/250000000000000000000000000000:ℝ)) (by norm_num [p202,cells202,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p202,cells202,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source203 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (65958023299154040872937125000000000000000000000000000/66238350789248880614640499338792823407483724678327059:ℝ) (250000000000000000000000000000/102612938284256088028249700649:ℝ) (1/10:ℝ)) :
 GlobalSource (791027541589559429907386300000000000000000000000000000/794462126942359767335487924188925892782969518633753103:ℝ) (200000000000000000000000000000/82168570507185949846406559827:ℝ) (1/10:ℝ) := by
 have heps : 0<p203.toReal.eps := by norm_num [p203,Params.toReal]
 have hcap : p203.toReal.cap=1/10 := by norm_num [p203,Params.toReal]
 have hi : GlobalSource (p203.toReal.state (((cells203 0).2:ℝ)/(p203.den:ℝ))).B (p203.toReal.state (((cells203 0).2:ℝ)/(p203.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p203,cells203,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells203 0).1 < (cells203 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p203) hw0 heps hcap (commonSigns203 0) (highSigns203 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns203 0)
   (u:=((cells203 0).1:ℝ)/(p203.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p203.toReal.state (((cells203 0).1:ℝ)/(p203.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(82168570507185949846406559827/200000000000000000000000000000:ℝ)) (by norm_num [p203,cells203,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p203,cells203,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source204 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (791027541589559429907386300000000000000000000000000000/794462126942359767335487924188925892782969518633753103:ℝ) (200000000000000000000000000000/82168570507185949846406559827:ℝ) (1/10:ℝ)) :
 GlobalSource (395279401794635184669763550000000000000000000000000000/397032277280512707963068715370385135028118688322104487:ℝ) (100000000000000000000000000000/41123535542039115758646441099:ℝ) (1/10:ℝ) := by
 have heps : 0<p204.toReal.eps := by norm_num [p204,Params.toReal]
 have hcap : p204.toReal.cap=1/10 := by norm_num [p204,Params.toReal]
 have hi : GlobalSource (p204.toReal.state (((cells204 0).2:ℝ)/(p204.den:ℝ))).B (p204.toReal.state (((cells204 0).2:ℝ)/(p204.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p204,cells204,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells204 0).1 < (cells204 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p204) hw0 heps hcap (commonSigns204 0) (highSigns204 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns204 0)
   (u:=((cells204 0).1:ℝ)/(p204.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p204.toReal.state (((cells204 0).1:ℝ)/(p204.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(41123535542039115758646441099/100000000000000000000000000000:ℝ)) (by norm_num [p204,cells204,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p204,cells204,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3962168777952133058054819500000000000000000000000000000/3978289512454711062104956043597767862066898539016823641:ℝ) (1000000000000000000000000000000/409673739131040755886911757173:ℝ) (1/10:ℝ)) :
 GlobalSource (395279401794635184669763550000000000000000000000000000/397032277280512707963068715370385135028118688322104487:ℝ) (100000000000000000000000000000/41123535542039115758646441099:ℝ) (1/10:ℝ) := by
 have h201 := source201 hβ hp
 have h202 := source202 hβ h201
 have h203 := source203 hβ h202
 have h204 := source204 hβ h203
 exact h204
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0201_0204
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0205_0208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0205_0208

theorem source205 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (395279401794635184669763550000000000000000000000000000/397032277280512707963068715370385135028118688322104487:ℝ) (100000000000000000000000000000/41123535542039115758646441099:ℝ) (1/10:ℝ)) :
 GlobalSource (329204193995408878654861625000000000000000000000000000/330694788728608502518088928316374028407408813700139307:ℝ) (250000000000000000000000000000/102907317063597557628205883133:ℝ) (1/10:ℝ) := by
 have heps : 0<p205.toReal.eps := by norm_num [p205,Params.toReal]
 have hcap : p205.toReal.cap=1/10 := by norm_num [p205,Params.toReal]
 have hi : GlobalSource (p205.toReal.state (((cells205 0).2:ℝ)/(p205.den:ℝ))).B (p205.toReal.state (((cells205 0).2:ℝ)/(p205.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p205,cells205,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells205 0).1 < (cells205 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p205) hw0 heps hcap (commonSigns205 0) (highSigns205 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns205 0)
   (u:=((cells205 0).1:ℝ)/(p205.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p205.toReal.state (((cells205 0).1:ℝ)/(p205.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(102907317063597557628205883133/250000000000000000000000000000:ℝ)) (by norm_num [p205,cells205,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p205,cells205,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source206 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (329204193995408878654861625000000000000000000000000000/330694788728608502518088928316374028407408813700139307:ℝ) (250000000000000000000000000000/102907317063597557628205883133:ℝ) (1/10:ℝ)) :
 GlobalSource (3948106637943461241019043500000000000000000000000000000/3966354713642275028353205618614273493777318681813678163:ℝ) (1000000000000000000000000000000/412024597540464331367642952583:ℝ) (1/10:ℝ) := by
 have heps : 0<p206.toReal.eps := by norm_num [p206,Params.toReal]
 have hcap : p206.toReal.cap=1/10 := by norm_num [p206,Params.toReal]
 have hi : GlobalSource (p206.toReal.state (((cells206 0).2:ℝ)/(p206.den:ℝ))).B (p206.toReal.state (((cells206 0).2:ℝ)/(p206.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p206,cells206,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells206 0).1 < (cells206 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p206) hw0 heps hcap (commonSigns206 0) (highSigns206 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns206 0)
   (u:=((cells206 0).1:ℝ)/(p206.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p206.toReal.state (((cells206 0).1:ℝ)/(p206.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(412024597540464331367642952583/1000000000000000000000000000000:ℝ)) (by norm_num [p206,cells206,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p206,cells206,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source207 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3948106637943461241019043500000000000000000000000000000/3966354713642275028353205618614273493777318681813678163:ℝ) (1000000000000000000000000000000/412024597540464331367642952583:ℝ) (1/10:ℝ)) :
 GlobalSource (789152589588403187635949500000000000000000000000000000/792874904525118664596389603066961083571161179809558867:ℝ) (1000000000000000000000000000000/412421349819991571791649602211:ℝ) (1/10:ℝ) := by
 have heps : 0<p207.toReal.eps := by norm_num [p207,Params.toReal]
 have hcap : p207.toReal.cap=1/10 := by norm_num [p207,Params.toReal]
 have hi : GlobalSource (p207.toReal.state (((cells207 0).2:ℝ)/(p207.den:ℝ))).B (p207.toReal.state (((cells207 0).2:ℝ)/(p207.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p207,cells207,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells207 0).1 < (cells207 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p207) hw0 heps hcap (commonSigns207 0) (highSigns207 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns207 0)
   (u:=((cells207 0).1:ℝ)/(p207.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p207.toReal.state (((cells207 0).1:ℝ)/(p207.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(412421349819991571791649602211/1000000000000000000000000000000:ℝ)) (by norm_num [p207,cells207,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p207,cells207,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source208 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (789152589588403187635949500000000000000000000000000000/792874904525118664596389603066961083571161179809558867:ℝ) (1000000000000000000000000000000/412421349819991571791649602211:ℝ) (1/10:ℝ)) :
 GlobalSource (164309135747523776472518812500000000000000000000000000/165099870617684553152231418257015945855939933509352879:ℝ) (125000000000000000000000000000/51602441459184796657936738393:ℝ) (1/10:ℝ) := by
 have heps : 0<p208.toReal.eps := by norm_num [p208,Params.toReal]
 have hcap : p208.toReal.cap=1/10 := by norm_num [p208,Params.toReal]
 have hi : GlobalSource (p208.toReal.state (((cells208 0).2:ℝ)/(p208.den:ℝ))).B (p208.toReal.state (((cells208 0).2:ℝ)/(p208.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p208,cells208,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells208 0).1 < (cells208 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p208) hw0 heps hcap (commonSigns208 0) (highSigns208 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns208 0)
   (u:=((cells208 0).1:ℝ)/(p208.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p208.toReal.state (((cells208 0).1:ℝ)/(p208.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(51602441459184796657936738393/125000000000000000000000000000:ℝ)) (by norm_num [p208,cells208,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p208,cells208,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (395279401794635184669763550000000000000000000000000000/397032277280512707963068715370385135028118688322104487:ℝ) (100000000000000000000000000000/41123535542039115758646441099:ℝ) (1/10:ℝ)) :
 GlobalSource (164309135747523776472518812500000000000000000000000000/165099870617684553152231418257015945855939933509352879:ℝ) (125000000000000000000000000000/51602441459184796657936738393:ℝ) (1/10:ℝ) := by
 have h205 := source205 hβ hp
 have h206 := source206 hβ h205
 have h207 := source207 hβ h206
 have h208 := source208 hβ h207
 exact h208
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0205_0208
