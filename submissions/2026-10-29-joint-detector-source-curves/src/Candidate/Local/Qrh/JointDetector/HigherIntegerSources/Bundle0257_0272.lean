/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0257_0260
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0261_0264
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0265_0268
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0269_0272
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0257_0260
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0257_0260

theorem source257 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (255394809191413073270282900000000000000000000000000000/258036563894366693069712298268334175409984560481974163:ℝ) (200000000000000000000000000000/86750601192117361702274244949:ℝ) (1/10:ℝ)) :
 GlobalSource (765715689573950159242989500000000000000000000000000000/773740086218523608672630036009564062550334947526150987:ℝ) (1000000000000000000000000000000/434230198729551490189132372251:ℝ) (1/10:ℝ) := by
 have heps : 0<p257.toReal.eps := by norm_num [p257,Params.toReal]
 have hcap : p257.toReal.cap=1/10 := by norm_num [p257,Params.toReal]
 have hi : GlobalSource (p257.toReal.state (((cells257 0).2:ℝ)/(p257.den:ℝ))).B (p257.toReal.state (((cells257 0).2:ℝ)/(p257.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p257,cells257,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells257 0).1 < (cells257 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p257) hw0 heps hcap (commonSigns257 0) (highSigns257 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns257 0)
   (u:=((cells257 0).1:ℝ)/(p257.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p257.toReal.state (((cells257 0).1:ℝ)/(p257.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(434230198729551490189132372251/1000000000000000000000000000000:ℝ)) (by norm_num [p257,cells257,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p257,cells257,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source258 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (765715689573950159242989500000000000000000000000000000/773740086218523608672630036009564062550334947526150987:ℝ) (1000000000000000000000000000000/434230198729551490189132372251:ℝ) (1/10:ℝ)) :
 GlobalSource (153049390314732219735026060000000000000000000000000000/154674205358666992072558725756449627136553574068582167:ℝ) (40000000000000000000000000000/17388368286865514866993487163:ℝ) (1/10:ℝ) := by
 have heps : 0<p258.toReal.eps := by norm_num [p258,Params.toReal]
 have hcap : p258.toReal.cap=1/10 := by norm_num [p258,Params.toReal]
 have hi : GlobalSource (p258.toReal.state (((cells258 0).2:ℝ)/(p258.den:ℝ))).B (p258.toReal.state (((cells258 0).2:ℝ)/(p258.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p258,cells258,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells258 0).1 < (cells258 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p258) hw0 heps hcap (commonSigns258 0) (highSigns258 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns258 0)
   (u:=((cells258 0).1:ℝ)/(p258.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p258.toReal.state (((cells258 0).1:ℝ)/(p258.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(17388368286865514866993487163/40000000000000000000000000000:ℝ)) (by norm_num [p258,cells258,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p258,cells258,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source259 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (153049390314732219735026060000000000000000000000000000/154674205358666992072558725756449627136553574068582167:ℝ) (40000000000000000000000000000/17388368286865514866993487163:ℝ) (1/10:ℝ)) :
 GlobalSource (1274630355955620063512118500000000000000000000000000000/1288337523533669288321908081440909769334868774259386359:ℝ) (1000000000000000000000000000000/435190040312656472225893564369:ℝ) (1/10:ℝ) := by
 have heps : 0<p259.toReal.eps := by norm_num [p259,Params.toReal]
 have hcap : p259.toReal.cap=1/10 := by norm_num [p259,Params.toReal]
 have hi : GlobalSource (p259.toReal.state (((cells259 0).2:ℝ)/(p259.den:ℝ))).B (p259.toReal.state (((cells259 0).2:ℝ)/(p259.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p259,cells259,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells259 0).1 < (cells259 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p259) hw0 heps hcap (commonSigns259 0) (highSigns259 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns259 0)
   (u:=((cells259 0).1:ℝ)/(p259.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p259.toReal.state (((cells259 0).1:ℝ)/(p259.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(435190040312656472225893564369/1000000000000000000000000000000:ℝ)) (by norm_num [p259,cells259,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p259,cells259,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source260 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1274630355955620063512118500000000000000000000000000000/1288337523533669288321908081440909769334868774259386359:ℝ) (1000000000000000000000000000000/435190040312656472225893564369:ℝ) (1/10:ℝ)) :
 GlobalSource (1910773688932707443848529750000000000000000000000000000/1931586372284189919933880140762871000054702523215712961:ℝ) (500000000000000000000000000000/217836353618367913414140307773:ℝ) (1/10:ℝ) := by
 have heps : 0<p260.toReal.eps := by norm_num [p260,Params.toReal]
 have hcap : p260.toReal.cap=1/10 := by norm_num [p260,Params.toReal]
 have hi : GlobalSource (p260.toReal.state (((cells260 0).2:ℝ)/(p260.den:ℝ))).B (p260.toReal.state (((cells260 0).2:ℝ)/(p260.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p260,cells260,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells260 0).1 < (cells260 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p260) hw0 heps hcap (commonSigns260 0) (highSigns260 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns260 0)
   (u:=((cells260 0).1:ℝ)/(p260.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p260.toReal.state (((cells260 0).1:ℝ)/(p260.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(217836353618367913414140307773/500000000000000000000000000000:ℝ)) (by norm_num [p260,cells260,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p260,cells260,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem prefix0258 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (255394809191413073270282900000000000000000000000000000/258036563894366693069712298268334175409984560481974163:ℝ) (200000000000000000000000000000/86750601192117361702274244949:ℝ) (1/10:ℝ)) :
 GlobalSource (153049390314732219735026060000000000000000000000000000/154674205358666992072558725756449627136553574068582167:ℝ) (40000000000000000000000000000/17388368286865514866993487163:ℝ) (1/10:ℝ) := by
 have h257 := source257 hβ hp
 have h258 := source258 hβ h257
 exact h258

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (255394809191413073270282900000000000000000000000000000/258036563894366693069712298268334175409984560481974163:ℝ) (200000000000000000000000000000/86750601192117361702274244949:ℝ) (1/10:ℝ)) :
 GlobalSource (1910773688932707443848529750000000000000000000000000000/1931586372284189919933880140762871000054702523215712961:ℝ) (500000000000000000000000000000/217836353618367913414140307773:ℝ) (1/10:ℝ) := by
 have h257 := source257 hβ hp
 have h258 := source258 hβ h257
 have h259 := source259 hβ h258
 have h260 := source260 hβ h259
 exact h260
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0257_0260
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0261_0264
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0261_0264

theorem source261 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1910773688932707443848529750000000000000000000000000000/1931586372284189919933880140762871000054702523215712961:ℝ) (500000000000000000000000000000/217836353618367913414140307773:ℝ) (1/10:ℝ)) :
 GlobalSource (1909601843931984792428881750000000000000000000000000000/1930667829725509961223954628301840524405727773666137189:ℝ) (500000000000000000000000000000/218078608543395147847620889169:ℝ) (1/10:ℝ) := by
 have heps : 0<p261.toReal.eps := by norm_num [p261,Params.toReal]
 have hcap : p261.toReal.cap=1/10 := by norm_num [p261,Params.toReal]
 have hi : GlobalSource (p261.toReal.state (((cells261 0).2:ℝ)/(p261.den:ℝ))).B (p261.toReal.state (((cells261 0).2:ℝ)/(p261.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p261,cells261,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells261 0).1 < (cells261 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p261) hw0 heps hcap (commonSigns261 0) (highSigns261 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns261 0)
   (u:=((cells261 0).1:ℝ)/(p261.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p261.toReal.state (((cells261 0).1:ℝ)/(p261.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(218078608543395147847620889169/500000000000000000000000000000:ℝ)) (by norm_num [p261,cells261,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p261,cells261,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source262 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1909601843931984792428881750000000000000000000000000000/1930667829725509961223954628301840524405727773666137189:ℝ) (500000000000000000000000000000/218078608543395147847620889169:ℝ) (1/10:ℝ)) :
 GlobalSource (16963822212722330142304300000000000000000000000000000/17153339194847401661620704028536198518240275918523327:ℝ) (200000000000000000000000000000/87328715812998474657744587463:ℝ) (1/10:ℝ) := by
 have heps : 0<p262.toReal.eps := by norm_num [p262,Params.toReal]
 have hcap : p262.toReal.cap=1/10 := by norm_num [p262,Params.toReal]
 have hi : GlobalSource (p262.toReal.state (((cells262 0).2:ℝ)/(p262.den:ℝ))).B (p262.toReal.state (((cells262 0).2:ℝ)/(p262.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p262,cells262,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells262 0).1 < (cells262 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p262) hw0 heps hcap (commonSigns262 0) (highSigns262 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns262 0)
   (u:=((cells262 0).1:ℝ)/(p262.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p262.toReal.state (((cells262 0).1:ℝ)/(p262.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(87328715812998474657744587463/200000000000000000000000000000:ℝ)) (by norm_num [p262,cells262,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p262,cells262,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source263 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (16963822212722330142304300000000000000000000000000000/17153339194847401661620704028536198518240275918523327:ℝ) (200000000000000000000000000000/87328715812998474657744587463:ℝ) (1/10:ℝ)) :
 GlobalSource (953629076965269744794792875000000000000000000000000000/964417431584650825388115813834020946600422403189928893:ℝ) (250000000000000000000000000000/109282950608312386868871532617:ℝ) (1/10:ℝ) := by
 have heps : 0<p263.toReal.eps := by norm_num [p263,Params.toReal]
 have hcap : p263.toReal.cap=1/10 := by norm_num [p263,Params.toReal]
 have hi : GlobalSource (p263.toReal.state (((cells263 0).2:ℝ)/(p263.den:ℝ))).B (p263.toReal.state (((cells263 0).2:ℝ)/(p263.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p263,cells263,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells263 0).1 < (cells263 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p263) hw0 heps hcap (commonSigns263 0) (highSigns263 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns263 0)
   (u:=((cells263 0).1:ℝ)/(p263.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p263.toReal.state (((cells263 0).1:ℝ)/(p263.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(109282950608312386868871532617/250000000000000000000000000000:ℝ)) (by norm_num [p263,cells263,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p263,cells263,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source264 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (953629076965269744794792875000000000000000000000000000/964417431584650825388115813834020946600422403189928893:ℝ) (250000000000000000000000000000/109282950608312386868871532617:ℝ) (1/10:ℝ)) :
 GlobalSource (3812172617859633676339875500000000000000000000000000000/3855840885555712748768144282875378197833219710339772271:ℝ) (1000000000000000000000000000000/437621896513685760084008851507:ℝ) (1/10:ℝ) := by
 have heps : 0<p264.toReal.eps := by norm_num [p264,Params.toReal]
 have hcap : p264.toReal.cap=1/10 := by norm_num [p264,Params.toReal]
 have hi : GlobalSource (p264.toReal.state (((cells264 0).2:ℝ)/(p264.den:ℝ))).B (p264.toReal.state (((cells264 0).2:ℝ)/(p264.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p264,cells264,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells264 0).1 < (cells264 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p264) hw0 heps hcap (commonSigns264 0) (highSigns264 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns264 0)
   (u:=((cells264 0).1:ℝ)/(p264.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p264.toReal.state (((cells264 0).1:ℝ)/(p264.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(437621896513685760084008851507/1000000000000000000000000000000:ℝ)) (by norm_num [p264,cells264,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p264,cells264,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1910773688932707443848529750000000000000000000000000000/1931586372284189919933880140762871000054702523215712961:ℝ) (500000000000000000000000000000/217836353618367913414140307773:ℝ) (1/10:ℝ)) :
 GlobalSource (3812172617859633676339875500000000000000000000000000000/3855840885555712748768144282875378197833219710339772271:ℝ) (1000000000000000000000000000000/437621896513685760084008851507:ℝ) (1/10:ℝ) := by
 have h261 := source261 hβ hp
 have h262 := source262 hβ h261
 have h263 := source263 hβ h262
 have h264 := source264 hβ h263
 exact h264
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0261_0264
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0265_0268
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0265_0268

theorem source265 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3812172617859633676339875500000000000000000000000000000/3855840885555712748768144282875378197833219710339772271:ℝ) (1000000000000000000000000000000/437621896513685760084008851507:ℝ) (1/10:ℝ)) :
 GlobalSource (1269942975952729457833526500000000000000000000000000000/1284671600037502365506073093401031548074045207847965603:ℝ) (1000000000000000000000000000000/438113870689127520792064466117:ℝ) (1/10:ℝ) := by
 have heps : 0<p265.toReal.eps := by norm_num [p265,Params.toReal]
 have hcap : p265.toReal.cap=1/10 := by norm_num [p265,Params.toReal]
 have hi : GlobalSource (p265.toReal.state (((cells265 0).2:ℝ)/(p265.den:ℝ))).B (p265.toReal.state (((cells265 0).2:ℝ)/(p265.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p265,cells265,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells265 0).1 < (cells265 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p265) hw0 heps hcap (commonSigns265 0) (highSigns265 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns265 0)
   (u:=((cells265 0).1:ℝ)/(p265.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p265.toReal.state (((cells265 0).1:ℝ)/(p265.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(438113870689127520792064466117/1000000000000000000000000000000:ℝ)) (by norm_num [p265,cells265,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p265,cells265,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source266 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1269942975952729457833526500000000000000000000000000000/1284671600037502365506073093401031548074045207847965603:ℝ) (1000000000000000000000000000000/438113870689127520792064466117:ℝ) (1/10:ℝ)) :
 GlobalSource (761497047571348614132256700000000000000000000000000000/770438294727835356364141724710935431484729914029907457:ℝ) (200000000000000000000000000000/87721546880718945389686130557:ℝ) (1/10:ℝ) := by
 have heps : 0<p266.toReal.eps := by norm_num [p266,Params.toReal]
 have hcap : p266.toReal.cap=1/10 := by norm_num [p266,Params.toReal]
 have hi : GlobalSource (p266.toReal.state (((cells266 0).2:ℝ)/(p266.den:ℝ))).B (p266.toReal.state (((cells266 0).2:ℝ)/(p266.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p266,cells266,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells266 0).1 < (cells266 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p266) hw0 heps hcap (commonSigns266 0) (highSigns266 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns266 0)
   (u:=((cells266 0).1:ℝ)/(p266.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p266.toReal.state (((cells266 0).1:ℝ)/(p266.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(87721546880718945389686130557/200000000000000000000000000000:ℝ)) (by norm_num [p266,cells266,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p266,cells266,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source267 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (761497047571348614132256700000000000000000000000000000/770438294727835356364141724710935431484729914029907457:ℝ) (200000000000000000000000000000/87721546880718945389686130557:ℝ) (1/10:ℝ)) :
 GlobalSource (21743665987744558673268500000000000000000000000000000/22002119484432184779031135452539677844798495752702041:ℝ) (1000000000000000000000000000000/439103497162796242615652422651:ℝ) (1/10:ℝ) := by
 have heps : 0<p267.toReal.eps := by norm_num [p267,Params.toReal]
 have hcap : p267.toReal.cap=1/10 := by norm_num [p267,Params.toReal]
 have hi : GlobalSource (p267.toReal.state (((cells267 0).2:ℝ)/(p267.den:ℝ))).B (p267.toReal.state (((cells267 0).2:ℝ)/(p267.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p267,cells267,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells267 0).1 < (cells267 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p267) hw0 heps hcap (commonSigns267 0) (highSigns267 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns267 0)
   (u:=((cells267 0).1:ℝ)/(p267.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p267.toReal.state (((cells267 0).1:ℝ)/(p267.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(439103497162796242615652422651/1000000000000000000000000000000:ℝ)) (by norm_num [p267,cells267,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p267,cells267,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source268 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (21743665987744558673268500000000000000000000000000000/22002119484432184779031135452539677844798495752702041:ℝ) (1000000000000000000000000000000/439103497162796242615652422651:ℝ) (1/10:ℝ)) :
 GlobalSource (1267599285951284154994230500000000000000000000000000000/1282851037390515916478104494329257027993998602888934207:ℝ) (1000000000000000000000000000000/439601168534630290814359686729:ℝ) (1/10:ℝ) := by
 have heps : 0<p268.toReal.eps := by norm_num [p268,Params.toReal]
 have hcap : p268.toReal.cap=1/10 := by norm_num [p268,Params.toReal]
 have hi : GlobalSource (p268.toReal.state (((cells268 0).2:ℝ)/(p268.den:ℝ))).B (p268.toReal.state (((cells268 0).2:ℝ)/(p268.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p268,cells268,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells268 0).1 < (cells268 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p268) hw0 heps hcap (commonSigns268 0) (highSigns268 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns268 0)
   (u:=((cells268 0).1:ℝ)/(p268.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p268.toReal.state (((cells268 0).1:ℝ)/(p268.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(439601168534630290814359686729/1000000000000000000000000000000:ℝ)) (by norm_num [p268,cells268,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p268,cells268,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3812172617859633676339875500000000000000000000000000000/3855840885555712748768144282875378197833219710339772271:ℝ) (1000000000000000000000000000000/437621896513685760084008851507:ℝ) (1/10:ℝ)) :
 GlobalSource (1267599285951284154994230500000000000000000000000000000/1282851037390515916478104494329257027993998602888934207:ℝ) (1000000000000000000000000000000/439601168534630290814359686729:ℝ) (1/10:ℝ) := by
 have h265 := source265 hβ hp
 have h266 := source266 hβ h265
 have h267 := source267 hβ h266
 have h268 := source268 hβ h267
 exact h268
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0265_0268
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0269_0272
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0269_0272

theorem source269 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1267599285951284154994230500000000000000000000000000000/1282851037390515916478104494329257027993998602888934207:ℝ) (1000000000000000000000000000000/439601168534630290814359686729:ℝ) (1/10:ℝ)) :
 GlobalSource (2955252074535308835259250000000000000000000000000000/2991242678449769953345280087840659605221430539859861:ℝ) (500000000000000000000000000000/220050379074844856826737581251:ℝ) (1/10:ℝ) := by
 have heps : 0<p269.toReal.eps := by norm_num [p269,Params.toReal]
 have hcap : p269.toReal.cap=1/10 := by norm_num [p269,Params.toReal]
 have hi : GlobalSource (p269.toReal.state (((cells269 0).2:ℝ)/(p269.den:ℝ))).B (p269.toReal.state (((cells269 0).2:ℝ)/(p269.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p269,cells269,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells269 0).1 < (cells269 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p269) hw0 heps hcap (commonSigns269 0) (highSigns269 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns269 0)
   (u:=((cells269 0).1:ℝ)/(p269.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p269.toReal.state (((cells269 0).1:ℝ)/(p269.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(220050379074844856826737581251/500000000000000000000000000000:ℝ)) (by norm_num [p269,cells269,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p269,cells269,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source270 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (2955252074535308835259250000000000000000000000000000/2991242678449769953345280087840659605221430539859861:ℝ) (500000000000000000000000000000/220050379074844856826737581251:ℝ) (1/10:ℝ)) :
 GlobalSource (3798110477850961859304099500000000000000000000000000000/3844925830389533881059539018916434573404308715597092147:ℝ) (1000000000000000000000000000000/440602275701772155744918482151:ℝ) (1/10:ℝ) := by
 have heps : 0<p270.toReal.eps := by norm_num [p270,Params.toReal]
 have hcap : p270.toReal.cap=1/10 := by norm_num [p270,Params.toReal]
 have hi : GlobalSource (p270.toReal.state (((cells270 0).2:ℝ)/(p270.den:ℝ))).B (p270.toReal.state (((cells270 0).2:ℝ)/(p270.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p270,cells270,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells270 0).1 < (cells270 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p270) hw0 heps hcap (commonSigns270 0) (highSigns270 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns270 0)
   (u:=((cells270 0).1:ℝ)/(p270.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p270.toReal.state (((cells270 0).1:ℝ)/(p270.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(440602275701772155744918482151/1000000000000000000000000000000:ℝ)) (by norm_num [p270,cells270,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p270,cells270,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source271 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3798110477850961859304099500000000000000000000000000000/3844925830389533881059539018916434573404308715597092147:ℝ) (1000000000000000000000000000000/440602275701772155744918482151:ℝ) (1/10:ℝ)) :
 GlobalSource (253051119189967770430986900000000000000000000000000000/256207756904010984115676429459807148964105165141934039:ℝ) (200000000000000000000000000000/88221146189679045405258356977:ℝ) (1/10:ℝ) := by
 have heps : 0<p271.toReal.eps := by norm_num [p271,Params.toReal]
 have hcap : p271.toReal.cap=1/10 := by norm_num [p271,Params.toReal]
 have hi : GlobalSource (p271.toReal.state (((cells271 0).2:ℝ)/(p271.den:ℝ))).B (p271.toReal.state (((cells271 0).2:ℝ)/(p271.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p271,cells271,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells271 0).1 < (cells271 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p271) hw0 heps hcap (commonSigns271 0) (highSigns271 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns271 0)
   (u:=((cells271 0).1:ℝ)/(p271.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p271.toReal.state (((cells271 0).1:ℝ)/(p271.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(88221146189679045405258356977/200000000000000000000000000000:ℝ)) (by norm_num [p271,cells271,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p271,cells271,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source272 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (253051119189967770430986900000000000000000000000000000/256207756904010984115676429459807148964105165141934039:ℝ) (200000000000000000000000000000/88221146189679045405258356977:ℝ) (1/10:ℝ)) :
 GlobalSource (758684619569614250725101500000000000000000000000000000/768261931537492978182823620359308091913499420529983911:ℝ) (1000000000000000000000000000000/441611133711316701850699287479:ℝ) (1/10:ℝ) := by
 have heps : 0<p272.toReal.eps := by norm_num [p272,Params.toReal]
 have hcap : p272.toReal.cap=1/10 := by norm_num [p272,Params.toReal]
 have hi : GlobalSource (p272.toReal.state (((cells272 0).2:ℝ)/(p272.den:ℝ))).B (p272.toReal.state (((cells272 0).2:ℝ)/(p272.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p272,cells272,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells272 0).1 < (cells272 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p272) hw0 heps hcap (commonSigns272 0) (highSigns272 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns272 0)
   (u:=((cells272 0).1:ℝ)/(p272.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p272.toReal.state (((cells272 0).1:ℝ)/(p272.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(441611133711316701850699287479/1000000000000000000000000000000:ℝ)) (by norm_num [p272,cells272,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p272,cells272,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1267599285951284154994230500000000000000000000000000000/1282851037390515916478104494329257027993998602888934207:ℝ) (1000000000000000000000000000000/439601168534630290814359686729:ℝ) (1/10:ℝ)) :
 GlobalSource (758684619569614250725101500000000000000000000000000000/768261931537492978182823620359308091913499420529983911:ℝ) (1000000000000000000000000000000/441611133711316701850699287479:ℝ) (1/10:ℝ) := by
 have h269 := source269 hβ hp
 have h270 := source270 hβ h269
 have h271 := source271 hβ h270
 have h272 := source272 hβ h271
 exact h272
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0269_0272
