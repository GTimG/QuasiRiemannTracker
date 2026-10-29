/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0209_0212
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0213_0216
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0217_0220
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0221_0224
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0209_0212
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0209_0212

theorem source209 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (164309135747523776472518812500000000000000000000000000/165099870617684553152231418257015945855939933509352879:ℝ) (125000000000000000000000000000/51602441459184796657936738393:ℝ) (1/10:ℝ)) :
 GlobalSource (1970537783969562666250577750000000000000000000000000000/1980210916688804867832520969493726394357651517631050953:ℝ) (500000000000000000000000000000/206609574860424789010804571941:ℝ) (1/10:ℝ) := by
 have heps : 0<p209.toReal.eps := by norm_num [p209,Params.toReal]
 have hcap : p209.toReal.cap=1/10 := by norm_num [p209,Params.toReal]
 have hi : GlobalSource (p209.toReal.state (((cells209 0).2:ℝ)/(p209.den:ℝ))).B (p209.toReal.state (((cells209 0).2:ℝ)/(p209.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p209,cells209,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells209 0).1 < (cells209 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p209) hw0 heps hcap (commonSigns209 0) (highSigns209 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns209 0)
   (u:=((cells209 0).1:ℝ)/(p209.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p209.toReal.state (((cells209 0).1:ℝ)/(p209.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(206609574860424789010804571941/500000000000000000000000000000:ℝ)) (by norm_num [p209,cells209,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p209,cells209,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source210 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1970537783969562666250577750000000000000000000000000000/1980210916688804867832520969493726394357651517631050953:ℝ) (500000000000000000000000000000/206609574860424789010804571941:ℝ) (1/10:ℝ)) :
 GlobalSource (984682969484420007415464875000000000000000000000000000/989612335357911397086292582985911381889897790446777793:ℝ) (250000000000000000000000000000/103405052655435283935411724349:ℝ) (1/10:ℝ) := by
 have heps : 0<p210.toReal.eps := by norm_num [p210,Params.toReal]
 have hcap : p210.toReal.cap=1/10 := by norm_num [p210,Params.toReal]
 have hi : GlobalSource (p210.toReal.state (((cells210 0).2:ℝ)/(p210.den:ℝ))).B (p210.toReal.state (((cells210 0).2:ℝ)/(p210.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p210,cells210,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells210 0).1 < (cells210 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p210) hw0 heps hcap (commonSigns210 0) (highSigns210 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns210 0)
   (u:=((cells210 0).1:ℝ)/(p210.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p210.toReal.state (((cells210 0).1:ℝ)/(p210.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(103405052655435283935411724349/250000000000000000000000000000:ℝ)) (by norm_num [p210,cells210,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p210,cells210,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source211 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (984682969484420007415464875000000000000000000000000000/989612335357911397086292582985911381889897790446777793:ℝ) (250000000000000000000000000000/103405052655435283935411724349:ℝ) (1/10:ℝ)) :
 GlobalSource (328032348994686227235213625000000000000000000000000000/329706618511730123174584706002377335044252486819772937:ℝ) (250000000000000000000000000000/103505680268948848167480938031:ℝ) (1/10:ℝ) := by
 have heps : 0<p211.toReal.eps := by norm_num [p211,Params.toReal]
 have hcap : p211.toReal.cap=1/10 := by norm_num [p211,Params.toReal]
 have hi : GlobalSource (p211.toReal.state (((cells211 0).2:ℝ)/(p211.den:ℝ))).B (p211.toReal.state (((cells211 0).2:ℝ)/(p211.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p211,cells211,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells211 0).1 < (cells211 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p211) hw0 heps hcap (commonSigns211 0) (highSigns211 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns211 0)
   (u:=((cells211 0).1:ℝ)/(p211.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p211.toReal.state (((cells211 0).1:ℝ)/(p211.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(103505680268948848167480938031/250000000000000000000000000000:ℝ)) (by norm_num [p211,cells211,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p211,cells211,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source212 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (328032348994686227235213625000000000000000000000000000/329706618511730123174584706002377335044252486819772937:ℝ) (250000000000000000000000000000/103505680268948848167480938031:ℝ) (1/10:ℝ)) :
 GlobalSource (786808899586957884796653500000000000000000000000000000/790902415733385141563403116595917594887243706191824849:ℝ) (1000000000000000000000000000000/414426687822959010230500207169:ℝ) (1/10:ℝ) := by
 have heps : 0<p212.toReal.eps := by norm_num [p212,Params.toReal]
 have hcap : p212.toReal.cap=1/10 := by norm_num [p212,Params.toReal]
 have hi : GlobalSource (p212.toReal.state (((cells212 0).2:ℝ)/(p212.den:ℝ))).B (p212.toReal.state (((cells212 0).2:ℝ)/(p212.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p212,cells212,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells212 0).1 < (cells212 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p212) hw0 heps hcap (commonSigns212 0) (highSigns212 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns212 0)
   (u:=((cells212 0).1:ℝ)/(p212.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p212.toReal.state (((cells212 0).1:ℝ)/(p212.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(414426687822959010230500207169/1000000000000000000000000000000:ℝ)) (by norm_num [p212,cells212,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p212,cells212,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (164309135747523776472518812500000000000000000000000000/165099870617684553152231418257015945855939933509352879:ℝ) (125000000000000000000000000000/51602441459184796657936738393:ℝ) (1/10:ℝ)) :
 GlobalSource (786808899586957884796653500000000000000000000000000000/790902415733385141563403116595917594887243706191824849:ℝ) (1000000000000000000000000000000/414426687822959010230500207169:ℝ) (1/10:ℝ) := by
 have h209 := source209 hβ hp
 have h210 := source210 hβ h209
 have h211 := source211 hβ h210
 have h212 := source212 hβ h211
 exact h212
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0209_0212
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0213_0216
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0213_0216

theorem source213 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (786808899586957884796653500000000000000000000000000000/790902415733385141563403116595917594887243706191824849:ℝ) (1000000000000000000000000000000/414426687822959010230500207169:ℝ) (1/10:ℝ)) :
 GlobalSource (122865650247917003785749109375000000000000000000000000/123517103568121259887146151287118131978788648397389337:ℝ) (31250000000000000000000000000/12963503676368235638904953653:ℝ) (1/10:ℝ) := by
 have heps : 0<p213.toReal.eps := by norm_num [p213,Params.toReal]
 have hcap : p213.toReal.cap=1/10 := by norm_num [p213,Params.toReal]
 have hi : GlobalSource (p213.toReal.state (((cells213 0).2:ℝ)/(p213.den:ℝ))).B (p213.toReal.state (((cells213 0).2:ℝ)/(p213.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p213,cells213,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells213 0).1 < (cells213 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p213) hw0 heps hcap (commonSigns213 0) (highSigns213 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns213 0)
   (u:=((cells213 0).1:ℝ)/(p213.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p213.toReal.state (((cells213 0).1:ℝ)/(p213.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(12963503676368235638904953653/31250000000000000000000000000:ℝ)) (by norm_num [p213,cells213,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p213,cells213,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source214 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (122865650247917003785749109375000000000000000000000000/123517103568121259887146151287118131978788648397389337:ℝ) (31250000000000000000000000000/12963503676368235638904953653:ℝ) (1/10:ℝ)) :
 GlobalSource (654892852988649803050779250000000000000000000000000000/658430855309528555976833100617609051131533654319702781:ℝ) (500000000000000000000000000000/207619508679864342914857899931:ℝ) (1/10:ℝ) := by
 have heps : 0<p214.toReal.eps := by norm_num [p214,Params.toReal]
 have hcap : p214.toReal.cap=1/10 := by norm_num [p214,Params.toReal]
 have hi : GlobalSource (p214.toReal.state (((cells214 0).2:ℝ)/(p214.den:ℝ))).B (p214.toReal.state (((cells214 0).2:ℝ)/(p214.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p214,cells214,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells214 0).1 < (cells214 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p214) hw0 heps hcap (commonSigns214 0) (highSigns214 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns214 0)
   (u:=((cells214 0).1:ℝ)/(p214.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p214.toReal.state (((cells214 0).1:ℝ)/(p214.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(207619508679864342914857899931/500000000000000000000000000000:ℝ)) (by norm_num [p214,cells214,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p214,cells214,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source215 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (654892852988649803050779250000000000000000000000000000/658430855309528555976833100617609051131533654319702781:ℝ) (500000000000000000000000000000/207619508679864342914857899931:ℝ) (1/10:ℝ)) :
 GlobalSource (1963506713965226757732689750000000000000000000000000000/1974312767442089615042939670443794559739676420003654443:ℝ) (500000000000000000000000000000/207823696916734135882933743359:ℝ) (1/10:ℝ) := by
 have heps : 0<p215.toReal.eps := by norm_num [p215,Params.toReal]
 have hcap : p215.toReal.cap=1/10 := by norm_num [p215,Params.toReal]
 have hi : GlobalSource (p215.toReal.state (((cells215 0).2:ℝ)/(p215.den:ℝ))).B (p215.toReal.state (((cells215 0).2:ℝ)/(p215.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p215,cells215,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells215 0).1 < (cells215 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p215) hw0 heps hcap (commonSigns215 0) (highSigns215 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns215 0)
   (u:=((cells215 0).1:ℝ)/(p215.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p215.toReal.state (((cells215 0).1:ℝ)/(p215.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(207823696916734135882933743359/500000000000000000000000000000:ℝ)) (by norm_num [p215,cells215,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p215,cells215,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source216 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1963506713965226757732689750000000000000000000000000000/1974312767442089615042939670443794559739676420003654443:ℝ) (500000000000000000000000000000/207823696916734135882933743359:ℝ) (1/10:ℝ)) :
 GlobalSource (1962334868964504106313041750000000000000000000000000000/1973334263227074758250786364094952054632498941501239699:ℝ) (500000000000000000000000000000/208028626984599479835585120199:ℝ) (1/10:ℝ) := by
 have heps : 0<p216.toReal.eps := by norm_num [p216,Params.toReal]
 have hcap : p216.toReal.cap=1/10 := by norm_num [p216,Params.toReal]
 have hi : GlobalSource (p216.toReal.state (((cells216 0).2:ℝ)/(p216.den:ℝ))).B (p216.toReal.state (((cells216 0).2:ℝ)/(p216.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p216,cells216,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells216 0).1 < (cells216 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p216) hw0 heps hcap (commonSigns216 0) (highSigns216 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns216 0)
   (u:=((cells216 0).1:ℝ)/(p216.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p216.toReal.state (((cells216 0).1:ℝ)/(p216.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(208028626984599479835585120199/500000000000000000000000000000:ℝ)) (by norm_num [p216,cells216,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p216,cells216,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (786808899586957884796653500000000000000000000000000000/790902415733385141563403116595917594887243706191824849:ℝ) (1000000000000000000000000000000/414426687822959010230500207169:ℝ) (1/10:ℝ)) :
 GlobalSource (1962334868964504106313041750000000000000000000000000000/1973334263227074758250786364094952054632498941501239699:ℝ) (500000000000000000000000000000/208028626984599479835585120199:ℝ) (1/10:ℝ) := by
 have h213 := source213 hβ hp
 have h214 := source214 hβ h213
 have h215 := source215 hβ h214
 have h216 := source216 hβ h215
 exact h216
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0213_0216
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0217_0220
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0217_0220

theorem source217 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1962334868964504106313041750000000000000000000000000000/1973334263227074758250786364094952054632498941501239699:ℝ) (500000000000000000000000000000/208028626984599479835585120199:ℝ) (1/10:ℝ)) :
 GlobalSource (52297680639034172130490500000000000000000000000000000/52596188130242980971073026769644012527213117936729707:ℝ) (1000000000000000000000000000000/416468604712951729642910243189:ℝ) (1/10:ℝ) := by
 have heps : 0<p217.toReal.eps := by norm_num [p217,Params.toReal]
 have hcap : p217.toReal.cap=1/10 := by norm_num [p217,Params.toReal]
 have hi : GlobalSource (p217.toReal.state (((cells217 0).2:ℝ)/(p217.den:ℝ))).B (p217.toReal.state (((cells217 0).2:ℝ)/(p217.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p217,cells217,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells217 0).1 < (cells217 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p217) hw0 heps hcap (commonSigns217 0) (highSigns217 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns217 0)
   (u:=((cells217 0).1:ℝ)/(p217.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p217.toReal.state (((cells217 0).1:ℝ)/(p217.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(416468604712951729642910243189/1000000000000000000000000000000:ℝ)) (by norm_num [p217,cells217,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p217,cells217,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source218 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (52297680639034172130490500000000000000000000000000000/52596188130242980971073026769644012527213117936729707:ℝ) (1000000000000000000000000000000/416468604712951729642910243189:ℝ) (1/10:ℝ)) :
 GlobalSource (1959991178963058803473745750000000000000000000000000000/1971381144017734815234645955770479201703879098190910119:ℝ) (500000000000000000000000000000/208440726526453080792065352331:ℝ) (1/10:ℝ) := by
 have heps : 0<p218.toReal.eps := by norm_num [p218,Params.toReal]
 have hcap : p218.toReal.cap=1/10 := by norm_num [p218,Params.toReal]
 have hi : GlobalSource (p218.toReal.state (((cells218 0).2:ℝ)/(p218.den:ℝ))).B (p218.toReal.state (((cells218 0).2:ℝ)/(p218.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p218,cells218,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells218 0).1 < (cells218 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p218) hw0 heps hcap (commonSigns218 0) (highSigns218 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns218 0)
   (u:=((cells218 0).1:ℝ)/(p218.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p218.toReal.state (((cells218 0).1:ℝ)/(p218.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(208440726526453080792065352331/500000000000000000000000000000:ℝ)) (by norm_num [p218,cells218,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p218,cells218,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source219 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1959991178963058803473745750000000000000000000000000000/1971381144017734815234645955770479201703879098190910119:ℝ) (500000000000000000000000000000/208440726526453080792065352331:ℝ) (1/10:ℝ)) :
 GlobalSource (391763866792467230410819550000000000000000000000000000/394081306447291395637783333893351489174412324172963493:ℝ) (100000000000000000000000000000/41729580601970754417408125841:ℝ) (1/10:ℝ) := by
 have heps : 0<p219.toReal.eps := by norm_num [p219,Params.toReal]
 have hcap : p219.toReal.cap=1/10 := by norm_num [p219,Params.toReal]
 have hi : GlobalSource (p219.toReal.state (((cells219 0).2:ℝ)/(p219.den:ℝ))).B (p219.toReal.state (((cells219 0).2:ℝ)/(p219.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p219,cells219,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells219 0).1 < (cells219 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p219) hw0 heps hcap (commonSigns219 0) (highSigns219 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns219 0)
   (u:=((cells219 0).1:ℝ)/(p219.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p219.toReal.state (((cells219 0).1:ℝ)/(p219.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(41729580601970754417408125841/100000000000000000000000000000:ℝ)) (by norm_num [p219,cells219,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p219,cells219,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source220 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (391763866792467230410819550000000000000000000000000000/394081306447291395637783333893351489174412324172963493:ℝ) (100000000000000000000000000000/41729580601970754417408125841:ℝ) (1/10:ℝ)) :
 GlobalSource (50196089460554192323960250000000000000000000000000000/50498287721866310580763835066241676568143458174073911:ℝ) (500000000000000000000000000000/208855835343393420698436209757:ℝ) (1/10:ℝ) := by
 have heps : 0<p220.toReal.eps := by norm_num [p220,Params.toReal]
 have hcap : p220.toReal.cap=1/10 := by norm_num [p220,Params.toReal]
 have hi : GlobalSource (p220.toReal.state (((cells220 0).2:ℝ)/(p220.den:ℝ))).B (p220.toReal.state (((cells220 0).2:ℝ)/(p220.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p220,cells220,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells220 0).1 < (cells220 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p220) hw0 heps hcap (commonSigns220 0) (highSigns220 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns220 0)
   (u:=((cells220 0).1:ℝ)/(p220.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p220.toReal.state (((cells220 0).1:ℝ)/(p220.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(208855835343393420698436209757/500000000000000000000000000000:ℝ)) (by norm_num [p220,cells220,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p220,cells220,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1962334868964504106313041750000000000000000000000000000/1973334263227074758250786364094952054632498941501239699:ℝ) (500000000000000000000000000000/208028626984599479835585120199:ℝ) (1/10:ℝ)) :
 GlobalSource (50196089460554192323960250000000000000000000000000000/50498287721866310580763835066241676568143458174073911:ℝ) (500000000000000000000000000000/208855835343393420698436209757:ℝ) (1/10:ℝ) := by
 have h217 := source217 hβ hp
 have h218 := source218 hβ h217
 have h219 := source219 hβ h218
 have h220 := source220 hβ h219
 exact h220
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0217_0220
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0221_0224
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0221_0224

theorem source221 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (50196089460554192323960250000000000000000000000000000/50498287721866310580763835066241676568143458174073911:ℝ) (500000000000000000000000000000/208855835343393420698436209757:ℝ) (1/10:ℝ)) :
 GlobalSource (3912951287921781698429603500000000000000000000000000000/3936922424766481084174341617158541299899344161810095159:ℝ) (1000000000000000000000000000000/418129054170683546700242505179:ℝ) (1/10:ℝ) := by
 have heps : 0<p221.toReal.eps := by norm_num [p221,Params.toReal]
 have hcap : p221.toReal.cap=1/10 := by norm_num [p221,Params.toReal]
 have hi : GlobalSource (p221.toReal.state (((cells221 0).2:ℝ)/(p221.den:ℝ))).B (p221.toReal.state (((cells221 0).2:ℝ)/(p221.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p221,cells221,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells221 0).1 < (cells221 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p221) hw0 heps hcap (commonSigns221 0) (highSigns221 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns221 0)
   (u:=((cells221 0).1:ℝ)/(p221.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p221.toReal.state (((cells221 0).1:ℝ)/(p221.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(418129054170683546700242505179/1000000000000000000000000000000:ℝ)) (by norm_num [p221,cells221,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p221,cells221,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source222 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3912951287921781698429603500000000000000000000000000000/3936922424766481084174341617158541299899344161810095159:ℝ) (1000000000000000000000000000000/418129054170683546700242505179:ℝ) (1/10:ℝ)) :
 GlobalSource (782121519584067279118061500000000000000000000000000000/786996203019345982126267436804018558174133724374151923:ℝ) (1000000000000000000000000000000/418547963631371455219145638467:ℝ) (1/10:ℝ) := by
 have heps : 0<p222.toReal.eps := by norm_num [p222,Params.toReal]
 have hcap : p222.toReal.cap=1/10 := by norm_num [p222,Params.toReal]
 have hi : GlobalSource (p222.toReal.state (((cells222 0).2:ℝ)/(p222.den:ℝ))).B (p222.toReal.state (((cells222 0).2:ℝ)/(p222.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p222,cells222,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells222 0).1 < (cells222 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p222) hw0 heps hcap (commonSigns222 0) (highSigns222 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns222 0)
   (u:=((cells222 0).1:ℝ)/(p222.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p222.toReal.state (((cells222 0).1:ℝ)/(p222.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(418547963631371455219145638467/1000000000000000000000000000000:ℝ)) (by norm_num [p222,cells222,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p222,cells222,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source223 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (782121519584067279118061500000000000000000000000000000/786996203019345982126267436804018558174133724374151923:ℝ) (1000000000000000000000000000000/418547963631371455219145638467:ℝ) (1/10:ℝ)) :
 GlobalSource (651377317986481848791835250000000000000000000000000000/655507036090915461246560677319641213525311421840311167:ℝ) (500000000000000000000000000000/209484203136293692433311083529:ℝ) (1/10:ℝ) := by
 have heps : 0<p223.toReal.eps := by norm_num [p223,Params.toReal]
 have hcap : p223.toReal.cap=1/10 := by norm_num [p223,Params.toReal]
 have hi : GlobalSource (p223.toReal.state (((cells223 0).2:ℝ)/(p223.den:ℝ))).B (p223.toReal.state (((cells223 0).2:ℝ)/(p223.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p223,cells223,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells223 0).1 < (cells223 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p223) hw0 heps hcap (commonSigns223 0) (highSigns223 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns223 0)
   (u:=((cells223 0).1:ℝ)/(p223.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p223.toReal.state (((cells223 0).1:ℝ)/(p223.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(209484203136293692433311083529/500000000000000000000000000000:ℝ)) (by norm_num [p223,cells223,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p223,cells223,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source224 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (651377317986481848791835250000000000000000000000000000/655507036090915461246560677319641213525311421840311167:ℝ) (500000000000000000000000000000/209484203136293692433311083529:ℝ) (1/10:ℝ)) :
 GlobalSource (156236808716697831596468620000000000000000000000000000/157244241294802422205592799857359432012629033770560029:ℝ) (40000000000000000000000000000/16775615573686515098687712553:ℝ) (1/10:ℝ) := by
 have heps : 0<p224.toReal.eps := by norm_num [p224,Params.toReal]
 have hcap : p224.toReal.cap=1/10 := by norm_num [p224,Params.toReal]
 have hi : GlobalSource (p224.toReal.state (((cells224 0).2:ℝ)/(p224.den:ℝ))).B (p224.toReal.state (((cells224 0).2:ℝ)/(p224.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p224,cells224,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells224 0).1 < (cells224 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p224) hw0 heps hcap (commonSigns224 0) (highSigns224 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns224 0)
   (u:=((cells224 0).1:ℝ)/(p224.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p224.toReal.state (((cells224 0).1:ℝ)/(p224.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(16775615573686515098687712553/40000000000000000000000000000:ℝ)) (by norm_num [p224,cells224,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p224,cells224,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (50196089460554192323960250000000000000000000000000000/50498287721866310580763835066241676568143458174073911:ℝ) (500000000000000000000000000000/208855835343393420698436209757:ℝ) (1/10:ℝ)) :
 GlobalSource (156236808716697831596468620000000000000000000000000000/157244241294802422205592799857359432012629033770560029:ℝ) (40000000000000000000000000000/16775615573686515098687712553:ℝ) (1/10:ℝ) := by
 have h221 := source221 hβ hp
 have h222 := source222 hβ h221
 have h223 := source223 hβ h222
 have h224 := source224 hβ h223
 exact h224
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0221_0224
