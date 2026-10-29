/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0241_0244
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0245_0248
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0249_0252
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0253_0256
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0241_0244
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0241_0244

theorem source241 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1934210588947160472241489750000000000000000000000000000/1950242665296216219921736746945402570886102730593845249:ℝ) (500000000000000000000000000000/213178853581934545393154605437:ℝ) (1/10:ℝ)) :
 GlobalSource (1288692495964291880547894500000000000000000000000000000/1299531365732122229398198417890985071933444149749005199:ℝ) (1000000000000000000000000000000/426807030831724726780925483897:ℝ) (1/10:ℝ) := by
 have heps : 0<p241.toReal.eps := by norm_num [p241,Params.toReal]
 have hcap : p241.toReal.cap=1/10 := by norm_num [p241,Params.toReal]
 have hi : GlobalSource (p241.toReal.state (((cells241 0).2:ℝ)/(p241.den:ℝ))).B (p241.toReal.state (((cells241 0).2:ℝ)/(p241.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p241,cells241,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells241 0).1 < (cells241 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p241) hw0 heps hcap (commonSigns241 0) (highSigns241 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns241 0)
   (u:=((cells241 0).1:ℝ)/(p241.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p241.toReal.state (((cells241 0).1:ℝ)/(p241.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(426807030831724726780925483897/1000000000000000000000000000000:ℝ)) (by norm_num [p241,cells241,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p241,cells241,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source242 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1288692495964291880547894500000000000000000000000000000/1299531365732122229398198417890985071933444149749005199:ℝ) (1000000000000000000000000000000/426807030831724726780925483897:ℝ) (1/10:ℝ)) :
 GlobalSource (15454935191565721355217550000000000000000000000000000/15586822152932856615681578584471658081451993128646369:ℝ) (100000000000000000000000000000/42725803332594073993432875413:ℝ) (1/10:ℝ) := by
 have heps : 0<p242.toReal.eps := by norm_num [p242,Params.toReal]
 have hcap : p242.toReal.cap=1/10 := by norm_num [p242,Params.toReal]
 have hi : GlobalSource (p242.toReal.state (((cells242 0).2:ℝ)/(p242.den:ℝ))).B (p242.toReal.state (((cells242 0).2:ℝ)/(p242.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p242,cells242,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells242 0).1 < (cells242 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p242) hw0 heps hcap (commonSigns242 0) (highSigns242 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns242 0)
   (u:=((cells242 0).1:ℝ)/(p242.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p242.toReal.state (((cells242 0).1:ℝ)/(p242.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(42725803332594073993432875413/100000000000000000000000000000:ℝ)) (by norm_num [p242,cells242,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p242,cells242,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source243 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (15454935191565721355217550000000000000000000000000000/15586822152932856615681578584471658081451993128646369:ℝ) (100000000000000000000000000000/42725803332594073993432875413:ℝ) (1/10:ℝ)) :
 GlobalSource (772278021577997007193018300000000000000000000000000000/778963931424174634670319844671068377303039824252246501:ℝ) (200000000000000000000000000000/85542144559875280807100586449:ℝ) (1/10:ℝ) := by
 have heps : 0<p243.toReal.eps := by norm_num [p243,Params.toReal]
 have hcap : p243.toReal.cap=1/10 := by norm_num [p243,Params.toReal]
 have hi : GlobalSource (p243.toReal.state (((cells243 0).2:ℝ)/(p243.den:ℝ))).B (p243.toReal.state (((cells243 0).2:ℝ)/(p243.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p243,cells243,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells243 0).1 < (cells243 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p243) hw0 heps hcap (commonSigns243 0) (highSigns243 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns243 0)
   (u:=((cells243 0).1:ℝ)/(p243.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p243.toReal.state (((cells243 0).1:ℝ)/(p243.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(85542144559875280807100586449/200000000000000000000000000000:ℝ)) (by norm_num [p243,cells243,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p243,cells243,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source244 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (772278021577997007193018300000000000000000000000000000/778963931424174634670319844671068377303039824252246501:ℝ) (200000000000000000000000000000/85542144559875280807100586449:ℝ) (1/10:ℝ)) :
 GlobalSource (160793600745355822213574812500000000000000000000000000/162205685720251950746390474117191640351010784040692951:ℝ) (125000000000000000000000000000/53520638432037135901625086961:ℝ) (1/10:ℝ) := by
 have heps : 0<p244.toReal.eps := by norm_num [p244,Params.toReal]
 have hcap : p244.toReal.cap=1/10 := by norm_num [p244,Params.toReal]
 have hi : GlobalSource (p244.toReal.state (((cells244 0).2:ℝ)/(p244.den:ℝ))).B (p244.toReal.state (((cells244 0).2:ℝ)/(p244.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p244,cells244,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells244 0).1 < (cells244 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p244) hw0 heps hcap (commonSigns244 0) (highSigns244 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns244 0)
   (u:=((cells244 0).1:ℝ)/(p244.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p244.toReal.state (((cells244 0).1:ℝ)/(p244.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(53520638432037135901625086961/125000000000000000000000000000:ℝ)) (by norm_num [p244,cells244,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p244,cells244,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1934210588947160472241489750000000000000000000000000000/1950242665296216219921736746945402570886102730593845249:ℝ) (500000000000000000000000000000/213178853581934545393154605437:ℝ) (1/10:ℝ)) :
 GlobalSource (160793600745355822213574812500000000000000000000000000/162205685720251950746390474117191640351010784040692951:ℝ) (125000000000000000000000000000/53520638432037135901625086961:ℝ) (1/10:ℝ) := by
 have h241 := source241 hβ hp
 have h242 := source242 hβ h241
 have h243 := source243 hβ h242
 have h244 := source244 hβ h243
 exact h244
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0241_0244
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0245_0248
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0245_0248

theorem source245 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (160793600745355822213574812500000000000000000000000000/162205685720251950746390474117191640351010784040692951:ℝ) (125000000000000000000000000000/53520638432037135901625086961:ℝ) (1/10:ℝ)) :
 GlobalSource (192835136394354721514324975000000000000000000000000000/194552797108213985561336101450838728617662131693560627:ℝ) (50000000000000000000000000000/21431059777638822669832450791:ℝ) (1/10:ℝ) := by
 have heps : 0<p245.toReal.eps := by norm_num [p245,Params.toReal]
 have hcap : p245.toReal.cap=1/10 := by norm_num [p245,Params.toReal]
 have hi : GlobalSource (p245.toReal.state (((cells245 0).2:ℝ)/(p245.den:ℝ))).B (p245.toReal.state (((cells245 0).2:ℝ)/(p245.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p245,cells245,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells245 0).1 < (cells245 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p245) hw0 heps hcap (commonSigns245 0) (highSigns245 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns245 0)
   (u:=((cells245 0).1:ℝ)/(p245.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p245.toReal.state (((cells245 0).1:ℝ)/(p245.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(21431059777638822669832450791/50000000000000000000000000000:ℝ)) (by norm_num [p245,cells245,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p245,cells245,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source246 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (192835136394354721514324975000000000000000000000000000/194552797108213985561336101450838728617662131693560627:ℝ) (50000000000000000000000000000/21431059777638822669832450791:ℝ) (1/10:ℝ)) :
 GlobalSource (1927179518942824563723601750000000000000000000000000000/1944589057599997547840935331392421335411977654553557849:ℝ) (500000000000000000000000000000/214539497698551217607738487669:ℝ) (1/10:ℝ) := by
 have heps : 0<p246.toReal.eps := by norm_num [p246,Params.toReal]
 have hcap : p246.toReal.cap=1/10 := by norm_num [p246,Params.toReal]
 have hi : GlobalSource (p246.toReal.state (((cells246 0).2:ℝ)/(p246.den:ℝ))).B (p246.toReal.state (((cells246 0).2:ℝ)/(p246.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p246,cells246,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells246 0).1 < (cells246 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p246) hw0 heps hcap (commonSigns246 0) (highSigns246 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns246 0)
   (u:=((cells246 0).1:ℝ)/(p246.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p246.toReal.state (((cells246 0).1:ℝ)/(p246.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(214539497698551217607738487669/500000000000000000000000000000:ℝ)) (by norm_num [p246,cells246,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p246,cells246,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source247 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1927179518942824563723601750000000000000000000000000000/1944589057599997547840935331392421335411977654553557849:ℝ) (500000000000000000000000000000/214539497698551217607738487669:ℝ) (1/10:ℝ)) :
 GlobalSource (256801023192280254973860500000000000000000000000000000/259153531989768810086399869460743989367309276510093283:ℝ) (1000000000000000000000000000000/429538515350187019663984806041:ℝ) (1/10:ℝ) := by
 have heps : 0<p247.toReal.eps := by norm_num [p247,Params.toReal]
 have hcap : p247.toReal.cap=1/10 := by norm_num [p247,Params.toReal]
 have hi : GlobalSource (p247.toReal.state (((cells247 0).2:ℝ)/(p247.den:ℝ))).B (p247.toReal.state (((cells247 0).2:ℝ)/(p247.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p247,cells247,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells247 0).1 < (cells247 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p247) hw0 heps hcap (commonSigns247 0) (highSigns247 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns247 0)
   (u:=((cells247 0).1:ℝ)/(p247.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p247.toReal.state (((cells247 0).1:ℝ)/(p247.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(429538515350187019663984806041/1000000000000000000000000000000:ℝ)) (by norm_num [p247,cells247,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p247,cells247,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source248 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (256801023192280254973860500000000000000000000000000000/259153531989768810086399869460743989367309276510093283:ℝ) (1000000000000000000000000000000/429538515350187019663984806041:ℝ) (1/10:ℝ)) :
 GlobalSource (96241791447068963044215287500000000000000000000000000/97135763489154589242906118154989277178846503119294167:ℝ) (25000000000000000000000000000/10749994095649497209720411643:ℝ) (1/10:ℝ) := by
 have heps : 0<p248.toReal.eps := by norm_num [p248,Params.toReal]
 have hcap : p248.toReal.cap=1/10 := by norm_num [p248,Params.toReal]
 have hi : GlobalSource (p248.toReal.state (((cells248 0).2:ℝ)/(p248.den:ℝ))).B (p248.toReal.state (((cells248 0).2:ℝ)/(p248.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p248,cells248,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells248 0).1 < (cells248 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p248) hw0 heps hcap (commonSigns248 0) (highSigns248 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns248 0)
   (u:=((cells248 0).1:ℝ)/(p248.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p248.toReal.state (((cells248 0).1:ℝ)/(p248.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(10749994095649497209720411643/25000000000000000000000000000:ℝ)) (by norm_num [p248,cells248,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p248,cells248,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (160793600745355822213574812500000000000000000000000000/162205685720251950746390474117191640351010784040692951:ℝ) (125000000000000000000000000000/53520638432037135901625086961:ℝ) (1/10:ℝ)) :
 GlobalSource (96241791447068963044215287500000000000000000000000000/97135763489154589242906118154989277178846503119294167:ℝ) (25000000000000000000000000000/10749994095649497209720411643:ℝ) (1/10:ℝ) := by
 have h245 := source245 hβ hp
 have h246 := source246 hβ h245
 have h247 := source247 hβ h246
 have h248 := source248 hβ h247
 exact h248
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0245_0248
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0249_0252
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0249_0252

theorem source249 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (96241791447068963044215287500000000000000000000000000/97135763489154589242906118154989277178846503119294167:ℝ) (25000000000000000000000000000/10749994095649497209720411643:ℝ) (1/10:ℝ)) :
 GlobalSource (30778623743050505751434524000000000000000000000000000/31068486382641867090226532429336769212375917427922417:ℝ) (8000000000000000000000000000/3443701994335087639802058669:ℝ) (1/10:ℝ) := by
 have heps : 0<p249.toReal.eps := by norm_num [p249,Params.toReal]
 have hcap : p249.toReal.cap=1/10 := by norm_num [p249,Params.toReal]
 have hi : GlobalSource (p249.toReal.state (((cells249 0).2:ℝ)/(p249.den:ℝ))).B (p249.toReal.state (((cells249 0).2:ℝ)/(p249.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p249,cells249,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells249 0).1 < (cells249 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p249) hw0 heps hcap (commonSigns249 0) (highSigns249 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns249 0)
   (u:=((cells249 0).1:ℝ)/(p249.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p249.toReal.state (((cells249 0).1:ℝ)/(p249.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(3443701994335087639802058669/8000000000000000000000000000:ℝ)) (by norm_num [p249,cells249,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p249,cells249,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source250 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (30778623743050505751434524000000000000000000000000000/31068486382641867090226532429336769212375917427922417:ℝ) (8000000000000000000000000000/3443701994335087639802058669:ℝ) (1/10:ℝ)) :
 GlobalSource (1281661425959955972030006500000000000000000000000000000/1293897919372998357693899073234951630086663533170032907:ℝ) (1000000000000000000000000000000/430927480269186842147872835613:ℝ) (1/10:ℝ) := by
 have heps : 0<p250.toReal.eps := by norm_num [p250,Params.toReal]
 have hcap : p250.toReal.cap=1/10 := by norm_num [p250,Params.toReal]
 have hi : GlobalSource (p250.toReal.state (((cells250 0).2:ℝ)/(p250.den:ℝ))).B (p250.toReal.state (((cells250 0).2:ℝ)/(p250.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p250,cells250,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells250 0).1 < (cells250 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p250) hw0 heps hcap (commonSigns250 0) (highSigns250 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns250 0)
   (u:=((cells250 0).1:ℝ)/(p250.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p250.toReal.state (((cells250 0).1:ℝ)/(p250.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(430927480269186842147872835613/1000000000000000000000000000000:ℝ)) (by norm_num [p250,cells250,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p250,cells250,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source251 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1281661425959955972030006500000000000000000000000000000/1293897919372998357693899073234951630086663533170032907:ℝ) (1000000000000000000000000000000/430927480269186842147872835613:ℝ) (1/10:ℝ)) :
 GlobalSource (3842640587878422613250723500000000000000000000000000000/3879829423921849896094269084242581058862751293608706723:ℝ) (1000000000000000000000000000000/431393965333466342342154263703:ℝ) (1/10:ℝ) := by
 have heps : 0<p251.toReal.eps := by norm_num [p251,Params.toReal]
 have hcap : p251.toReal.cap=1/10 := by norm_num [p251,Params.toReal]
 have hi : GlobalSource (p251.toReal.state (((cells251 0).2:ℝ)/(p251.den:ℝ))).B (p251.toReal.state (((cells251 0).2:ℝ)/(p251.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p251,cells251,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells251 0).1 < (cells251 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p251) hw0 heps hcap (commonSigns251 0) (highSigns251 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns251 0)
   (u:=((cells251 0).1:ℝ)/(p251.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p251.toReal.state (((cells251 0).1:ℝ)/(p251.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(431393965333466342342154263703/1000000000000000000000000000000:ℝ)) (by norm_num [p251,cells251,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p251,cells251,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source252 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3842640587878422613250723500000000000000000000000000000/3879829423921849896094269084242581058862751293608706723:ℝ) (1000000000000000000000000000000/431393965333466342342154263703:ℝ) (1/10:ℝ)) :
 GlobalSource (192014844893848865520571375000000000000000000000000000/193898389936864276967606908721879292591283462248296829:ℝ) (250000000000000000000000000000/107965553278759976413592044333:ℝ) (1/10:ℝ) := by
 have heps : 0<p252.toReal.eps := by norm_num [p252,Params.toReal]
 have hcap : p252.toReal.cap=1/10 := by norm_num [p252,Params.toReal]
 have hi : GlobalSource (p252.toReal.state (((cells252 0).2:ℝ)/(p252.den:ℝ))).B (p252.toReal.state (((cells252 0).2:ℝ)/(p252.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p252,cells252,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells252 0).1 < (cells252 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p252) hw0 heps hcap (commonSigns252 0) (highSigns252 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns252 0)
   (u:=((cells252 0).1:ℝ)/(p252.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p252.toReal.state (((cells252 0).1:ℝ)/(p252.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(107965553278759976413592044333/250000000000000000000000000000:ℝ)) (by norm_num [p252,cells252,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p252,cells252,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (96241791447068963044215287500000000000000000000000000/97135763489154589242906118154989277178846503119294167:ℝ) (25000000000000000000000000000/10749994095649497209720411643:ℝ) (1/10:ℝ)) :
 GlobalSource (192014844893848865520571375000000000000000000000000000/193898389936864276967606908721879292591283462248296829:ℝ) (250000000000000000000000000000/107965553278759976413592044333:ℝ) (1/10:ℝ) := by
 have h249 := source249 hβ hp
 have h250 := source250 hβ h249
 have h251 := source251 hβ h250
 have h252 := source252 hβ h251
 exact h252
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0249_0252
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0253_0256
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0253_0256

theorem source253 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (192014844893848865520571375000000000000000000000000000/193898389936864276967606908721879292591283462248296829:ℝ) (250000000000000000000000000000/107965553278759976413592044333:ℝ) (1/10:ℝ)) :
 GlobalSource (639658867979255334595355250000000000000000000000000000/646018147678822499895780153346425624712096589647980173:ℝ) (500000000000000000000000000000/216166116149694099867520626571:ℝ) (1/10:ℝ) := by
 have heps : 0<p253.toReal.eps := by norm_num [p253,Params.toReal]
 have hcap : p253.toReal.cap=1/10 := by norm_num [p253,Params.toReal]
 have hi : GlobalSource (p253.toReal.state (((cells253 0).2:ℝ)/(p253.den:ℝ))).B (p253.toReal.state (((cells253 0).2:ℝ)/(p253.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p253,cells253,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells253 0).1 < (cells253 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p253) hw0 heps hcap (commonSigns253 0) (highSigns253 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns253 0)
   (u:=((cells253 0).1:ℝ)/(p253.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p253.toReal.state (((cells253 0).1:ℝ)/(p253.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(216166116149694099867520626571/500000000000000000000000000000:ℝ)) (by norm_num [p253,cells253,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p253,cells253,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source254 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (639658867979255334595355250000000000000000000000000000/646018147678822499895780153346425624712096589647980173:ℝ) (500000000000000000000000000000/216166116149694099867520626571:ℝ) (1/10:ℝ)) :
 GlobalSource (7491424839597825595181319335937500000000000000000000/7566899784073468267520141346705935249111723744056851:ℝ) (1953125000000000000000000000/845320374272646067886291527:ℝ) (1/10:ℝ) := by
 have heps : 0<p254.toReal.eps := by norm_num [p254,Params.toReal]
 have hcap : p254.toReal.cap=1/10 := by norm_num [p254,Params.toReal]
 have hi : GlobalSource (p254.toReal.state (((cells254 0).2:ℝ)/(p254.den:ℝ))).B (p254.toReal.state (((cells254 0).2:ℝ)/(p254.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p254,cells254,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells254 0).1 < (cells254 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p254) hw0 heps hcap (commonSigns254 0) (highSigns254 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns254 0)
   (u:=((cells254 0).1:ℝ)/(p254.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p254.toReal.state (((cells254 0).1:ℝ)/(p254.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(845320374272646067886291527/1953125000000000000000000000:ℝ)) (by norm_num [p254,cells254,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p254,cells254,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source255 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (7491424839597825595181319335937500000000000000000000/7566899784073468267520141346705935249111723744056851:ℝ) (1953125000000000000000000000/845320374272646067886291527:ℝ) (1/10:ℝ)) :
 GlobalSource (3833265827872641401893539500000000000000000000000000000/3872399212381369201665253463333322138375835405422485607:ℝ) (1000000000000000000000000000000/433277619896787963169567304011:ℝ) (1/10:ℝ) := by
 have heps : 0<p255.toReal.eps := by norm_num [p255,Params.toReal]
 have hcap : p255.toReal.cap=1/10 := by norm_num [p255,Params.toReal]
 have hi : GlobalSource (p255.toReal.state (((cells255 0).2:ℝ)/(p255.den:ℝ))).B (p255.toReal.state (((cells255 0).2:ℝ)/(p255.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p255,cells255,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells255 0).1 < (cells255 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p255) hw0 heps hcap (commonSigns255 0) (highSigns255 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns255 0)
   (u:=((cells255 0).1:ℝ)/(p255.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p255.toReal.state (((cells255 0).1:ℝ)/(p255.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(433277619896787963169567304011/1000000000000000000000000000000:ℝ)) (by norm_num [p255,cells255,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p255,cells255,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source256 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3833265827872641401893539500000000000000000000000000000/3872399212381369201665253463333322138375835405422485607:ℝ) (1000000000000000000000000000000/433277619896787963169567304011:ℝ) (1/10:ℝ)) :
 GlobalSource (255394809191413073270282900000000000000000000000000000/258036563894366693069712298268334175409984560481974163:ℝ) (200000000000000000000000000000/86750601192117361702274244949:ℝ) (1/10:ℝ) := by
 have heps : 0<p256.toReal.eps := by norm_num [p256,Params.toReal]
 have hcap : p256.toReal.cap=1/10 := by norm_num [p256,Params.toReal]
 have hi : GlobalSource (p256.toReal.state (((cells256 0).2:ℝ)/(p256.den:ℝ))).B (p256.toReal.state (((cells256 0).2:ℝ)/(p256.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p256,cells256,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells256 0).1 < (cells256 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p256) hw0 heps hcap (commonSigns256 0) (highSigns256 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns256 0)
   (u:=((cells256 0).1:ℝ)/(p256.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p256.toReal.state (((cells256 0).1:ℝ)/(p256.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(86750601192117361702274244949/200000000000000000000000000000:ℝ)) (by norm_num [p256,cells256,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p256,cells256,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (192014844893848865520571375000000000000000000000000000/193898389936864276967606908721879292591283462248296829:ℝ) (250000000000000000000000000000/107965553278759976413592044333:ℝ) (1/10:ℝ)) :
 GlobalSource (255394809191413073270282900000000000000000000000000000/258036563894366693069712298268334175409984560481974163:ℝ) (200000000000000000000000000000/86750601192117361702274244949:ℝ) (1/10:ℝ) := by
 have h253 := source253 hβ hp
 have h254 := source254 hβ h253
 have h255 := source255 hβ h254
 have h256 := source256 hβ h255
 exact h256
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0253_0256
