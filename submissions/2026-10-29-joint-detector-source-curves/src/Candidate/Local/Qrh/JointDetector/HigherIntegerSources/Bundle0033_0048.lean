/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0033_0036
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0037_0040
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0041_0044
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0045_0048
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0033_0036
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0033_0036

theorem source33 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1555347625728009598268750000000000000000000000000/1556047599237374410304202537662077569863341297107:ℝ) (25000000000000000000000000000/9804208998938539040202642181:ℝ) (1/10:ℝ)) :
 GlobalSource (1327039243973981821476500000000000000000000000000000/1327655949564905010711150171883632186041549938502373:ℝ) (1000000000000000000000000000000/392250332705089691428674958047:ℝ) (1/10:ℝ) := by
 have heps : 0<p33.toReal.eps := by norm_num [p33,Params.toReal]
 have hcap : p33.toReal.cap=1/10 := by norm_num [p33,Params.toReal]
 have hi : GlobalSource (p33.toReal.state (((cells33 0).2:ℝ)/(p33.den:ℝ))).B (p33.toReal.state (((cells33 0).2:ℝ)/(p33.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p33,cells33,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells33 0).1 < (cells33 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p33) hw0 heps hcap (commonSigns33 0) (highSigns33 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns33 0)
   (u:=((cells33 0).1:ℝ)/(p33.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p33.toReal.state (((cells33 0).1:ℝ)/(p33.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(392250332705089691428674958047/1000000000000000000000000000000:ℝ)) (by norm_num [p33,cells33,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p33,cells33,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source34 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1327039243973981821476500000000000000000000000000000/1327655949564905010711150171883632186041549938502373:ℝ) (1000000000000000000000000000000/392250332705089691428674958047:ℝ) (1/10:ℝ)) :
 GlobalSource (1990272770990093178645500000000000000000000000000000/1991226987709067428203229368088004868877766696062749:ℝ) (1000000000000000000000000000000/392332373913252370235832332813:ℝ) (1/10:ℝ) := by
 have heps : 0<p34.toReal.eps := by norm_num [p34,Params.toReal]
 have hcap : p34.toReal.cap=1/10 := by norm_num [p34,Params.toReal]
 have hi : GlobalSource (p34.toReal.state (((cells34 0).2:ℝ)/(p34.den:ℝ))).B (p34.toReal.state (((cells34 0).2:ℝ)/(p34.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p34,cells34,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells34 0).1 < (cells34 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p34) hw0 heps hcap (commonSigns34 0) (highSigns34 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns34 0)
   (u:=((cells34 0).1:ℝ)/(p34.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p34.toReal.state (((cells34 0).1:ℝ)/(p34.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(392332373913252370235832332813/1000000000000000000000000000000:ℝ)) (by norm_num [p34,cells34,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p34,cells34,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source35 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1990272770990093178645500000000000000000000000000000/1991226987709067428203229368088004868877766696062749:ℝ) (1000000000000000000000000000000/392332373913252370235832332813:ℝ) (1/10:ℝ)) :
 GlobalSource (795994670407685450030500000000000000000000000000000/796388046835963038348740821250332928954469248108529:ℝ) (1000000000000000000000000000000/392414483647759693209870531863:ℝ) (1/10:ℝ) := by
 have heps : 0<p35.toReal.eps := by norm_num [p35,Params.toReal]
 have hcap : p35.toReal.cap=1/10 := by norm_num [p35,Params.toReal]
 have hi : GlobalSource (p35.toReal.state (((cells35 0).2:ℝ)/(p35.den:ℝ))).B (p35.toReal.state (((cells35 0).2:ℝ)/(p35.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p35,cells35,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells35 0).1 < (cells35 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p35) hw0 heps hcap (commonSigns35 0) (highSigns35 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns35 0)
   (u:=((cells35 0).1:ℝ)/(p35.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p35.toReal.state (((cells35 0).1:ℝ)/(p35.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(392414483647759693209870531863/1000000000000000000000000000000:ℝ)) (by norm_num [p35,cells35,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p35,cells35,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source36 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (795994670407685450030500000000000000000000000000000/796388046835963038348740821250332928954469248108529:ℝ) (1000000000000000000000000000000/392414483647759693209870531863:ℝ) (1/10:ℝ)) :
 GlobalSource (3454341286542246651921875000000000000000000000000/3456099500817557230778994521731305153516820330259:ℝ) (31250000000000000000000000000/12265520686701554151561721611:ℝ) (1/10:ℝ) := by
 have heps : 0<p36.toReal.eps := by norm_num [p36,Params.toReal]
 have hcap : p36.toReal.cap=1/10 := by norm_num [p36,Params.toReal]
 have hi : GlobalSource (p36.toReal.state (((cells36 0).2:ℝ)/(p36.den:ℝ))).B (p36.toReal.state (((cells36 0).2:ℝ)/(p36.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p36,cells36,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells36 0).1 < (cells36 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p36) hw0 heps hcap (commonSigns36 0) (highSigns36 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns36 0)
   (u:=((cells36 0).1:ℝ)/(p36.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p36.toReal.state (((cells36 0).1:ℝ)/(p36.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(12265520686701554151561721611/31250000000000000000000000000:ℝ)) (by norm_num [p36,cells36,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p36,cells36,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1555347625728009598268750000000000000000000000000/1556047599237374410304202537662077569863341297107:ℝ) (25000000000000000000000000000/9804208998938539040202642181:ℝ) (1/10:ℝ)) :
 GlobalSource (3454341286542246651921875000000000000000000000000/3456099500817557230778994521731305153516820330259:ℝ) (31250000000000000000000000000/12265520686701554151561721611:ℝ) (1/10:ℝ) := by
 have h33 := source33 hβ hp
 have h34 := source34 hβ h33
 have h35 := source35 hβ h34
 have h36 := source36 hβ h35
 exact h36
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0033_0036
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0037_0040
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0037_0040

theorem source37 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3454341286542246651921875000000000000000000000000/3456099500817557230778994521731305153516820330259:ℝ) (31250000000000000000000000000/12265520686701554151561721611:ℝ) (1/10:ℝ)) :
 GlobalSource (3978828972154909035875500000000000000000000000000000/3980913147666429327954040364643984948152564058630993:ℝ) (1000000000000000000000000000000/392578908959268692403252521581:ℝ) (1/10:ℝ) := by
 have heps : 0<p37.toReal.eps := by norm_num [p37,Params.toReal]
 have hcap : p37.toReal.cap=1/10 := by norm_num [p37,Params.toReal]
 have hi : GlobalSource (p37.toReal.state (((cells37 0).2:ℝ)/(p37.den:ℝ))).B (p37.toReal.state (((cells37 0).2:ℝ)/(p37.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p37,cells37,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells37 0).1 < (cells37 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p37) hw0 heps hcap (commonSigns37 0) (highSigns37 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns37 0)
   (u:=((cells37 0).1:ℝ)/(p37.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p37.toReal.state (((cells37 0).1:ℝ)/(p37.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(392578908959268692403252521581/1000000000000000000000000000000:ℝ)) (by norm_num [p37,cells37,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p37,cells37,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source38 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3978828972154909035875500000000000000000000000000000/3980913147666429327954040364643984948152564058630993:ℝ) (1000000000000000000000000000000/392578908959268692403252521581:ℝ) (1/10:ℝ)) :
 GlobalSource (1989128391106574964368500000000000000000000000000000/1990199901158039855795623093146341861713504619672139:ℝ) (1000000000000000000000000000000/392661224668271059657707347849:ℝ) (1/10:ℝ) := by
 have heps : 0<p38.toReal.eps := by norm_num [p38,Params.toReal]
 have hcap : p38.toReal.cap=1/10 := by norm_num [p38,Params.toReal]
 have hi : GlobalSource (p38.toReal.state (((cells38 0).2:ℝ)/(p38.den:ℝ))).B (p38.toReal.state (((cells38 0).2:ℝ)/(p38.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p38,cells38,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells38 0).1 < (cells38 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p38) hw0 heps hcap (commonSigns38 0) (highSigns38 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns38 0)
   (u:=((cells38 0).1:ℝ)/(p38.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p38.toReal.state (((cells38 0).1:ℝ)/(p38.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(392661224668271059657707347849/1000000000000000000000000000000:ℝ)) (by norm_num [p38,cells38,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p38,cells38,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source39 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1989128391106574964368500000000000000000000000000000/1990199901158039855795623093146341861713504619672139:ℝ) (1000000000000000000000000000000/392661224668271059657707347849:ℝ) (1/10:ℝ)) :
 GlobalSource (1325894864090463607199500000000000000000000000000000/1326628862951141059235194972691058671540499899960261:ℝ) (1000000000000000000000000000000/392743609167619761064708439113:ℝ) (1/10:ℝ) := by
 have heps : 0<p39.toReal.eps := by norm_num [p39,Params.toReal]
 have hcap : p39.toReal.cap=1/10 := by norm_num [p39,Params.toReal]
 have hi : GlobalSource (p39.toReal.state (((cells39 0).2:ℝ)/(p39.den:ℝ))).B (p39.toReal.state (((cells39 0).2:ℝ)/(p39.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p39,cells39,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells39 0).1 < (cells39 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p39) hw0 heps hcap (commonSigns39 0) (highSigns39 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns39 0)
   (u:=((cells39 0).1:ℝ)/(p39.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p39.toReal.state (((cells39 0).1:ℝ)/(p39.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(392743609167619761064708439113/1000000000000000000000000000000:ℝ)) (by norm_num [p39,cells39,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p39,cells39,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source40 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1325894864090463607199500000000000000000000000000000/1326628862951141059235194972691058671540499899960261:ℝ) (1000000000000000000000000000000/392743609167619761064708439113:ℝ) (1/10:ℝ)) :
 GlobalSource (19885562011648158572300000000000000000000000000000/19896867536206486488979492179412829043842279750829:ℝ) (200000000000000000000000000000/78565212504717263238041106041:ℝ) (1/10:ℝ) := by
 have heps : 0<p40.toReal.eps := by norm_num [p40,Params.toReal]
 have hcap : p40.toReal.cap=1/10 := by norm_num [p40,Params.toReal]
 have hi : GlobalSource (p40.toReal.state (((cells40 0).2:ℝ)/(p40.den:ℝ))).B (p40.toReal.state (((cells40 0).2:ℝ)/(p40.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p40,cells40,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells40 0).1 < (cells40 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p40) hw0 heps hcap (commonSigns40 0) (highSigns40 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns40 0)
   (u:=((cells40 0).1:ℝ)/(p40.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p40.toReal.state (((cells40 0).1:ℝ)/(p40.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(78565212504717263238041106041/200000000000000000000000000000:ℝ)) (by norm_num [p40,cells40,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p40,cells40,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3454341286542246651921875000000000000000000000000/3456099500817557230778994521731305153516820330259:ℝ) (31250000000000000000000000000/12265520686701554151561721611:ℝ) (1/10:ℝ)) :
 GlobalSource (19885562011648158572300000000000000000000000000000/19896867536206486488979492179412829043842279750829:ℝ) (200000000000000000000000000000/78565212504717263238041106041:ℝ) (1/10:ℝ) := by
 have h37 := source37 hβ hp
 have h38 := source38 hβ h37
 have h39 := source39 hβ h38
 have h40 := source40 hβ h39
 exact h40
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0037_0040
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0041_0044
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0041_0044

theorem source41 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19885562011648158572300000000000000000000000000000/19896867536206486488979492179412829043842279750829:ℝ) (200000000000000000000000000000/78565212504717263238041106041:ℝ) (1/10:ℝ)) :
 GlobalSource (6061799104249805803843750000000000000000000000000/6065336215613918935139037517240350896500029648279:ℝ) (62500000000000000000000000000/24556786550159437032133937191:ℝ) (1/10:ℝ) := by
 have heps : 0<p41.toReal.eps := by norm_num [p41,Params.toReal]
 have hcap : p41.toReal.cap=1/10 := by norm_num [p41,Params.toReal]
 have hi : GlobalSource (p41.toReal.state (((cells41 0).2:ℝ)/(p41.den:ℝ))).B (p41.toReal.state (((cells41 0).2:ℝ)/(p41.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p41,cells41,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells41 0).1 < (cells41 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p41) hw0 heps hcap (commonSigns41 0) (highSigns41 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns41 0)
   (u:=((cells41 0).1:ℝ)/(p41.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p41.toReal.state (((cells41 0).1:ℝ)/(p41.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(24556786550159437032133937191/62500000000000000000000000000:ℝ)) (by norm_num [p41,cells41,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p41,cells41,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source42 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (6061799104249805803843750000000000000000000000000/6065336215613918935139037517240350896500029648279:ℝ) (62500000000000000000000000000/24556786550159437032133937191:ℝ) (1/10:ℝ)) :
 GlobalSource (662661337074352250030500000000000000000000000000000/663057956570157230029165360940542964725446976485163:ℝ) (1000000000000000000000000000000/392991176071002960574136496061:ℝ) (1/10:ℝ) := by
 have heps : 0<p42.toReal.eps := by norm_num [p42,Params.toReal]
 have hcap : p42.toReal.cap=1/10 := by norm_num [p42,Params.toReal]
 have hi : GlobalSource (p42.toReal.state (((cells42 0).2:ℝ)/(p42.den:ℝ))).B (p42.toReal.state (((cells42 0).2:ℝ)/(p42.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p42,cells42,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells42 0).1 < (cells42 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p42) hw0 heps hcap (commonSigns42 0) (highSigns42 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns42 0)
   (u:=((cells42 0).1:ℝ)/(p42.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p42.toReal.state (((cells42 0).1:ℝ)/(p42.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(392991176071002960574136496061/1000000000000000000000000000000:ℝ)) (by norm_num [p42,cells42,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p42,cells42,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source43 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (662661337074352250030500000000000000000000000000000/663057956570157230029165360940542964725446976485163:ℝ) (1000000000000000000000000000000/392991176071002960574136496061:ℝ) (1/10:ℝ)) :
 GlobalSource (397539583250435439304450000000000000000000000000000/397783505313934519137383021194030372051714315126887:ℝ) (100000000000000000000000000000/39307383639554044944118669861:ℝ) (1/10:ℝ) := by
 have heps : 0<p43.toReal.eps := by norm_num [p43,Params.toReal]
 have hcap : p43.toReal.cap=1/10 := by norm_num [p43,Params.toReal]
 have hi : GlobalSource (p43.toReal.state (((cells43 0).2:ℝ)/(p43.den:ℝ))).B (p43.toReal.state (((cells43 0).2:ℝ)/(p43.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p43,cells43,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells43 0).1 < (cells43 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p43) hw0 heps hcap (commonSigns43 0) (highSigns43 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns43 0)
   (u:=((cells43 0).1:ℝ)/(p43.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p43.toReal.state (((cells43 0).1:ℝ)/(p43.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(39307383639554044944118669861/100000000000000000000000000000:ℝ)) (by norm_num [p43,cells43,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p43,cells43,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source44 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (397539583250435439304450000000000000000000000000000/397783505313934519137383021194030372051714315126887:ℝ) (100000000000000000000000000000/39307383639554044944118669861:ℝ) (1/10:ℝ)) :
 GlobalSource (496852955320324410738250000000000000000000000000000/497165312320192095329343733102112665534513399757313:ℝ) (500000000000000000000000000000/196578282921435451270253769707:ℝ) (1/10:ℝ) := by
 have heps : 0<p44.toReal.eps := by norm_num [p44,Params.toReal]
 have hcap : p44.toReal.cap=1/10 := by norm_num [p44,Params.toReal]
 have hi : GlobalSource (p44.toReal.state (((cells44 0).2:ℝ)/(p44.den:ℝ))).B (p44.toReal.state (((cells44 0).2:ℝ)/(p44.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p44,cells44,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells44 0).1 < (cells44 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p44) hw0 heps hcap (commonSigns44 0) (highSigns44 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns44 0)
   (u:=((cells44 0).1:ℝ)/(p44.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p44.toReal.state (((cells44 0).1:ℝ)/(p44.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(196578282921435451270253769707/500000000000000000000000000000:ℝ)) (by norm_num [p44,cells44,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p44,cells44,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19885562011648158572300000000000000000000000000000/19896867536206486488979492179412829043842279750829:ℝ) (200000000000000000000000000000/78565212504717263238041106041:ℝ) (1/10:ℝ)) :
 GlobalSource (496852955320324410738250000000000000000000000000000/497165312320192095329343733102112665534513399757313:ℝ) (500000000000000000000000000000/196578282921435451270253769707:ℝ) (1/10:ℝ) := by
 have h41 := source41 hβ hp
 have h42 := source42 hβ h41
 have h43 := source43 hβ h42
 have h44 := source44 hβ h43
 exact h44
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0041_0044
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0045_0048
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0045_0048

theorem source45 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (496852955320324410738250000000000000000000000000000/497165312320192095329343733102112665534513399757313:ℝ) (500000000000000000000000000000/196578282921435451270253769707:ℝ) (1/10:ℝ)) :
 GlobalSource (52990019368277815716900000000000000000000000000000/53024134342017447952444088813811924075809784870307:ℝ) (200000000000000000000000000000/78647872895962226766467077201:ℝ) (1/10:ℝ) := by
 have heps : 0<p45.toReal.eps := by norm_num [p45,Params.toReal]
 have hcap : p45.toReal.cap=1/10 := by norm_num [p45,Params.toReal]
 have hi : GlobalSource (p45.toReal.state (((cells45 0).2:ℝ)/(p45.den:ℝ))).B (p45.toReal.state (((cells45 0).2:ℝ)/(p45.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p45,cells45,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells45 0).1 < (cells45 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p45) hw0 heps hcap (commonSigns45 0) (highSigns45 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns45 0)
   (u:=((cells45 0).1:ℝ)/(p45.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p45.toReal.state (((cells45 0).1:ℝ)/(p45.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(78647872895962226766467077201/200000000000000000000000000000:ℝ)) (by norm_num [p45,cells45,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p45,cells45,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source46 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (52990019368277815716900000000000000000000000000000/53024134342017447952444088813811924075809784870307:ℝ) (200000000000000000000000000000/78647872895962226766467077201:ℝ) (1/10:ℝ)) :
 GlobalSource (1986839631339538535814500000000000000000000000000000/1988148892186320447417966449610588920632779982971579:ℝ) (1000000000000000000000000000000/393322232373287484310400167517:ℝ) (1/10:ℝ) := by
 have heps : 0<p46.toReal.eps := by norm_num [p46,Params.toReal]
 have hcap : p46.toReal.cap=1/10 := by norm_num [p46,Params.toReal]
 have hi : GlobalSource (p46.toReal.state (((cells46 0).2:ℝ)/(p46.den:ℝ))).B (p46.toReal.state (((cells46 0).2:ℝ)/(p46.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p46,cells46,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells46 0).1 < (cells46 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p46) hw0 heps hcap (commonSigns46 0) (highSigns46 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns46 0)
   (u:=((cells46 0).1:ℝ)/(p46.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p46.toReal.state (((cells46 0).1:ℝ)/(p46.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(393322232373287484310400167517/1000000000000000000000000000000:ℝ)) (by norm_num [p46,cells46,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p46,cells46,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source47 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1986839631339538535814500000000000000000000000000000/1988148892186320447417966449610588920632779982971579:ℝ) (1000000000000000000000000000000/393322232373287484310400167517:ℝ) (1/10:ℝ)) :
 GlobalSource (3973107072737317964490500000000000000000000000000000/3975785624689703264800281933238371604319605525820631:ℝ) (1000000000000000000000000000000/393405169590335978878553134217:ℝ) (1/10:ℝ) := by
 have heps : 0<p47.toReal.eps := by norm_num [p47,Params.toReal]
 have hcap : p47.toReal.cap=1/10 := by norm_num [p47,Params.toReal]
 have hi : GlobalSource (p47.toReal.state (((cells47 0).2:ℝ)/(p47.den:ℝ))).B (p47.toReal.state (((cells47 0).2:ℝ)/(p47.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p47,cells47,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells47 0).1 < (cells47 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p47) hw0 heps hcap (commonSigns47 0) (highSigns47 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns47 0)
   (u:=((cells47 0).1:ℝ)/(p47.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p47.toReal.state (((cells47 0).1:ℝ)/(p47.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(393405169590335978878553134217/1000000000000000000000000000000:ℝ)) (by norm_num [p47,cells47,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p47,cells47,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source48 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3973107072737317964490500000000000000000000000000000/3975785624689703264800281933238371604319605525820631:ℝ) (1000000000000000000000000000000/393405169590335978878553134217:ℝ) (1/10:ℝ)) :
 GlobalSource (41380571695787071430750000000000000000000000000000/41409099964238066912448220112861655861697766663899:ℝ) (500000000000000000000000000000/196744088099051241779541550421:ℝ) (1/10:ℝ) := by
 have heps : 0<p48.toReal.eps := by norm_num [p48,Params.toReal]
 have hcap : p48.toReal.cap=1/10 := by norm_num [p48,Params.toReal]
 have hi : GlobalSource (p48.toReal.state (((cells48 0).2:ℝ)/(p48.den:ℝ))).B (p48.toReal.state (((cells48 0).2:ℝ)/(p48.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p48,cells48,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells48 0).1 < (cells48 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p48) hw0 heps hcap (commonSigns48 0) (highSigns48 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns48 0)
   (u:=((cells48 0).1:ℝ)/(p48.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p48.toReal.state (((cells48 0).1:ℝ)/(p48.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(196744088099051241779541550421/500000000000000000000000000000:ℝ)) (by norm_num [p48,cells48,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p48,cells48,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (496852955320324410738250000000000000000000000000000/497165312320192095329343733102112665534513399757313:ℝ) (500000000000000000000000000000/196578282921435451270253769707:ℝ) (1/10:ℝ)) :
 GlobalSource (41380571695787071430750000000000000000000000000000/41409099964238066912448220112861655861697766663899:ℝ) (500000000000000000000000000000/196744088099051241779541550421:ℝ) (1/10:ℝ) := by
 have h45 := source45 hβ hp
 have h46 := source46 hβ h45
 have h47 := source47 hβ h46
 have h48 := source48 hβ h47
 exact h48
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0045_0048
