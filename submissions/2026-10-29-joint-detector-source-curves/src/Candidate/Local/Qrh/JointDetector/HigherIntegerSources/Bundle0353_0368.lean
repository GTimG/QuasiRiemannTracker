/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0353_0356
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0357_0360
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0361_0364
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0365_0368
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0353_0356
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0353_0356

theorem source353 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19242325000000000000000000000000000/19773385820870438030345790051037881:ℝ) (50000000000000000000000000000/24439375908743692557025692239:ℝ) (1/10:ℝ)) :
 GlobalSource (192298250000000000000000000000000000/197650084232905334677577387952579519:ℝ) (500000000000000000000000000000/244743962179434253091743826861:ℝ) (1/10:ℝ) := by
 have heps : 0<p353.toReal.eps := by norm_num [p353,Params.toReal]
 have hcap : p353.toReal.cap=1/10 := by norm_num [p353,Params.toReal]
 have hi : GlobalSource (p353.toReal.state (((cells353 0).2:ℝ)/(p353.den:ℝ))).B (p353.toReal.state (((cells353 0).2:ℝ)/(p353.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p353,cells353,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells353 0).1 < (cells353 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p353) hw0 heps hcap (commonSigns353 0) (highSigns353 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns353 0)
   (u:=((cells353 0).1:ℝ)/(p353.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p353.toReal.state (((cells353 0).1:ℝ)/(p353.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(244743962179434253091743826861/500000000000000000000000000000:ℝ)) (by norm_num [p353,cells353,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p353,cells353,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source354 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (192298250000000000000000000000000000/197650084232905334677577387952579519:ℝ) (500000000000000000000000000000/244743962179434253091743826861:ℝ) (1/10:ℝ)) :
 GlobalSource (1439500000000000000000000000000000/1479898701031461032042215999366951:ℝ) (1000000000000000000000000000000/490191349948826474272709835923:ℝ) (1/10:ℝ) := by
 have heps : 0<p354.toReal.eps := by norm_num [p354,Params.toReal]
 have hcap : p354.toReal.cap=1/10 := by norm_num [p354,Params.toReal]
 have hi : GlobalSource (p354.toReal.state (((cells354 0).2:ℝ)/(p354.den:ℝ))).B (p354.toReal.state (((cells354 0).2:ℝ)/(p354.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p354,cells354,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells354 0).1 < (cells354 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p354) hw0 heps hcap (commonSigns354 0) (highSigns354 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns354 0)
   (u:=((cells354 0).1:ℝ)/(p354.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p354.toReal.state (((cells354 0).1:ℝ)/(p354.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(490191349948826474272709835923/1000000000000000000000000000000:ℝ)) (by norm_num [p354,cells354,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p354,cells354,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source355 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1439500000000000000000000000000000/1479898701031461032042215999366951:ℝ) (1000000000000000000000000000000/490191349948826474272709835923:ℝ) (1/10:ℝ)) :
 GlobalSource (24006031250000000000000000000000000/24685379440506226318424711553689097:ℝ) (62500000000000000000000000000/30681113278504940246296151843:ℝ) (1/10:ℝ) := by
 have heps : 0<p355.toReal.eps := by norm_num [p355,Params.toReal]
 have hcap : p355.toReal.cap=1/10 := by norm_num [p355,Params.toReal]
 have hi : GlobalSource (p355.toReal.state (((cells355 0).2:ℝ)/(p355.den:ℝ))).B (p355.toReal.state (((cells355 0).2:ℝ)/(p355.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p355,cells355,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells355 0).1 < (cells355 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p355) hw0 heps hcap (commonSigns355 0) (highSigns355 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns355 0)
   (u:=((cells355 0).1:ℝ)/(p355.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p355.toReal.state (((cells355 0).1:ℝ)/(p355.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(30681113278504940246296151843/62500000000000000000000000000:ℝ)) (by norm_num [p355,cells355,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p355,cells355,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source356 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24006031250000000000000000000000000/24685379440506226318424711553689097:ℝ) (62500000000000000000000000000/30681113278504940246296151843:ℝ) (1/10:ℝ)) :
 GlobalSource (383846500000000000000000000000000000/394799522587497272732000259905391807:ℝ) (1000000000000000000000000000000/491607329524862775308531613833:ℝ) (1/10:ℝ) := by
 have heps : 0<p356.toReal.eps := by norm_num [p356,Params.toReal]
 have hcap : p356.toReal.cap=1/10 := by norm_num [p356,Params.toReal]
 have hi : GlobalSource (p356.toReal.state (((cells356 0).2:ℝ)/(p356.den:ℝ))).B (p356.toReal.state (((cells356 0).2:ℝ)/(p356.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p356,cells356,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells356 0).1 < (cells356 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p356) hw0 heps hcap (commonSigns356 0) (highSigns356 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns356 0)
   (u:=((cells356 0).1:ℝ)/(p356.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p356.toReal.state (((cells356 0).1:ℝ)/(p356.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(491607329524862775308531613833/1000000000000000000000000000000:ℝ)) (by norm_num [p356,cells356,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p356,cells356,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19242325000000000000000000000000000/19773385820870438030345790051037881:ℝ) (50000000000000000000000000000/24439375908743692557025692239:ℝ) (1/10:ℝ)) :
 GlobalSource (383846500000000000000000000000000000/394799522587497272732000259905391807:ℝ) (1000000000000000000000000000000/491607329524862775308531613833:ℝ) (1/10:ℝ) := by
 have h353 := source353 hβ hp
 have h354 := source354 hβ h353
 have h355 := source355 hβ h354
 have h356 := source356 hβ h355
 exact h356
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0353_0356
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0357_0360
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0357_0360

theorem source357 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (383846500000000000000000000000000000/394799522587497272732000259905391807:ℝ) (1000000000000000000000000000000/491607329524862775308531613833:ℝ) (1/10:ℝ)) :
 GlobalSource (127865500000000000000000000000000000/131544436099619324228538374919815087:ℝ) (1000000000000000000000000000000/492319918933577317626353889959:ℝ) (1/10:ℝ) := by
 have heps : 0<p357.toReal.eps := by norm_num [p357,Params.toReal]
 have hcap : p357.toReal.cap=1/10 := by norm_num [p357,Params.toReal]
 have hi : GlobalSource (p357.toReal.state (((cells357 0).2:ℝ)/(p357.den:ℝ))).B (p357.toReal.state (((cells357 0).2:ℝ)/(p357.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p357,cells357,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells357 0).1 < (cells357 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p357) hw0 heps hcap (commonSigns357 0) (highSigns357 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns357 0)
   (u:=((cells357 0).1:ℝ)/(p357.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p357.toReal.state (((cells357 0).1:ℝ)/(p357.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(492319918933577317626353889959/1000000000000000000000000000000:ℝ)) (by norm_num [p357,cells357,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p357,cells357,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source358 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (127865500000000000000000000000000000/131544436099619324228538374919815087:ℝ) (1000000000000000000000000000000/492319918933577317626353889959:ℝ) (1/10:ℝ)) :
 GlobalSource (47918312500000000000000000000000000/49308428586141894540483499830810591:ℝ) (125000000000000000000000000000/61629449824507198089793007729:ℝ) (1/10:ℝ) := by
 have heps : 0<p358.toReal.eps := by norm_num [p358,Params.toReal]
 have hcap : p358.toReal.cap=1/10 := by norm_num [p358,Params.toReal]
 have hi : GlobalSource (p358.toReal.state (((cells358 0).2:ℝ)/(p358.den:ℝ))).B (p358.toReal.state (((cells358 0).2:ℝ)/(p358.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p358,cells358,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells358 0).1 < (cells358 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p358) hw0 heps hcap (commonSigns358 0) (highSigns358 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns358 0)
   (u:=((cells358 0).1:ℝ)/(p358.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p358.toReal.state (((cells358 0).1:ℝ)/(p358.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(61629449824507198089793007729/125000000000000000000000000000:ℝ)) (by norm_num [p358,cells358,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p358,cells358,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source359 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (47918312500000000000000000000000000/49308428586141894540483499830810591:ℝ) (125000000000000000000000000000/61629449824507198089793007729:ℝ) (1/10:ℝ)) :
 GlobalSource (191548250000000000000000000000000000/197150942133491280510824347883437179:ℝ) (500000000000000000000000000000/246877193281430241104291933401:ℝ) (1/10:ℝ) := by
 have heps : 0<p359.toReal.eps := by norm_num [p359,Params.toReal]
 have hcap : p359.toReal.cap=1/10 := by norm_num [p359,Params.toReal]
 have hi : GlobalSource (p359.toReal.state (((cells359 0).2:ℝ)/(p359.den:ℝ))).B (p359.toReal.state (((cells359 0).2:ℝ)/(p359.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p359,cells359,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells359 0).1 < (cells359 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p359) hw0 heps hcap (commonSigns359 0) (highSigns359 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns359 0)
   (u:=((cells359 0).1:ℝ)/(p359.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p359.toReal.state (((cells359 0).1:ℝ)/(p359.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(246877193281430241104291933401/500000000000000000000000000000:ℝ)) (by norm_num [p359,cells359,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p359,cells359,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source360 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (191548250000000000000000000000000000/197150942133491280510824347883437179:ℝ) (500000000000000000000000000000/246877193281430241104291933401:ℝ) (1/10:ℝ)) :
 GlobalSource (4726500000000000000000000000000000/4865884883244027041791409033523173:ℝ) (1000000000000000000000000000000/494476301022566383489094721747:ℝ) (1/10:ℝ) := by
 have heps : 0<p360.toReal.eps := by norm_num [p360,Params.toReal]
 have hcap : p360.toReal.cap=1/10 := by norm_num [p360,Params.toReal]
 have hi : GlobalSource (p360.toReal.state (((cells360 0).2:ℝ)/(p360.den:ℝ))).B (p360.toReal.state (((cells360 0).2:ℝ)/(p360.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p360,cells360,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells360 0).1 < (cells360 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p360) hw0 heps hcap (commonSigns360 0) (highSigns360 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns360 0)
   (u:=((cells360 0).1:ℝ)/(p360.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p360.toReal.state (((cells360 0).1:ℝ)/(p360.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(494476301022566383489094721747/1000000000000000000000000000000:ℝ)) (by norm_num [p360,cells360,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p360,cells360,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (383846500000000000000000000000000000/394799522587497272732000259905391807:ℝ) (1000000000000000000000000000000/491607329524862775308531613833:ℝ) (1/10:ℝ)) :
 GlobalSource (4726500000000000000000000000000000/4865884883244027041791409033523173:ℝ) (1000000000000000000000000000000/494476301022566383489094721747:ℝ) (1/10:ℝ) := by
 have h357 := source357 hβ hp
 have h358 := source358 hβ h357
 have h359 := source359 hβ h358
 have h360 := source360 hβ h359
 exact h360
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0357_0360
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0361_0364
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0361_0364

theorem source361 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (4726500000000000000000000000000000/4865884883244027041791409033523173:ℝ) (1000000000000000000000000000000/494476301022566383489094721747:ℝ) (1/10:ℝ)) :
 GlobalSource (5886100000000000000000000000000000/6061104661978099356592235653556331:ℝ) (200000000000000000000000000000/99040272060619110906269601757:ℝ) (1/10:ℝ) := by
 have heps : 0<p361.toReal.eps := by norm_num [p361,Params.toReal]
 have hcap : p361.toReal.cap=1/10 := by norm_num [p361,Params.toReal]
 have hi : GlobalSource (p361.toReal.state (((cells361 0).2:ℝ)/(p361.den:ℝ))).B (p361.toReal.state (((cells361 0).2:ℝ)/(p361.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p361,cells361,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells361 0).1 < (cells361 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p361) hw0 heps hcap (commonSigns361 0) (highSigns361 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns361 0)
   (u:=((cells361 0).1:ℝ)/(p361.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p361.toReal.state (((cells361 0).1:ℝ)/(p361.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(99040272060619110906269601757/200000000000000000000000000000:ℝ)) (by norm_num [p361,cells361,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p361,cells361,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source362 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (5886100000000000000000000000000000/6061104661978099356592235653556331:ℝ) (200000000000000000000000000000/99040272060619110906269601757:ℝ) (1/10:ℝ)) :
 GlobalSource (382346500000000000000000000000000000/393807267238240516428858350472591951:ℝ) (1000000000000000000000000000000/495929582873039730843981959569:ℝ) (1/10:ℝ) := by
 have heps : 0<p362.toReal.eps := by norm_num [p362,Params.toReal]
 have hcap : p362.toReal.cap=1/10 := by norm_num [p362,Params.toReal]
 have hi : GlobalSource (p362.toReal.state (((cells362 0).2:ℝ)/(p362.den:ℝ))).B (p362.toReal.state (((cells362 0).2:ℝ)/(p362.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p362,cells362,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells362 0).1 < (cells362 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p362) hw0 heps hcap (commonSigns362 0) (highSigns362 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns362 0)
   (u:=((cells362 0).1:ℝ)/(p362.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p362.toReal.state (((cells362 0).1:ℝ)/(p362.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(495929582873039730843981959569/1000000000000000000000000000000:ℝ)) (by norm_num [p362,cells362,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p362,cells362,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source363 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (382346500000000000000000000000000000/393807267238240516428858350472591951:ℝ) (1000000000000000000000000000000/495929582873039730843981959569:ℝ) (1/10:ℝ)) :
 GlobalSource (127365500000000000000000000000000000/131214356229111590776717471722587329:ℝ) (1000000000000000000000000000000/496660987343009053141898050753:ℝ) (1/10:ℝ) := by
 have heps : 0<p363.toReal.eps := by norm_num [p363,Params.toReal]
 have hcap : p363.toReal.cap=1/10 := by norm_num [p363,Params.toReal]
 have hi : GlobalSource (p363.toReal.state (((cells363 0).2:ℝ)/(p363.den:ℝ))).B (p363.toReal.state (((cells363 0).2:ℝ)/(p363.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p363,cells363,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells363 0).1 < (cells363 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p363) hw0 heps hcap (commonSigns363 0) (highSigns363 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns363 0)
   (u:=((cells363 0).1:ℝ)/(p363.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p363.toReal.state (((cells363 0).1:ℝ)/(p363.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(496660987343009053141898050753/1000000000000000000000000000000:ℝ)) (by norm_num [p363,cells363,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p363,cells363,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source364 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (127365500000000000000000000000000000/131214356229111590776717471722587329:ℝ) (1000000000000000000000000000000/496660987343009053141898050753:ℝ) (1/10:ℝ)) :
 GlobalSource (610954400000000000000000000000000/629566732629116157952616592899991:ℝ) (1600000000000000000000000000/795832947947191314587565329:ℝ) (1/10:ℝ) := by
 have heps : 0<p364.toReal.eps := by norm_num [p364,Params.toReal]
 have hcap : p364.toReal.cap=1/10 := by norm_num [p364,Params.toReal]
 have hi : GlobalSource (p364.toReal.state (((cells364 0).2:ℝ)/(p364.den:ℝ))).B (p364.toReal.state (((cells364 0).2:ℝ)/(p364.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p364,cells364,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells364 0).1 < (cells364 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p364) hw0 heps hcap (commonSigns364 0) (highSigns364 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns364 0)
   (u:=((cells364 0).1:ℝ)/(p364.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p364.toReal.state (((cells364 0).1:ℝ)/(p364.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(795832947947191314587565329/1600000000000000000000000000:ℝ)) (by norm_num [p364,cells364,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p364,cells364,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (4726500000000000000000000000000000/4865884883244027041791409033523173:ℝ) (1000000000000000000000000000000/494476301022566383489094721747:ℝ) (1/10:ℝ)) :
 GlobalSource (610954400000000000000000000000000/629566732629116157952616592899991:ℝ) (1600000000000000000000000000/795832947947191314587565329:ℝ) (1/10:ℝ) := by
 have h361 := source361 hβ hp
 have h362 := source362 hβ h361
 have h363 := source363 hβ h362
 have h364 := source364 hβ h363
 exact h364
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0361_0364
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0365_0368
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0365_0368

theorem source365 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (610954400000000000000000000000000/629566732629116157952616592899991:ℝ) (1600000000000000000000000000/795832947947191314587565329:ℝ) (1/10:ℝ)) :
 GlobalSource (23849781250000000000000000000000000/24582230335933890191433329937477057:ℝ) (62500000000000000000000000000/31133338571484158255770898083:ℝ) (1/10:ℝ) := by
 have heps : 0<p365.toReal.eps := by norm_num [p365,Params.toReal]
 have hcap : p365.toReal.cap=1/10 := by norm_num [p365,Params.toReal]
 have hi : GlobalSource (p365.toReal.state (((cells365 0).2:ℝ)/(p365.den:ℝ))).B (p365.toReal.state (((cells365 0).2:ℝ)/(p365.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p365,cells365,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells365 0).1 < (cells365 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p365) hw0 heps hcap (commonSigns365 0) (highSigns365 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns365 0)
   (u:=((cells365 0).1:ℝ)/(p365.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p365.toReal.state (((cells365 0).1:ℝ)/(p365.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(31133338571484158255770898083/62500000000000000000000000000:ℝ)) (by norm_num [p365,cells365,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p365,cells365,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source366 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (23849781250000000000000000000000000/24582230335933890191433329937477057:ℝ) (62500000000000000000000000000/31133338571484158255770898083:ℝ) (1/10:ℝ)) :
 GlobalSource (127115500000000000000000000000000000/131050833884489980009059364604161833:ℝ) (1000000000000000000000000000000/498874480418168660790578220981:ℝ) (1/10:ℝ) := by
 have heps : 0<p366.toReal.eps := by norm_num [p366,Params.toReal]
 have hcap : p366.toReal.cap=1/10 := by norm_num [p366,Params.toReal]
 have hi : GlobalSource (p366.toReal.state (((cells366 0).2:ℝ)/(p366.den:ℝ))).B (p366.toReal.state (((cells366 0).2:ℝ)/(p366.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p366,cells366,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells366 0).1 < (cells366 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p366) hw0 heps hcap (commonSigns366 0) (highSigns366 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns366 0)
   (u:=((cells366 0).1:ℝ)/(p366.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p366.toReal.state (((cells366 0).1:ℝ)/(p366.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(498874480418168660790578220981/1000000000000000000000000000000:ℝ)) (by norm_num [p366,cells366,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p366,cells366,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source367 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (127115500000000000000000000000000000/131050833884489980009059364604161833:ℝ) (1000000000000000000000000000000/498874480418168660790578220981:ℝ) (1/10:ℝ)) :
 GlobalSource (47637062500000000000000000000000000/49123707156435404116744344687293679:ℝ) (125000000000000000000000000000/62452350185341083497963134901:ℝ) (1/10:ℝ) := by
 have heps : 0<p367.toReal.eps := by norm_num [p367,Params.toReal]
 have hcap : p367.toReal.cap=1/10 := by norm_num [p367,Params.toReal]
 have hi : GlobalSource (p367.toReal.state (((cells367 0).2:ℝ)/(p367.den:ℝ))).B (p367.toReal.state (((cells367 0).2:ℝ)/(p367.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p367,cells367,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells367 0).1 < (cells367 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p367) hw0 heps hcap (commonSigns367 0) (highSigns367 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns367 0)
   (u:=((cells367 0).1:ℝ)/(p367.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p367.toReal.state (((cells367 0).1:ℝ)/(p367.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(62452350185341083497963134901/125000000000000000000000000000:ℝ)) (by norm_num [p367,cells367,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p367,cells367,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source368 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (47637062500000000000000000000000000/49123707156435404116744344687293679:ℝ) (125000000000000000000000000000/62452350185341083497963134901:ℝ) (1/10:ℝ)) :
 GlobalSource (190423250000000000000000000000000000/196413576346749754754208100812485763:ℝ) (500000000000000000000000000000/250183199839442597183478478997:ℝ) (1/10:ℝ) := by
 have heps : 0<p368.toReal.eps := by norm_num [p368,Params.toReal]
 have hcap : p368.toReal.cap=1/10 := by norm_num [p368,Params.toReal]
 have hi : GlobalSource (p368.toReal.state (((cells368 0).2:ℝ)/(p368.den:ℝ))).B (p368.toReal.state (((cells368 0).2:ℝ)/(p368.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p368,cells368,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells368 0).1 < (cells368 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p368) hw0 heps hcap (commonSigns368 0) (highSigns368 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns368 0)
   (u:=((cells368 0).1:ℝ)/(p368.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p368.toReal.state (((cells368 0).1:ℝ)/(p368.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(250183199839442597183478478997/500000000000000000000000000000:ℝ)) (by norm_num [p368,cells368,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p368,cells368,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (610954400000000000000000000000000/629566732629116157952616592899991:ℝ) (1600000000000000000000000000/795832947947191314587565329:ℝ) (1/10:ℝ)) :
 GlobalSource (190423250000000000000000000000000000/196413576346749754754208100812485763:ℝ) (500000000000000000000000000000/250183199839442597183478478997:ℝ) (1/10:ℝ) := by
 have h365 := source365 hβ hp
 have h366 := source366 hβ h365
 have h367 := source367 hβ h366
 have h368 := source368 hβ h367
 exact h368
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0365_0368
