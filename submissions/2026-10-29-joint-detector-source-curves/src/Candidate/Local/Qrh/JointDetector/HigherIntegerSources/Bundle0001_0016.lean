/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0001_0004
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0005_0008
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0009_0012
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0013_0016
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0001_0004
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0001_0004

theorem source1 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (999999999999999/1000000000000000:ℝ) (2566860349445351169/1000000000000000000:ℝ) (1/10:ℝ)) :
 GlobalSource (159977112402329475714460000000000000000000000000000/159979269876216092716921950778145581512754830674169:ℝ) (40000000000000000000000000000/15586432303333850993969489001:ℝ) (1/10:ℝ) := by
 have heps : 0<p1.toReal.eps := by norm_num [p1,Params.toReal]
 have hcap : p1.toReal.cap=1/10 := by norm_num [p1,Params.toReal]
 have hi : GlobalSource (p1.toReal.state (((cells1 0).2:ℝ)/(p1.den:ℝ))).B (p1.toReal.state (((cells1 0).2:ℝ)/(p1.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p1,cells1,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells1 0).1 < (cells1 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p1) hw0 heps hcap (commonSigns1 0) (highSigns1 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns1 0)
   (u:=((cells1 0).1:ℝ)/(p1.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p1.toReal.state (((cells1 0).1:ℝ)/(p1.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(15586432303333850993969489001/40000000000000000000000000000:ℝ)) (by norm_num [p1,cells1,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p1,cells1,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source2 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (159977112402329475714460000000000000000000000000000/159979269876216092716921950778145581512754830674169:ℝ) (40000000000000000000000000000/15586432303333850993969489001:ℝ) (1/10:ℝ)) :
 GlobalSource (3998855620116477785723000000000000000000000000000/3998963627210632739954686458806317852956340860147:ℝ) (2000000000000000000000000000/779481380143713321057920563:ℝ) (1/10:ℝ) := by
 have heps : 0<p2.toReal.eps := by norm_num [p2,Params.toReal]
 have hcap : p2.toReal.cap=1/10 := by norm_num [p2,Params.toReal]
 have hi : GlobalSource (p2.toReal.state (((cells2 0).2:ℝ)/(p2.den:ℝ))).B (p2.toReal.state (((cells2 0).2:ℝ)/(p2.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p2,cells2,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells2 0).1 < (cells2 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p2) hw0 heps hcap (commonSigns2 0) (highSigns2 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns2 0)
   (u:=((cells2 0).1:ℝ)/(p2.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p2.toReal.state (((cells2 0).1:ℝ)/(p2.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(779481380143713321057920563/2000000000000000000000000000:ℝ)) (by norm_num [p2,cells2,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p2,cells2,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source3 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3998855620116477785723000000000000000000000000000/3998963627210632739954686458806317852956340860147:ℝ) (2000000000000000000000000000/779481380143713321057920563:ℝ) (1/10:ℝ)) :
 GlobalSource (266552228678314578572300000000000000000000000000000/266563042724749675888324577128903108254092323605287:ℝ) (200000000000000000000000000000/77964127807216652137432517623:ℝ) (1/10:ℝ) := by
 have heps : 0<p3.toReal.eps := by norm_num [p3,Params.toReal]
 have hcap : p3.toReal.cap=1/10 := by norm_num [p3,Params.toReal]
 have hi : GlobalSource (p3.toReal.state (((cells3 0).2:ℝ)/(p3.den:ℝ))).B (p3.toReal.state (((cells3 0).2:ℝ)/(p3.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p3,cells3,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells3 0).1 < (cells3 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p3) hw0 heps hcap (commonSigns3 0) (highSigns3 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns3 0)
   (u:=((cells3 0).1:ℝ)/(p3.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p3.toReal.state (((cells3 0).1:ℝ)/(p3.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(77964127807216652137432517623/200000000000000000000000000000:ℝ)) (by norm_num [p3,cells3,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p3,cells3,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source4 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (266552228678314578572300000000000000000000000000000/266563042724749675888324577128903108254092323605287:ℝ) (200000000000000000000000000000/77964127807216652137432517623:ℝ) (1/10:ℝ)) :
 GlobalSource (1561605953215999832596093750000000000000000000000/1561690542126170176653549652869392689388521943409:ℝ) (1562500000000000000000000000/609219772716380033409055961:ℝ) (1/10:ℝ) := by
 have heps : 0<p4.toReal.eps := by norm_num [p4,Params.toReal]
 have hcap : p4.toReal.cap=1/10 := by norm_num [p4,Params.toReal]
 have hi : GlobalSource (p4.toReal.state (((cells4 0).2:ℝ)/(p4.den:ℝ))).B (p4.toReal.state (((cells4 0).2:ℝ)/(p4.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p4,cells4,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells4 0).1 < (cells4 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p4) hw0 heps hcap (commonSigns4 0) (highSigns4 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns4 0)
   (u:=((cells4 0).1:ℝ)/(p4.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p4.toReal.state (((cells4 0).1:ℝ)/(p4.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(609219772716380033409055961/1562500000000000000000000000:ℝ)) (by norm_num [p4,cells4,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p4,cells4,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (999999999999999/1000000000000000:ℝ) (2566860349445351169/1000000000000000000:ℝ) (1/10:ℝ)) :
 GlobalSource (1561605953215999832596093750000000000000000000000/1561690542126170176653549652869392689388521943409:ℝ) (1562500000000000000000000000/609219772716380033409055961:ℝ) (1/10:ℝ) := by
 have h1 := source1 hβ hp
 have h2 := source2 hβ h1
 have h3 := source3 hβ h2
 have h4 := source4 hβ h3
 exact h4
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0001_0004
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0005_0008
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0005_0008

theorem source5 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1561605953215999832596093750000000000000000000000/1561690542126170176653549652869392689388521943409:ℝ) (1562500000000000000000000000/609219772716380033409055961:ℝ) (1/10:ℝ)) :
 GlobalSource (799427810058240092861500000000000000000000000000000/799482013616368477269837654749502558581853892467171:ℝ) (1000000000000000000000000000000/389980736641617067537857284659:ℝ) (1/10:ℝ) := by
 have heps : 0<p5.toReal.eps := by norm_num [p5,Params.toReal]
 have hcap : p5.toReal.cap=1/10 := by norm_num [p5,Params.toReal]
 have hi : GlobalSource (p5.toReal.state (((cells5 0).2:ℝ)/(p5.den:ℝ))).B (p5.toReal.state (((cells5 0).2:ℝ)/(p5.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p5,cells5,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells5 0).1 < (cells5 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p5) hw0 heps hcap (commonSigns5 0) (highSigns5 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns5 0)
   (u:=((cells5 0).1:ℝ)/(p5.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p5.toReal.state (((cells5 0).1:ℝ)/(p5.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(389980736641617067537857284659/1000000000000000000000000000000:ℝ)) (by norm_num [p5,cells5,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p5,cells5,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source6 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (799427810058240092861500000000000000000000000000000/799482013616368477269837654749502558581853892467171:ℝ) (1000000000000000000000000000000/389980736641617067537857284659:ℝ) (1/10:ℝ)) :
 GlobalSource (133218895344981378572300000000000000000000000000000/133229749384798170319119579443871410083026262426879:ℝ) (200000000000000000000000000000/78012177081629769346251466591:ℝ) (1/10:ℝ) := by
 have heps : 0<p6.toReal.eps := by norm_num [p6,Params.toReal]
 have hcap : p6.toReal.cap=1/10 := by norm_num [p6,Params.toReal]
 have hi : GlobalSource (p6.toReal.state (((cells6 0).2:ℝ)/(p6.den:ℝ))).B (p6.toReal.state (((cells6 0).2:ℝ)/(p6.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p6,cells6,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells6 0).1 < (cells6 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p6) hw0 heps hcap (commonSigns6 0) (highSigns6 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns6 0)
   (u:=((cells6 0).1:ℝ)/(p6.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p6.toReal.state (((cells6 0).1:ℝ)/(p6.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(78012177081629769346251466591/200000000000000000000000000000:ℝ)) (by norm_num [p6,cells6,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p6,cells6,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source7 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (133218895344981378572300000000000000000000000000000/133229749384798170319119579443871410083026262426879:ℝ) (200000000000000000000000000000/78012177081629769346251466591:ℝ) (1/10:ℝ)) :
 GlobalSource (1997997335203841125015250000000000000000000000000000/1998187514092832476820393316473383931663157150244917:ℝ) (500000000000000000000000000000/195070550450423136623264771699:ℝ) (1/10:ℝ) := by
 have heps : 0<p7.toReal.eps := by norm_num [p7,Params.toReal]
 have hcap : p7.toReal.cap=1/10 := by norm_num [p7,Params.toReal]
 have hi : GlobalSource (p7.toReal.state (((cells7 0).2:ℝ)/(p7.den:ℝ))).B (p7.toReal.state (((cells7 0).2:ℝ)/(p7.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p7,cells7,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells7 0).1 < (cells7 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p7) hw0 heps hcap (commonSigns7 0) (highSigns7 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns7 0)
   (u:=((cells7 0).1:ℝ)/(p7.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p7.toReal.state (((cells7 0).1:ℝ)/(p7.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(195070550450423136623264771699/500000000000000000000000000000:ℝ)) (by norm_num [p7,cells7,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p7,cells7,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source8 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1997997335203841125015250000000000000000000000000000/1998187514092832476820393316473383931663157150244917:ℝ) (500000000000000000000000000000/195070550450423136623264771699:ℝ) (1/10:ℝ)) :
 GlobalSource (249713905029120196430750000000000000000000000000000/249741106747722756986072034781433333649228704117073:ℝ) (500000000000000000000000000000/195110691591290436214813832317:ℝ) (1/10:ℝ) := by
 have heps : 0<p8.toReal.eps := by norm_num [p8,Params.toReal]
 have hcap : p8.toReal.cap=1/10 := by norm_num [p8,Params.toReal]
 have hi : GlobalSource (p8.toReal.state (((cells8 0).2:ℝ)/(p8.den:ℝ))).B (p8.toReal.state (((cells8 0).2:ℝ)/(p8.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p8,cells8,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells8 0).1 < (cells8 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p8) hw0 heps hcap (commonSigns8 0) (highSigns8 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns8 0)
   (u:=((cells8 0).1:ℝ)/(p8.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p8.toReal.state (((cells8 0).1:ℝ)/(p8.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(195110691591290436214813832317/500000000000000000000000000000:ℝ)) (by norm_num [p8,cells8,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p8,cells8,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1561605953215999832596093750000000000000000000000/1561690542126170176653549652869392689388521943409:ℝ) (1562500000000000000000000000/609219772716380033409055961:ℝ) (1/10:ℝ)) :
 GlobalSource (249713905029120196430750000000000000000000000000000/249741106747722756986072034781433333649228704117073:ℝ) (500000000000000000000000000000/195110691591290436214813832317:ℝ) (1/10:ℝ) := by
 have h5 := source5 hβ hp
 have h6 := source6 hβ h5
 have h7 := source7 hβ h6
 have h8 := source8 hβ h7
 exact h8
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0005_0008
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0009_0012
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0009_0012

theorem source9 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (249713905029120196430750000000000000000000000000000/249741106747722756986072034781433333649228704117073:ℝ) (500000000000000000000000000000/195110691591290436214813832317:ℝ) (1/10:ℝ)) :
 GlobalSource (443872254502684892861500000000000000000000000000000/443926724537156170818066740144967800101603141934731:ℝ) (1000000000000000000000000000000/390301732316328125331583131099:ℝ) (1/10:ℝ) := by
 have heps : 0<p9.toReal.eps := by norm_num [p9,Params.toReal]
 have hcap : p9.toReal.cap=1/10 := by norm_num [p9,Params.toReal]
 have hi : GlobalSource (p9.toReal.state (((cells9 0).2:ℝ)/(p9.den:ℝ))).B (p9.toReal.state (((cells9 0).2:ℝ)/(p9.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p9,cells9,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells9 0).1 < (cells9 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p9) hw0 heps hcap (commonSigns9 0) (highSigns9 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns9 0)
   (u:=((cells9 0).1:ℝ)/(p9.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p9.toReal.state (((cells9 0).1:ℝ)/(p9.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(390301732316328125331583131099/1000000000000000000000000000000:ℝ)) (by norm_num [p9,cells9,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p9,cells9,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source10 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (443872254502684892861500000000000000000000000000000/443926724537156170818066740144967800101603141934731:ℝ) (1000000000000000000000000000000/390301732316328125331583131099:ℝ) (1/10:ℝ)) :
 GlobalSource (19971390502912024643075000000000000000000000000000/19974117333775763213516352883826508420056473709877:ℝ) (50000000000000000000000000000/19519107418258380682708532533:ℝ) (1/10:ℝ) := by
 have heps : 0<p10.toReal.eps := by norm_num [p10,Params.toReal]
 have hcap : p10.toReal.cap=1/10 := by norm_num [p10,Params.toReal]
 have hi : GlobalSource (p10.toReal.state (((cells10 0).2:ℝ)/(p10.den:ℝ))).B (p10.toReal.state (((cells10 0).2:ℝ)/(p10.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p10,cells10,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells10 0).1 < (cells10 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p10) hw0 heps hcap (commonSigns10 0) (highSigns10 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns10 0)
   (u:=((cells10 0).1:ℝ)/(p10.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p10.toReal.state (((cells10 0).1:ℝ)/(p10.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(19519107418258380682708532533/50000000000000000000000000000:ℝ)) (by norm_num [p10,cells10,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p10,cells10,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source11 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (19971390502912024643075000000000000000000000000000/19974117333775763213516352883826508420056473709877:ℝ) (50000000000000000000000000000/19519107418258380682708532533:ℝ) (1/10:ℝ)) :
 GlobalSource (3993705910640645821476500000000000000000000000000000/3994306545682968997758654947475462071316626614098897:ℝ) (1000000000000000000000000000000/390462631392283164982989128483:ℝ) (1/10:ℝ) := by
 have heps : 0<p11.toReal.eps := by norm_num [p11,Params.toReal]
 have hcap : p11.toReal.cap=1/10 := by norm_num [p11,Params.toReal]
 have hi : GlobalSource (p11.toReal.state (((cells11 0).2:ℝ)/(p11.den:ℝ))).B (p11.toReal.state (((cells11 0).2:ℝ)/(p11.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p11,cells11,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells11 0).1 < (cells11 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p11) hw0 heps hcap (commonSigns11 0) (highSigns11 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns11 0)
   (u:=((cells11 0).1:ℝ)/(p11.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p11.toReal.state (((cells11 0).1:ℝ)/(p11.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(390462631392283164982989128483/1000000000000000000000000000000:ℝ)) (by norm_num [p11,cells11,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p11,cells11,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source12 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3993705910640645821476500000000000000000000000000000/3994306545682968997758654947475462071316626614098897:ℝ) (1000000000000000000000000000000/390462631392283164982989128483:ℝ) (1/10:ℝ)) :
 GlobalSource (166380571695786946430750000000000000000000000000000/166407906565634084539019439628426033063955436279739:ℝ) (500000000000000000000000000000/195271590730481499159855590531:ℝ) (1/10:ℝ) := by
 have heps : 0<p12.toReal.eps := by norm_num [p12,Params.toReal]
 have hcap : p12.toReal.cap=1/10 := by norm_num [p12,Params.toReal]
 have hi : GlobalSource (p12.toReal.state (((cells12 0).2:ℝ)/(p12.den:ℝ))).B (p12.toReal.state (((cells12 0).2:ℝ)/(p12.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p12,cells12,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells12 0).1 < (cells12 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p12) hw0 heps hcap (commonSigns12 0) (highSigns12 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns12 0)
   (u:=((cells12 0).1:ℝ)/(p12.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p12.toReal.state (((cells12 0).1:ℝ)/(p12.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(195271590730481499159855590531/500000000000000000000000000000:ℝ)) (by norm_num [p12,cells12,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p12,cells12,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (249713905029120196430750000000000000000000000000000/249741106747722756986072034781433333649228704117073:ℝ) (500000000000000000000000000000/195110691591290436214813832317:ℝ) (1/10:ℝ)) :
 GlobalSource (166380571695786946430750000000000000000000000000000/166407906565634084539019439628426033063955436279739:ℝ) (500000000000000000000000000000/195271590730481499159855590531:ℝ) (1/10:ℝ) := by
 have h9 := source9 hβ hp
 have h10 := source10 hβ h9
 have h11 := source11 hβ h10
 have h12 := source12 hβ h11
 exact h12
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0009_0012
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0013_0016
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0013_0016

theorem source13 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (166380571695786946430750000000000000000000000000000/166407906565634084539019439628426033063955436279739:ℝ) (500000000000000000000000000000/195271590730481499159855590531:ℝ) (1/10:ℝ)) :
 GlobalSource (3992561530757127607199500000000000000000000000000000/3993273102389462717985241515525698101818019138778967:ℝ) (1000000000000000000000000000000/390623798634599869917138937411:ℝ) (1/10:ℝ) := by
 have heps : 0<p13.toReal.eps := by norm_num [p13,Params.toReal]
 have hcap : p13.toReal.cap=1/10 := by norm_num [p13,Params.toReal]
 have hi : GlobalSource (p13.toReal.state (((cells13 0).2:ℝ)/(p13.den:ℝ))).B (p13.toReal.state (((cells13 0).2:ℝ)/(p13.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p13,cells13,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells13 0).1 < (cells13 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p13) hw0 heps hcap (commonSigns13 0) (highSigns13 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns13 0)
   (u:=((cells13 0).1:ℝ)/(p13.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p13.toReal.state (((cells13 0).1:ℝ)/(p13.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(390623798634599869917138937411/1000000000000000000000000000000:ℝ)) (by norm_num [p13,cells13,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p13,cells13,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source14 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3992561530757127607199500000000000000000000000000000/3993273102389462717985241515525698101818019138778967:ℝ) (1000000000000000000000000000000/390623798634599869917138937411:ℝ) (1/10:ℝ)) :
 GlobalSource (997997335203842125015250000000000000000000000000000/998189145020866325217568316195098581478202156726967:ℝ) (500000000000000000000000000000/195352241488345609703291632049:ℝ) (1/10:ℝ) := by
 have heps : 0<p14.toReal.eps := by norm_num [p14,Params.toReal]
 have hcap : p14.toReal.cap=1/10 := by norm_num [p14,Params.toReal]
 have hi : GlobalSource (p14.toReal.state (((cells14 0).2:ℝ)/(p14.den:ℝ))).B (p14.toReal.state (((cells14 0).2:ℝ)/(p14.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p14,cells14,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells14 0).1 < (cells14 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p14) hw0 heps hcap (commonSigns14 0) (highSigns14 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns14 0)
   (u:=((cells14 0).1:ℝ)/(p14.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p14.toReal.state (((cells14 0).1:ℝ)/(p14.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(195352241488345609703291632049/500000000000000000000000000000:ℝ)) (by norm_num [p14,cells14,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p14,cells14,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source15 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (997997335203842125015250000000000000000000000000000/998189145020866325217568316195098581478202156726967:ℝ) (500000000000000000000000000000/195352241488345609703291632049:ℝ) (1/10:ℝ)) :
 GlobalSource (133047238362453646430750000000000000000000000000000/133074673020506232228822011426811964420434102737913:ℝ) (500000000000000000000000000000/195392617275419658120471223977:ℝ) (1/10:ℝ) := by
 have heps : 0<p15.toReal.eps := by norm_num [p15,Params.toReal]
 have hcap : p15.toReal.cap=1/10 := by norm_num [p15,Params.toReal]
 have hi : GlobalSource (p15.toReal.state (((cells15 0).2:ℝ)/(p15.den:ℝ))).B (p15.toReal.state (((cells15 0).2:ℝ)/(p15.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p15,cells15,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells15 0).1 < (cells15 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p15) hw0 heps hcap (commonSigns15 0) (highSigns15 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns15 0)
   (u:=((cells15 0).1:ℝ)/(p15.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p15.toReal.state (((cells15 0).1:ℝ)/(p15.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(195392617275419658120471223977/500000000000000000000000000000:ℝ)) (by norm_num [p15,cells15,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p15,cells15,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source16 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (133047238362453646430750000000000000000000000000000/133074673020506232228822011426811964420434102737913:ℝ) (500000000000000000000000000000/195392617275419658120471223977:ℝ) (1/10:ℝ)) :
 GlobalSource (249427810058240642861500000000000000000000000000000/249482745871424222346616694579569159348819328087937:ℝ) (1000000000000000000000000000000/390866053420751406423907382723:ℝ) (1/10:ℝ) := by
 have heps : 0<p16.toReal.eps := by norm_num [p16,Params.toReal]
 have hcap : p16.toReal.cap=1/10 := by norm_num [p16,Params.toReal]
 have hi : GlobalSource (p16.toReal.state (((cells16 0).2:ℝ)/(p16.den:ℝ))).B (p16.toReal.state (((cells16 0).2:ℝ)/(p16.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p16,cells16,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells16 0).1 < (cells16 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p16) hw0 heps hcap (commonSigns16 0) (highSigns16 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns16 0)
   (u:=((cells16 0).1:ℝ)/(p16.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p16.toReal.state (((cells16 0).1:ℝ)/(p16.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(390866053420751406423907382723/1000000000000000000000000000000:ℝ)) (by norm_num [p16,cells16,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p16,cells16,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (166380571695786946430750000000000000000000000000000/166407906565634084539019439628426033063955436279739:ℝ) (500000000000000000000000000000/195271590730481499159855590531:ℝ) (1/10:ℝ)) :
 GlobalSource (249427810058240642861500000000000000000000000000000/249482745871424222346616694579569159348819328087937:ℝ) (1000000000000000000000000000000/390866053420751406423907382723:ℝ) (1/10:ℝ) := by
 have h13 := source13 hβ hp
 have h14 := source14 hβ h13
 have h15 := source15 hβ h14
 have h16 := source16 hβ h15
 exact h16
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0013_0016
