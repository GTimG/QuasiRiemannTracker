/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0049_0052
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0053_0056
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0057_0060
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0061_0064
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0049_0052
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0049_0052

theorem source49 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (41380571695787071430750000000000000000000000000000/41409099964238066912448220112861655861697766663899:ℝ) (500000000000000000000000000000/196744088099051241779541550421:ℝ) (1/10:ℝ)) :
 GlobalSource (3971962692853799750213500000000000000000000000000000/3974761699968641904526345370126179922873227656434577:ℝ) (1000000000000000000000000000000/393571252263842863052048116817:ℝ) (1/10:ℝ) := by
 have heps : 0<p49.toReal.eps := by norm_num [p49,Params.toReal]
 have hcap : p49.toReal.cap=1/10 := by norm_num [p49,Params.toReal]
 have hi : GlobalSource (p49.toReal.state (((cells49 0).2:ℝ)/(p49.den:ℝ))).B (p49.toReal.state (((cells49 0).2:ℝ)/(p49.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p49,cells49,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells49 0).1 < (cells49 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p49) hw0 heps hcap (commonSigns49 0) (highSigns49 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns49 0)
   (u:=((cells49 0).1:ℝ)/(p49.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p49.toReal.state (((cells49 0).1:ℝ)/(p49.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(393571252263842863052048116817/1000000000000000000000000000000:ℝ)) (by norm_num [p49,cells49,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p49,cells49,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source50 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3971962692853799750213500000000000000000000000000000/3974761699968641904526345370126179922873227656434577:ℝ) (1000000000000000000000000000000/393571252263842863052048116817:ℝ) (1/10:ℝ)) :
 GlobalSource (992847625728010160768750000000000000000000000000/993562483714950440749451834221537534921587430557:ℝ) (12500000000000000000000000000/4920679973186539233113864413:ℝ) (1/10:ℝ) := by
 have heps : 0<p50.toReal.eps := by norm_num [p50,Params.toReal]
 have hcap : p50.toReal.cap=1/10 := by norm_num [p50,Params.toReal]
 have hi : GlobalSource (p50.toReal.state (((cells50 0).2:ℝ)/(p50.den:ℝ))).B (p50.toReal.state (((cells50 0).2:ℝ)/(p50.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p50,cells50,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells50 0).1 < (cells50 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p50) hw0 heps hcap (commonSigns50 0) (highSigns50 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns50 0)
   (u:=((cells50 0).1:ℝ)/(p50.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p50.toReal.state (((cells50 0).1:ℝ)/(p50.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(4920679973186539233113864413/12500000000000000000000000000:ℝ)) (by norm_num [p50,cells50,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p50,cells50,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source51 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (992847625728010160768750000000000000000000000000/993562483714950440749451834221537534921587430557:ℝ) (12500000000000000000000000000/4920679973186539233113864413:ℝ) (1/10:ℝ)) :
 GlobalSource (330901526080856794661375000000000000000000000000000/331144858433771523575833416183835719049268597969571:ℝ) (250000000000000000000000000000/98434403259704911625832465027:ℝ) (1/10:ℝ) := by
 have heps : 0<p51.toReal.eps := by norm_num [p51,Params.toReal]
 have hcap : p51.toReal.cap=1/10 := by norm_num [p51,Params.toReal]
 have hi : GlobalSource (p51.toReal.state (((cells51 0).2:ℝ)/(p51.den:ℝ))).B (p51.toReal.state (((cells51 0).2:ℝ)/(p51.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p51,cells51,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells51 0).1 < (cells51 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p51) hw0 heps hcap (commonSigns51 0) (highSigns51 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns51 0)
   (u:=((cells51 0).1:ℝ)/(p51.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p51.toReal.state (((cells51 0).1:ℝ)/(p51.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(98434403259704911625832465027/250000000000000000000000000000:ℝ)) (by norm_num [p51,cells51,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p51,cells51,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source52 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (330901526080856794661375000000000000000000000000000/331144858433771523575833416183835719049268597969571:ℝ) (250000000000000000000000000000/98434403259704911625832465027:ℝ) (1/10:ℝ)) :
 GlobalSource (70897252196937900514250000000000000000000000000000/70950478553037922917447483645747815113793608215357:ℝ) (500000000000000000000000000000/196910448941559598126767229967:ℝ) (1/10:ℝ) := by
 have heps : 0<p52.toReal.eps := by norm_num [p52,Params.toReal]
 have hcap : p52.toReal.cap=1/10 := by norm_num [p52,Params.toReal]
 have hi : GlobalSource (p52.toReal.state (((cells52 0).2:ℝ)/(p52.den:ℝ))).B (p52.toReal.state (((cells52 0).2:ℝ)/(p52.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p52,cells52,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells52 0).1 < (cells52 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p52) hw0 heps hcap (commonSigns52 0) (highSigns52 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns52 0)
   (u:=((cells52 0).1:ℝ)/(p52.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p52.toReal.state (((cells52 0).1:ℝ)/(p52.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(196910448941559598126767229967/500000000000000000000000000000:ℝ)) (by norm_num [p52,cells52,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p52,cells52,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (41380571695787071430750000000000000000000000000000/41409099964238066912448220112861655861697766663899:ℝ) (500000000000000000000000000000/196744088099051241779541550421:ℝ) (1/10:ℝ)) :
 GlobalSource (70897252196937900514250000000000000000000000000000/70950478553037922917447483645747815113793608215357:ℝ) (500000000000000000000000000000/196910448941559598126767229967:ℝ) (1/10:ℝ) := by
 have h49 := source49 hβ hp
 have h50 := source50 hβ h49
 have h51 := source51 hβ h50
 have h52 := source52 hβ h51
 exact h52
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0049_0052
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0053_0056
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0053_0056

theorem source53 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (70897252196937900514250000000000000000000000000000/70950478553037922917447483645747815113793608215357:ℝ) (500000000000000000000000000000/196910448941559598126767229967:ℝ) (1/10:ℝ)) :
 GlobalSource (396967393308676332165950000000000000000000000000000/397271542811969782562609278497923846645292995920029:ℝ) (100000000000000000000000000000/39390425245551922999077824697:ℝ) (1/10:ℝ) := by
 have heps : 0<p53.toReal.eps := by norm_num [p53,Params.toReal]
 have hcap : p53.toReal.cap=1/10 := by norm_num [p53,Params.toReal]
 have hi : GlobalSource (p53.toReal.state (((cells53 0).2:ℝ)/(p53.den:ℝ))).B (p53.toReal.state (((cells53 0).2:ℝ)/(p53.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p53,cells53,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells53 0).1 < (cells53 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p53) hw0 heps hcap (commonSigns53 0) (highSigns53 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns53 0)
   (u:=((cells53 0).1:ℝ)/(p53.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p53.toReal.state (((cells53 0).1:ℝ)/(p53.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(39390425245551922999077824697/100000000000000000000000000000:ℝ)) (by norm_num [p53,cells53,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p53,cells53,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source54 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (396967393308676332165950000000000000000000000000000/397271542811969782562609278497923846645292995920029:ℝ) (100000000000000000000000000000/39390425245551922999077824697:ℝ) (1/10:ℝ)) :
 GlobalSource (661516957190834035753500000000000000000000000000000/662034031436577986737442278015392795371356663419809:ℝ) (1000000000000000000000000000000/393987676823827981601978900729:ℝ) (1/10:ℝ) := by
 have heps : 0<p54.toReal.eps := by norm_num [p54,Params.toReal]
 have hcap : p54.toReal.cap=1/10 := by norm_num [p54,Params.toReal]
 have hi : GlobalSource (p54.toReal.state (((cells54 0).2:ℝ)/(p54.den:ℝ))).B (p54.toReal.state (((cells54 0).2:ℝ)/(p54.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p54,cells54,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells54 0).1 < (cells54 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p54) hw0 heps hcap (commonSigns54 0) (highSigns54 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns54 0)
   (u:=((cells54 0).1:ℝ)/(p54.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p54.toReal.state (((cells54 0).1:ℝ)/(p54.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(393987676823827981601978900729/1000000000000000000000000000000:ℝ)) (by norm_num [p54,cells54,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p54,cells54,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source55 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (661516957190834035753500000000000000000000000000000/662034031436577986737442278015392795371356663419809:ℝ) (1000000000000000000000000000000/393987676823827981601978900729:ℝ) (1/10:ℝ)) :
 GlobalSource (158741182128129804295300000000000000000000000000000/158867723217404329428488216120540009010217702766991:ℝ) (200000000000000000000000000000/78814234211192927291891725949:ℝ) (1/10:ℝ) := by
 have heps : 0<p55.toReal.eps := by norm_num [p55,Params.toReal]
 have hcap : p55.toReal.cap=1/10 := by norm_num [p55,Params.toReal]
 have hi : GlobalSource (p55.toReal.state (((cells55 0).2:ℝ)/(p55.den:ℝ))).B (p55.toReal.state (((cells55 0).2:ℝ)/(p55.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p55,cells55,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells55 0).1 < (cells55 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p55) hw0 heps hcap (commonSigns55 0) (highSigns55 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns55 0)
   (u:=((cells55 0).1:ℝ)/(p55.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p55.toReal.state (((cells55 0).1:ℝ)/(p55.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(78814234211192927291891725949/200000000000000000000000000000:ℝ)) (by norm_num [p55,cells55,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p55,cells55,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source56 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (158741182128129804295300000000000000000000000000000/158867723217404329428488216120540009010217702766991:ℝ) (200000000000000000000000000000/78814234211192927291891725949:ℝ) (1/10:ℝ)) :
 GlobalSource (495994670407685750030500000000000000000000000000000/496397762941559975571586304037324358801645985652489:ℝ) (1000000000000000000000000000000/394154735219959491470828458683:ℝ) (1/10:ℝ) := by
 have heps : 0<p56.toReal.eps := by norm_num [p56,Params.toReal]
 have hcap : p56.toReal.cap=1/10 := by norm_num [p56,Params.toReal]
 have hi : GlobalSource (p56.toReal.state (((cells56 0).2:ℝ)/(p56.den:ℝ))).B (p56.toReal.state (((cells56 0).2:ℝ)/(p56.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p56,cells56,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells56 0).1 < (cells56 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p56) hw0 heps hcap (commonSigns56 0) (highSigns56 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns56 0)
   (u:=((cells56 0).1:ℝ)/(p56.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p56.toReal.state (((cells56 0).1:ℝ)/(p56.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(394154735219959491470828458683/1000000000000000000000000000000:ℝ)) (by norm_num [p56,cells56,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p56,cells56,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (70897252196937900514250000000000000000000000000000/70950478553037922917447483645747815113793608215357:ℝ) (500000000000000000000000000000/196910448941559598126767229967:ℝ) (1/10:ℝ)) :
 GlobalSource (495994670407685750030500000000000000000000000000000/496397762941559975571586304037324358801645985652489:ℝ) (1000000000000000000000000000000/394154735219959491470828458683:ℝ) (1/10:ℝ) := by
 have h53 := source53 hβ hp
 have h54 := source54 hβ h53
 have h55 := source55 hβ h54
 have h56 := source56 hβ h55
 exact h56
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0053_0056
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0057_0060
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0057_0060

theorem source57 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (495994670407685750030500000000000000000000000000000/496397762941559975571586304037324358801645985652489:ℝ) (1000000000000000000000000000000/394154735219959491470828458683:ℝ) (1/10:ℝ)) :
 GlobalSource (1322461724439908964368500000000000000000000000000000/1323557085959210044544626783677519436184903458142519:ℝ) (1000000000000000000000000000000/394238369383954115498582290429:ℝ) (1/10:ℝ) := by
 have heps : 0<p57.toReal.eps := by norm_num [p57,Params.toReal]
 have hcap : p57.toReal.cap=1/10 := by norm_num [p57,Params.toReal]
 have hi : GlobalSource (p57.toReal.state (((cells57 0).2:ℝ)/(p57.den:ℝ))).B (p57.toReal.state (((cells57 0).2:ℝ)/(p57.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p57,cells57,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells57 0).1 < (cells57 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p57) hw0 heps hcap (commonSigns57 0) (highSigns57 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns57 0)
   (u:=((cells57 0).1:ℝ)/(p57.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p57.toReal.state (((cells57 0).1:ℝ)/(p57.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(394238369383954115498582290429/1000000000000000000000000000000:ℝ)) (by norm_num [p57,cells57,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p57,cells57,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source58 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1322461724439908964368500000000000000000000000000000/1323557085959210044544626783677519436184903458142519:ℝ) (1000000000000000000000000000000/394238369383954115498582290429:ℝ) (1/10:ℝ)) :
 GlobalSource (991703245844491946491750000000000000000000000000000/992540135859198227913471133413984082633579495991811:ℝ) (500000000000000000000000000000/197161036808100755063241626911:ℝ) (1/10:ℝ) := by
 have heps : 0<p58.toReal.eps := by norm_num [p58,Params.toReal]
 have hcap : p58.toReal.cap=1/10 := by norm_num [p58,Params.toReal]
 have hi : GlobalSource (p58.toReal.state (((cells58 0).2:ℝ)/(p58.den:ℝ))).B (p58.toReal.state (((cells58 0).2:ℝ)/(p58.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p58,cells58,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells58 0).1 < (cells58 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p58) hw0 heps hcap (commonSigns58 0) (highSigns58 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns58 0)
   (u:=((cells58 0).1:ℝ)/(p58.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p58.toReal.state (((cells58 0).1:ℝ)/(p58.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(197161036808100755063241626911/500000000000000000000000000000:ℝ)) (by norm_num [p58,cells58,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p58,cells58,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source59 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (991703245844491946491750000000000000000000000000000/992540135859198227913471133413984082633579495991811:ℝ) (500000000000000000000000000000/197161036808100755063241626911:ℝ) (1/10:ℝ)) :
 GlobalSource (566605827633744096975500000000000000000000000000000/567092851453769674094522933553041170400828255765511:ℝ) (1000000000000000000000000000000/394405847985066270810018231187:ℝ) (1/10:ℝ) := by
 have heps : 0<p59.toReal.eps := by norm_num [p59,Params.toReal]
 have hcap : p59.toReal.cap=1/10 := by norm_num [p59,Params.toReal]
 have hi : GlobalSource (p59.toReal.state (((cells59 0).2:ℝ)/(p59.den:ℝ))).B (p59.toReal.state (((cells59 0).2:ℝ)/(p59.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p59,cells59,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells59 0).1 < (cells59 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p59) hw0 heps hcap (commonSigns59 0) (highSigns59 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns59 0)
   (u:=((cells59 0).1:ℝ)/(p59.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p59.toReal.state (((cells59 0).1:ℝ)/(p59.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(394405847985066270810018231187/1000000000000000000000000000000:ℝ)) (by norm_num [p59,cells59,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p59,cells59,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source60 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (566605827633744096975500000000000000000000000000000/567092851453769674094522933553041170400828255765511:ℝ) (1000000000000000000000000000000/394405847985066270810018231187:ℝ) (1/10:ℝ)) :
 GlobalSource (1321889534498149857230000000000000000000000000000/1323046502687673245092825752682976145105339646989:ℝ) (20000000000000000000000000000/7889793851180494967495217381:ℝ) (1/10:ℝ) := by
 have heps : 0<p60.toReal.eps := by norm_num [p60,Params.toReal]
 have hcap : p60.toReal.cap=1/10 := by norm_num [p60,Params.toReal]
 have hi : GlobalSource (p60.toReal.state (((cells60 0).2:ℝ)/(p60.den:ℝ))).B (p60.toReal.state (((cells60 0).2:ℝ)/(p60.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p60,cells60,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells60 0).1 < (cells60 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p60) hw0 heps hcap (commonSigns60 0) (highSigns60 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns60 0)
   (u:=((cells60 0).1:ℝ)/(p60.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p60.toReal.state (((cells60 0).1:ℝ)/(p60.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(7889793851180494967495217381/20000000000000000000000000000:ℝ)) (by norm_num [p60,cells60,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p60,cells60,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (495994670407685750030500000000000000000000000000000/496397762941559975571586304037324358801645985652489:ℝ) (1000000000000000000000000000000/394154735219959491470828458683:ℝ) (1/10:ℝ)) :
 GlobalSource (1321889534498149857230000000000000000000000000000/1323046502687673245092825752682976145105339646989:ℝ) (20000000000000000000000000000/7889793851180494967495217381:ℝ) (1/10:ℝ) := by
 have h57 := source57 hβ hp
 have h58 := source58 hβ h57
 have h59 := source59 hβ h58
 have h60 := source60 hβ h59
 exact h60
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0057_0060
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0061_0064
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0061_0064

theorem source61 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1321889534498149857230000000000000000000000000000/1323046502687673245092825752682976145105339646989:ℝ) (20000000000000000000000000000/7889793851180494967495217381:ℝ) (1/10:ℝ)) :
 GlobalSource (1982548206776345232275750000000000000000000000000000/1984314593531739726218367327153562688477094962765541:ℝ) (500000000000000000000000000000/197286803703332605442494942649:ℝ) (1/10:ℝ) := by
 have heps : 0<p61.toReal.eps := by norm_num [p61,Params.toReal]
 have hcap : p61.toReal.cap=1/10 := by norm_num [p61,Params.toReal]
 have hi : GlobalSource (p61.toReal.state (((cells61 0).2:ℝ)/(p61.den:ℝ))).B (p61.toReal.state (((cells61 0).2:ℝ)/(p61.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p61,cells61,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells61 0).1 < (cells61 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p61) hw0 heps hcap (commonSigns61 0) (highSigns61 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns61 0)
   (u:=((cells61 0).1:ℝ)/(p61.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p61.toReal.state (((cells61 0).1:ℝ)/(p61.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(197286803703332605442494942649/500000000000000000000000000000:ℝ)) (by norm_num [p61,cells61,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p61,cells61,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source62 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1982548206776345232275750000000000000000000000000000/1984314593531739726218367327153562688477094962765541:ℝ) (500000000000000000000000000000/197286803703332605442494942649:ℝ) (1/10:ℝ)) :
 GlobalSource (495565527951366419676625000000000000000000000000000/496014874643092797693675821710360021982508170958123:ℝ) (250000000000000000000000000000/98664398149172001472186345557:ℝ) (1/10:ℝ) := by
 have heps : 0<p62.toReal.eps := by norm_num [p62,Params.toReal]
 have hcap : p62.toReal.cap=1/10 := by norm_num [p62,Params.toReal]
 have hi : GlobalSource (p62.toReal.state (((cells62 0).2:ℝ)/(p62.den:ℝ))).B (p62.toReal.state (((cells62 0).2:ℝ)/(p62.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p62,cells62,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells62 0).1 < (cells62 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p62) hw0 heps hcap (commonSigns62 0) (highSigns62 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns62 0)
   (u:=((cells62 0).1:ℝ)/(p62.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p62.toReal.state (((cells62 0).1:ℝ)/(p62.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(98664398149172001472186345557/250000000000000000000000000000:ℝ)) (by norm_num [p62,cells62,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p62,cells62,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source63 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (495565527951366419676625000000000000000000000000000/496014874643092797693675821710360021982508170958123:ℝ) (250000000000000000000000000000/98664398149172001472186345557:ℝ) (1/10:ℝ)) :
 GlobalSource (1321317344556390750091500000000000000000000000000000/1322536312757989588317424492719049625450850906800539:ℝ) (1000000000000000000000000000000/394741648197905723022530392511:ℝ) (1/10:ℝ) := by
 have heps : 0<p63.toReal.eps := by norm_num [p63,Params.toReal]
 have hcap : p63.toReal.cap=1/10 := by norm_num [p63,Params.toReal]
 have hi : GlobalSource (p63.toReal.state (((cells63 0).2:ℝ)/(p63.den:ℝ))).B (p63.toReal.state (((cells63 0).2:ℝ)/(p63.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p63,cells63,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells63 0).1 < (cells63 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p63) hw0 heps hcap (commonSigns63 0) (highSigns63 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns63 0)
   (u:=((cells63 0).1:ℝ)/(p63.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p63.toReal.state (((cells63 0).1:ℝ)/(p63.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(394741648197905723022530392511/1000000000000000000000000000000:ℝ)) (by norm_num [p63,cells63,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p63,cells63,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source64 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1321317344556390750091500000000000000000000000000000/1322536312757989588317424492719049625450850906800539:ℝ) (1000000000000000000000000000000/394741648197905723022530392511:ℝ) (1/10:ℝ)) :
 GlobalSource (30963905029120415180750000000000000000000000000000/30992961018894556927328612637507048370377852346167:ℝ) (250000000000000000000000000000/98706443569810839246098004009:ℝ) (1/10:ℝ) := by
 have heps : 0<p64.toReal.eps := by norm_num [p64,Params.toReal]
 have hcap : p64.toReal.cap=1/10 := by norm_num [p64,Params.toReal]
 have hi : GlobalSource (p64.toReal.state (((cells64 0).2:ℝ)/(p64.den:ℝ))).B (p64.toReal.state (((cells64 0).2:ℝ)/(p64.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p64,cells64,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells64 0).1 < (cells64 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p64) hw0 heps hcap (commonSigns64 0) (highSigns64 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns64 0)
   (u:=((cells64 0).1:ℝ)/(p64.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p64.toReal.state (((cells64 0).1:ℝ)/(p64.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(98706443569810839246098004009/250000000000000000000000000000:ℝ)) (by norm_num [p64,cells64,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p64,cells64,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1321889534498149857230000000000000000000000000000/1323046502687673245092825752682976145105339646989:ℝ) (20000000000000000000000000000/7889793851180494967495217381:ℝ) (1/10:ℝ)) :
 GlobalSource (30963905029120415180750000000000000000000000000000/30992961018894556927328612637507048370377852346167:ℝ) (250000000000000000000000000000/98706443569810839246098004009:ℝ) (1/10:ℝ) := by
 have h61 := source61 hβ hp
 have h62 := source62 hβ h61
 have h63 := source63 hβ h62
 have h64 := source64 hβ h63
 exact h64
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0061_0064
