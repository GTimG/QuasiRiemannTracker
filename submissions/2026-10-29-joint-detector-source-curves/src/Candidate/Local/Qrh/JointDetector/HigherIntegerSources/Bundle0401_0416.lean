/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0401_0404
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0405_0408
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0409_0412
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0413_0416
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0401_0404
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0401_0404

theorem source401 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (124334166666666750000000000000000000000000000/129300856133687203388245773923500987414900889:ℝ) (500000000000000000000000000000/262801276668537104097414900889:ℝ) (1/10:ℝ)) :
 GlobalSource (745505000000000500000000000000000000000000000/775501918972004435116107964306693560032938203:ℝ) (1000000000000000000000000000000/526467158830439879510010979401:ℝ) (1/10:ℝ) := by
 have heps : 0<p401.toReal.eps := by norm_num [p401,Params.toReal]
 have hcap : p401.toReal.cap=1/10 := by norm_num [p401,Params.toReal]
 have hi : GlobalSource (p401.toReal.state (((cells401 0).2:ℝ)/(p401.den:ℝ))).B (p401.toReal.state (((cells401 0).2:ℝ)/(p401.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p401,cells401,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells401 0).1 < (cells401 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p401) hw0 heps hcap (commonSigns401 0) (highSigns401 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns401 0)
   (u:=((cells401 0).1:ℝ)/(p401.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p401.toReal.state (((cells401 0).1:ℝ)/(p401.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(526467158830439879510010979401/1000000000000000000000000000000:ℝ)) (by norm_num [p401,cells401,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p401,cells401,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source402 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (745505000000000500000000000000000000000000000/775501918972004435116107964306693560032938203:ℝ) (1000000000000000000000000000000/526467158830439879510010979401:ℝ) (1/10:ℝ)) :
 GlobalSource (745005000000000500000000000000000000000000000/775199322685576816443378943231636454312465469:ℝ) (1000000000000000000000000000000/527335716064009057254770821823:ℝ) (1/10:ℝ) := by
 have heps : 0<p402.toReal.eps := by norm_num [p402,Params.toReal]
 have hcap : p402.toReal.cap=1/10 := by norm_num [p402,Params.toReal]
 have hi : GlobalSource (p402.toReal.state (((cells402 0).2:ℝ)/(p402.den:ℝ))).B (p402.toReal.state (((cells402 0).2:ℝ)/(p402.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p402,cells402,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells402 0).1 < (cells402 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p402) hw0 heps hcap (commonSigns402 0) (highSigns402 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns402 0)
   (u:=((cells402 0).1:ℝ)/(p402.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p402.toReal.state (((cells402 0).1:ℝ)/(p402.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(527335716064009057254770821823/1000000000000000000000000000000:ℝ)) (by norm_num [p402,cells402,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p402,cells402,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source403 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (745005000000000500000000000000000000000000000/775199322685576816443378943231636454312465469:ℝ) (1000000000000000000000000000000/527335716064009057254770821823:ℝ) (1/10:ℝ)) :
 GlobalSource (248168333333333500000000000000000000000000000/258299116342125846458785231113498452998735057:ℝ) (1000000000000000000000000000000/528208250019683274882998735057:ℝ) (1/10:ℝ) := by
 have heps : 0<p403.toReal.eps := by norm_num [p403,Params.toReal]
 have hcap : p403.toReal.cap=1/10 := by norm_num [p403,Params.toReal]
 have hi : GlobalSource (p403.toReal.state (((cells403 0).2:ℝ)/(p403.den:ℝ))).B (p403.toReal.state (((cells403 0).2:ℝ)/(p403.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p403,cells403,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells403 0).1 < (cells403 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p403) hw0 heps hcap (commonSigns403 0) (highSigns403 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns403 0)
   (u:=((cells403 0).1:ℝ)/(p403.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p403.toReal.state (((cells403 0).1:ℝ)/(p403.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(528208250019683274882998735057/1000000000000000000000000000000:ℝ)) (by norm_num [p403,cells403,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p403,cells403,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source404 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (248168333333333500000000000000000000000000000/258299116342125846458785231113498452998735057:ℝ) (1000000000000000000000000000000/528208250019683274882998735057:ℝ) (1/10:ℝ)) :
 GlobalSource (372002500000000250000000000000000000000000000/387297999544074838329517738626840972745644507:ℝ) (500000000000000000000000000000/264542392945550326634248548169:ℝ) (1/10:ℝ) := by
 have heps : 0<p404.toReal.eps := by norm_num [p404,Params.toReal]
 have hcap : p404.toReal.cap=1/10 := by norm_num [p404,Params.toReal]
 have hi : GlobalSource (p404.toReal.state (((cells404 0).2:ℝ)/(p404.den:ℝ))).B (p404.toReal.state (((cells404 0).2:ℝ)/(p404.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p404,cells404,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells404 0).1 < (cells404 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p404) hw0 heps hcap (commonSigns404 0) (highSigns404 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns404 0)
   (u:=((cells404 0).1:ℝ)/(p404.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p404.toReal.state (((cells404 0).1:ℝ)/(p404.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(264542392945550326634248548169/500000000000000000000000000000:ℝ)) (by norm_num [p404,cells404,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p404,cells404,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem prefix0401 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (124334166666666750000000000000000000000000000/129300856133687203388245773923500987414900889:ℝ) (500000000000000000000000000000/262801276668537104097414900889:ℝ) (1/10:ℝ)) :
 GlobalSource (745505000000000500000000000000000000000000000/775501918972004435116107964306693560032938203:ℝ) (1000000000000000000000000000000/526467158830439879510010979401:ℝ) (1/10:ℝ) := by
 have h401 := source401 hβ hp
 exact h401

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (124334166666666750000000000000000000000000000/129300856133687203388245773923500987414900889:ℝ) (500000000000000000000000000000/262801276668537104097414900889:ℝ) (1/10:ℝ)) :
 GlobalSource (372002500000000250000000000000000000000000000/387297999544074838329517738626840972745644507:ℝ) (500000000000000000000000000000/264542392945550326634248548169:ℝ) (1/10:ℝ) := by
 have h401 := source401 hβ hp
 have h402 := source402 hβ h401
 have h403 := source403 hβ h402
 have h404 := source404 hβ h403
 exact h404
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0401_0404
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0405_0408
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0405_0408

theorem source405 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (372002500000000250000000000000000000000000000/387297999544074838329517738626840972745644507:ℝ) (500000000000000000000000000000/264542392945550326634248548169:ℝ) (1/10:ℝ)) :
 GlobalSource (371752500000000250000000000000000000000000000/387147636987469645290167556060137486884924839:ℝ) (500000000000000000000000000000/264982674542938098698961641613:ℝ) (1/10:ℝ) := by
 have heps : 0<p405.toReal.eps := by norm_num [p405,Params.toReal]
 have hcap : p405.toReal.cap=1/10 := by norm_num [p405,Params.toReal]
 have hi : GlobalSource (p405.toReal.state (((cells405 0).2:ℝ)/(p405.den:ℝ))).B (p405.toReal.state (((cells405 0).2:ℝ)/(p405.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p405,cells405,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells405 0).1 < (cells405 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p405) hw0 heps hcap (commonSigns405 0) (highSigns405 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns405 0)
   (u:=((cells405 0).1:ℝ)/(p405.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p405.toReal.state (((cells405 0).1:ℝ)/(p405.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(264982674542938098698961641613/500000000000000000000000000000:ℝ)) (by norm_num [p405,cells405,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p405,cells405,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source406 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (371752500000000250000000000000000000000000000/387147636987469645290167556060137486884924839:ℝ) (500000000000000000000000000000/264982674542938098698961641613:ℝ) (1/10:ℝ)) :
 GlobalSource (35381190476190500000000000000000000000000000/36856913085771138913720881528427522870852989:ℝ) (1000000000000000000000000000000/530849965227870705430095970923:ℝ) (1/10:ℝ) := by
 have heps : 0<p406.toReal.eps := by norm_num [p406,Params.toReal]
 have hcap : p406.toReal.cap=1/10 := by norm_num [p406,Params.toReal]
 have hi : GlobalSource (p406.toReal.state (((cells406 0).2:ℝ)/(p406.den:ℝ))).B (p406.toReal.state (((cells406 0).2:ℝ)/(p406.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p406,cells406,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells406 0).1 < (cells406 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p406) hw0 heps hcap (commonSigns406 0) (highSigns406 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns406 0)
   (u:=((cells406 0).1:ℝ)/(p406.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p406.toReal.state (((cells406 0).1:ℝ)/(p406.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(530849965227870705430095970923/1000000000000000000000000000000:ℝ)) (by norm_num [p406,cells406,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p406,cells406,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source407 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (35381190476190500000000000000000000000000000/36856913085771138913720881528427522870852989:ℝ) (1000000000000000000000000000000/530849965227870705430095970923:ℝ) (1/10:ℝ)) :
 GlobalSource (46406562500000031250000000000000000000000000/48355981418241404187053011471509927535785999:ℝ) (62500000000000000000000000000/33233666259968044979178595333:ℝ) (1/10:ℝ) := by
 have heps : 0<p407.toReal.eps := by norm_num [p407,Params.toReal]
 have hcap : p407.toReal.cap=1/10 := by norm_num [p407,Params.toReal]
 have hi : GlobalSource (p407.toReal.state (((cells407 0).2:ℝ)/(p407.den:ℝ))).B (p407.toReal.state (((cells407 0).2:ℝ)/(p407.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p407,cells407,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells407 0).1 < (cells407 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p407) hw0 heps hcap (commonSigns407 0) (highSigns407 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns407 0)
   (u:=((cells407 0).1:ℝ)/(p407.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p407.toReal.state (((cells407 0).1:ℝ)/(p407.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(33233666259968044979178595333/62500000000000000000000000000:ℝ)) (by norm_num [p407,cells407,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p407,cells407,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source408 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (46406562500000031250000000000000000000000000/48355981418241404187053011471509927535785999:ℝ) (62500000000000000000000000000/33233666259968044979178595333:ℝ) (1/10:ℝ)) :
 GlobalSource (37100250000000025000000000000000000000000000/38669842939124828340565239584715454693390599:ℝ) (50000000000000000000000000000/26631572997200297821564463533:ℝ) (1/10:ℝ) := by
 have heps : 0<p408.toReal.eps := by norm_num [p408,Params.toReal]
 have hcap : p408.toReal.cap=1/10 := by norm_num [p408,Params.toReal]
 have hi : GlobalSource (p408.toReal.state (((cells408 0).2:ℝ)/(p408.den:ℝ))).B (p408.toReal.state (((cells408 0).2:ℝ)/(p408.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p408,cells408,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells408 0).1 < (cells408 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p408) hw0 heps hcap (commonSigns408 0) (highSigns408 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns408 0)
   (u:=((cells408 0).1:ℝ)/(p408.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p408.toReal.state (((cells408 0).1:ℝ)/(p408.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(26631572997200297821564463533/50000000000000000000000000000:ℝ)) (by norm_num [p408,cells408,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p408,cells408,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (372002500000000250000000000000000000000000000/387297999544074838329517738626840972745644507:ℝ) (500000000000000000000000000000/264542392945550326634248548169:ℝ) (1/10:ℝ)) :
 GlobalSource (37100250000000025000000000000000000000000000/38669842939124828340565239584715454693390599:ℝ) (50000000000000000000000000000/26631572997200297821564463533:ℝ) (1/10:ℝ) := by
 have h405 := source405 hβ hp
 have h406 := source406 hβ h405
 have h407 := source407 hβ h406
 have h408 := source408 hβ h407
 exact h408
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0405_0408
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0409_0412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0409_0412

theorem source409 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (37100250000000025000000000000000000000000000/38669842939124828340565239584715454693390599:ℝ) (50000000000000000000000000000/26631572997200297821564463533:ℝ) (1/10:ℝ)) :
 GlobalSource (82389444444444500000000000000000000000000000/85899849357705929769322665621076219056354207:ℝ) (1000000000000000000000000000000/533528390867926659447169062621:ℝ) (1/10:ℝ) := by
 have heps : 0<p409.toReal.eps := by norm_num [p409,Params.toReal]
 have hcap : p409.toReal.cap=1/10 := by norm_num [p409,Params.toReal]
 have hi : GlobalSource (p409.toReal.state (((cells409 0).2:ℝ)/(p409.den:ℝ))).B (p409.toReal.state (((cells409 0).2:ℝ)/(p409.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p409,cells409,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells409 0).1 < (cells409 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p409) hw0 heps hcap (commonSigns409 0) (highSigns409 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns409 0)
   (u:=((cells409 0).1:ℝ)/(p409.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p409.toReal.state (((cells409 0).1:ℝ)/(p409.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(533528390867926659447169062621/1000000000000000000000000000000:ℝ)) (by norm_num [p409,cells409,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p409,cells409,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source410 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (82389444444444500000000000000000000000000000/85899849357705929769322665621076219056354207:ℝ) (1000000000000000000000000000000/533528390867926659447169062621:ℝ) (1/10:ℝ)) :
 GlobalSource (741005000000000500000000000000000000000000000/772801060159499846252607313272129397338402021:ℝ) (1000000000000000000000000000000/534429479443371329062446134007:ℝ) (1/10:ℝ) := by
 have heps : 0<p410.toReal.eps := by norm_num [p410,Params.toReal]
 have hcap : p410.toReal.cap=1/10 := by norm_num [p410,Params.toReal]
 have hi : GlobalSource (p410.toReal.state (((cells410 0).2:ℝ)/(p410.den:ℝ))).B (p410.toReal.state (((cells410 0).2:ℝ)/(p410.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p410,cells410,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells410 0).1 < (cells410 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p410) hw0 heps hcap (commonSigns410 0) (highSigns410 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns410 0)
   (u:=((cells410 0).1:ℝ)/(p410.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p410.toReal.state (((cells410 0).1:ℝ)/(p410.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(534429479443371329062446134007/1000000000000000000000000000000:ℝ)) (by norm_num [p410,cells410,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p410,cells410,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source411 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (741005000000000500000000000000000000000000000/772801060159499846252607313272129397338402021:ℝ) (1000000000000000000000000000000/534429479443371329062446134007:ℝ) (1/10:ℝ)) :
 GlobalSource (370252500000000250000000000000000000000000000/386252053885459310407840070439513033862819269:ℝ) (500000000000000000000000000000/267667376205247643781287606423:ℝ) (1/10:ℝ) := by
 have heps : 0<p411.toReal.eps := by norm_num [p411,Params.toReal]
 have hcap : p411.toReal.cap=1/10 := by norm_num [p411,Params.toReal]
 have hi : GlobalSource (p411.toReal.state (((cells411 0).2:ℝ)/(p411.den:ℝ))).B (p411.toReal.state (((cells411 0).2:ℝ)/(p411.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p411,cells411,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells411 0).1 < (cells411 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p411) hw0 heps hcap (commonSigns411 0) (highSigns411 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns411 0)
   (u:=((cells411 0).1:ℝ)/(p411.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p411.toReal.state (((cells411 0).1:ℝ)/(p411.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(267667376205247643781287606423/500000000000000000000000000000:ℝ)) (by norm_num [p411,cells411,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p411,cells411,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source412 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (370252500000000250000000000000000000000000000/386252053885459310407840070439513033862819269:ℝ) (500000000000000000000000000000/267667376205247643781287606423:ℝ) (1/10:ℝ)) :
 GlobalSource (246668333333333500000000000000000000000000000/257402596077538439092257471981635850274852697:ℝ) (1000000000000000000000000000000/536244236739938548880274852697:ℝ) (1/10:ℝ) := by
 have heps : 0<p412.toReal.eps := by norm_num [p412,Params.toReal]
 have hcap : p412.toReal.cap=1/10 := by norm_num [p412,Params.toReal]
 have hi : GlobalSource (p412.toReal.state (((cells412 0).2:ℝ)/(p412.den:ℝ))).B (p412.toReal.state (((cells412 0).2:ℝ)/(p412.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p412,cells412,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells412 0).1 < (cells412 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p412) hw0 heps hcap (commonSigns412 0) (highSigns412 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns412 0)
   (u:=((cells412 0).1:ℝ)/(p412.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p412.toReal.state (((cells412 0).1:ℝ)/(p412.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(536244236739938548880274852697/1000000000000000000000000000000:ℝ)) (by norm_num [p412,cells412,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p412,cells412,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (37100250000000025000000000000000000000000000/38669842939124828340565239584715454693390599:ℝ) (50000000000000000000000000000/26631572997200297821564463533:ℝ) (1/10:ℝ)) :
 GlobalSource (246668333333333500000000000000000000000000000/257402596077538439092257471981635850274852697:ℝ) (1000000000000000000000000000000/536244236739938548880274852697:ℝ) (1/10:ℝ) := by
 have h409 := source409 hβ hp
 have h410 := source410 hβ h409
 have h411 := source411 hβ h410
 have h412 := source412 hβ h411
 exact h412
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0409_0412
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0413_0416
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0413_0416

theorem source413 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (246668333333333500000000000000000000000000000/257402596077538439092257471981635850274852697:ℝ) (1000000000000000000000000000000/536244236739938548880274852697:ℝ) (1/10:ℝ)) :
 GlobalSource (369752500000000250000000000000000000000000000/385956051367363751990888394422691375324610053:ℝ) (500000000000000000000000000000/268578979817653734615108203351:ℝ) (1/10:ℝ) := by
 have heps : 0<p413.toReal.eps := by norm_num [p413,Params.toReal]
 have hcap : p413.toReal.cap=1/10 := by norm_num [p413,Params.toReal]
 have hi : GlobalSource (p413.toReal.state (((cells413 0).2:ℝ)/(p413.den:ℝ))).B (p413.toReal.state (((cells413 0).2:ℝ)/(p413.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p413,cells413,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells413 0).1 < (cells413 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p413) hw0 heps hcap (commonSigns413 0) (highSigns413 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns413 0)
   (u:=((cells413 0).1:ℝ)/(p413.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p413.toReal.state (((cells413 0).1:ℝ)/(p413.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(268578979817653734615108203351/500000000000000000000000000000:ℝ)) (by norm_num [p413,cells413,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p413,cells413,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source414 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (369752500000000250000000000000000000000000000/385956051367363751990888394422691375324610053:ℝ) (500000000000000000000000000000/268578979817653734615108203351:ℝ) (1/10:ℝ)) :
 GlobalSource (739005000000000500000000000000000000000000000/771617052478635228467156816988578561890566981:ℝ) (1000000000000000000000000000000/538075948535688663583963522327:ℝ) (1/10:ℝ) := by
 have heps : 0<p414.toReal.eps := by norm_num [p414,Params.toReal]
 have hcap : p414.toReal.cap=1/10 := by norm_num [p414,Params.toReal]
 have hi : GlobalSource (p414.toReal.state (((cells414 0).2:ℝ)/(p414.den:ℝ))).B (p414.toReal.state (((cells414 0).2:ℝ)/(p414.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p414,cells414,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells414 0).1 < (cells414 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p414) hw0 heps hcap (commonSigns414 0) (highSigns414 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns414 0)
   (u:=((cells414 0).1:ℝ)/(p414.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p414.toReal.state (((cells414 0).1:ℝ)/(p414.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(538075948535688663583963522327/1000000000000000000000000000000:ℝ)) (by norm_num [p414,cells414,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p414,cells414,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source415 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (739005000000000500000000000000000000000000000/771617052478635228467156816988578561890566981:ℝ) (1000000000000000000000000000000/538075948535688663583963522327:ℝ) (1/10:ℝ)) :
 GlobalSource (15385520833333343750000000000000000000000000/16069221639105691313094796567640680994636759:ℝ) (62500000000000000000000000000/33687389444887230090994636759:ℝ) (1/10:ℝ) := by
 have heps : 0<p415.toReal.eps := by norm_num [p415,Params.toReal]
 have hcap : p415.toReal.cap=1/10 := by norm_num [p415,Params.toReal]
 have hi : GlobalSource (p415.toReal.state (((cells415 0).2:ℝ)/(p415.den:ℝ))).B (p415.toReal.state (((cells415 0).2:ℝ)/(p415.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p415,cells415,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells415 0).1 < (cells415 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p415) hw0 heps hcap (commonSigns415 0) (highSigns415 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns415 0)
   (u:=((cells415 0).1:ℝ)/(p415.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p415.toReal.state (((cells415 0).1:ℝ)/(p415.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(33687389444887230090994636759/62500000000000000000000000000:ℝ)) (by norm_num [p415,cells415,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p415,cells415,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source416 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (15385520833333343750000000000000000000000000/16069221639105691313094796567640680994636759:ℝ) (62500000000000000000000000000/33687389444887230090994636759:ℝ) (1/10:ℝ)) :
 GlobalSource (738005000000000500000000000000000000000000000/771028862554244528558848245478655966673061137:ℝ) (1000000000000000000000000000000/539924835300548944198891020379:ℝ) (1/10:ℝ) := by
 have heps : 0<p416.toReal.eps := by norm_num [p416,Params.toReal]
 have hcap : p416.toReal.cap=1/10 := by norm_num [p416,Params.toReal]
 have hi : GlobalSource (p416.toReal.state (((cells416 0).2:ℝ)/(p416.den:ℝ))).B (p416.toReal.state (((cells416 0).2:ℝ)/(p416.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p416,cells416,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells416 0).1 < (cells416 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p416) hw0 heps hcap (commonSigns416 0) (highSigns416 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns416 0)
   (u:=((cells416 0).1:ℝ)/(p416.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p416.toReal.state (((cells416 0).1:ℝ)/(p416.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(539924835300548944198891020379/1000000000000000000000000000000:ℝ)) (by norm_num [p416,cells416,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p416,cells416,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (246668333333333500000000000000000000000000000/257402596077538439092257471981635850274852697:ℝ) (1000000000000000000000000000000/536244236739938548880274852697:ℝ) (1/10:ℝ)) :
 GlobalSource (738005000000000500000000000000000000000000000/771028862554244528558848245478655966673061137:ℝ) (1000000000000000000000000000000/539924835300548944198891020379:ℝ) (1/10:ℝ) := by
 have h413 := source413 hβ hp
 have h414 := source414 hβ h413
 have h415 := source415 hβ h414
 have h416 := source416 hβ h415
 exact h416
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0413_0416
