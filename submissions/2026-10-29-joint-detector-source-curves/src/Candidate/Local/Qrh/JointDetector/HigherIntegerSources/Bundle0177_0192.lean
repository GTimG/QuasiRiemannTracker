/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0177_0180
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0181_0184
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0185_0188
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0189_0192
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0177_0180
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0177_0180

theorem source177 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1523161941504059821728125000000000000000000000000/1527659973876890420832012479858899452870647470611:ℝ) (6250000000000000000000000000/2529445450175200403805867079:ℝ) (1/10:ℝ)) :
 GlobalSource (1299574126769544678828500000000000000000000000000000/1303438081069619196813553073941717598582306565391577:ℝ) (1000000000000000000000000000000/404803835295409915899835002187:ℝ) (1/10:ℝ) := by
 have heps : 0<p177.toReal.eps := by norm_num [p177,Params.toReal]
 have hcap : p177.toReal.cap=1/10 := by norm_num [p177,Params.toReal]
 have hi : GlobalSource (p177.toReal.state (((cells177 0).2:ℝ)/(p177.den:ℝ))).B (p177.toReal.state (((cells177 0).2:ℝ)/(p177.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p177,cells177,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells177 0).1 < (cells177 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p177) hw0 heps hcap (commonSigns177 0) (highSigns177 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns177 0)
   (u:=((cells177 0).1:ℝ)/(p177.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p177.toReal.state (((cells177 0).1:ℝ)/(p177.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(404803835295409915899835002187/1000000000000000000000000000000:ℝ)) (by norm_num [p177,cells177,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p177,cells177,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source178 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1299574126769544678828500000000000000000000000000000/1303438081069619196813553073941717598582306565391577:ℝ) (1000000000000000000000000000000/404803835295409915899835002187:ℝ) (1/10:ℝ)) :
 GlobalSource (974537547591718732336750000000000000000000000000000/977454770431131862249598250783724845631353705861501:ℝ) (500000000000000000000000000000/202448238840724728667179053061:ℝ) (1/10:ℝ) := by
 have heps : 0<p178.toReal.eps := by norm_num [p178,Params.toReal]
 have hcap : p178.toReal.cap=1/10 := by norm_num [p178,Params.toReal]
 have hi : GlobalSource (p178.toReal.state (((cells178 0).2:ℝ)/(p178.den:ℝ))).B (p178.toReal.state (((cells178 0).2:ℝ)/(p178.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p178,cells178,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells178 0).1 < (cells178 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p178) hw0 heps hcap (commonSigns178 0) (highSigns178 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns178 0)
   (u:=((cells178 0).1:ℝ)/(p178.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p178.toReal.state (((cells178 0).1:ℝ)/(p178.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(202448238840724728667179053061/500000000000000000000000000000:ℝ)) (by norm_num [p178,cells178,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p178,cells178,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source179 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (974537547591718732336750000000000000000000000000000/977454770431131862249598250783724845631353705861501:ℝ) (500000000000000000000000000000/202448238840724728667179053061:ℝ) (1/10:ℝ)) :
 GlobalSource (3897578000425115822208500000000000000000000000000000/3909324048658596136996255392784156834375259662137171:ℝ) (1000000000000000000000000000000/404989199269195426451148267921:ℝ) (1/10:ℝ) := by
 have heps : 0<p179.toReal.eps := by norm_num [p179,Params.toReal]
 have hcap : p179.toReal.cap=1/10 := by norm_num [p179,Params.toReal]
 have hi : GlobalSource (p179.toReal.state (((cells179 0).2:ℝ)/(p179.den:ℝ))).B (p179.toReal.state (((cells179 0).2:ℝ)/(p179.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p179,cells179,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells179 0).1 < (cells179 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p179) hw0 heps hcap (commonSigns179 0) (highSigns179 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns179 0)
   (u:=((cells179 0).1:ℝ)/(p179.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p179.toReal.state (((cells179 0).1:ℝ)/(p179.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(404989199269195426451148267921/1000000000000000000000000000000:ℝ)) (by norm_num [p179,cells179,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p179,cells179,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source180 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3897578000425115822208500000000000000000000000000000/3909324048658596136996255392784156834375259662137171:ℝ) (1000000000000000000000000000000/404989199269195426451148267921:ℝ) (1/10:ℝ)) :
 GlobalSource (21650032280463092861500000000000000000000000000000/21715717466655360639452618838659941662845654308411:ℝ) (1000000000000000000000000000000/405082000141826722826660465619:ℝ) (1/10:ℝ) := by
 have heps : 0<p180.toReal.eps := by norm_num [p180,Params.toReal]
 have hcap : p180.toReal.cap=1/10 := by norm_num [p180,Params.toReal]
 have hi : GlobalSource (p180.toReal.state (((cells180 0).2:ℝ)/(p180.den:ℝ))).B (p180.toReal.state (((cells180 0).2:ℝ)/(p180.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p180,cells180,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells180 0).1 < (cells180 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p180) hw0 heps hcap (commonSigns180 0) (highSigns180 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns180 0)
   (u:=((cells180 0).1:ℝ)/(p180.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p180.toReal.state (((cells180 0).1:ℝ)/(p180.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(405082000141826722826660465619/1000000000000000000000000000000:ℝ)) (by norm_num [p180,cells180,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p180,cells180,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1523161941504059821728125000000000000000000000000/1527659973876890420832012479858899452870647470611:ℝ) (6250000000000000000000000000/2529445450175200403805867079:ℝ) (1/10:ℝ)) :
 GlobalSource (21650032280463092861500000000000000000000000000000/21715717466655360639452618838659941662845654308411:ℝ) (1000000000000000000000000000000/405082000141826722826660465619:ℝ) (1/10:ℝ) := by
 have h177 := source177 hβ hp
 have h178 := source178 hβ h177
 have h179 := source179 hβ h178
 have h180 := source180 hβ h179
 exact h180
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0177_0180
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0181_0184
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0181_0184

theorem source181 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (21650032280463092861500000000000000000000000000000/21715717466655360639452618838659941662845654308411:ℝ) (1000000000000000000000000000000/405082000141826722826660465619:ℝ) (1/10:ℝ)) :
 GlobalSource (3896433620541597607931500000000000000000000000000000/3908334367729688991670670402538063825102414182322783:ℝ) (1000000000000000000000000000000/405174880382656623085642156947:ℝ) (1/10:ℝ) := by
 have heps : 0<p181.toReal.eps := by norm_num [p181,Params.toReal]
 have hcap : p181.toReal.cap=1/10 := by norm_num [p181,Params.toReal]
 have hi : GlobalSource (p181.toReal.state (((cells181 0).2:ℝ)/(p181.den:ℝ))).B (p181.toReal.state (((cells181 0).2:ℝ)/(p181.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p181,cells181,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells181 0).1 < (cells181 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p181) hw0 heps hcap (commonSigns181 0) (highSigns181 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns181 0)
   (u:=((cells181 0).1:ℝ)/(p181.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p181.toReal.state (((cells181 0).1:ℝ)/(p181.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(405174880382656623085642156947/1000000000000000000000000000000:ℝ)) (by norm_num [p181,cells181,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p181,cells181,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source182 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3896433620541597607931500000000000000000000000000000/3908334367729688991670670402538063825102414182322783:ℝ) (1000000000000000000000000000000/405174880382656623085642156947:ℝ) (1/10:ℝ)) :
 GlobalSource (973965357649959625198250000000000000000000000000000/976959929960244323643516389781278588610550749571563:ℝ) (500000000000000000000000000000/202633920037566498227405401297:ℝ) (1/10:ℝ) := by
 have heps : 0<p182.toReal.eps := by norm_num [p182,Params.toReal]
 have hcap : p182.toReal.cap=1/10 := by norm_num [p182,Params.toReal]
 have hi : GlobalSource (p182.toReal.state (((cells182 0).2:ℝ)/(p182.den:ℝ))).B (p182.toReal.state (((cells182 0).2:ℝ)/(p182.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p182,cells182,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells182 0).1 < (cells182 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p182) hw0 heps hcap (commonSigns182 0) (highSigns182 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns182 0)
   (u:=((cells182 0).1:ℝ)/(p182.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p182.toReal.state (((cells182 0).1:ℝ)/(p182.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(202633920037566498227405401297/500000000000000000000000000000:ℝ)) (by norm_num [p182,cells182,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p182,cells182,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source183 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (973965357649959625198250000000000000000000000000000/976959929960244323643516389781278588610550749571563:ℝ) (500000000000000000000000000000/202633920037566498227405401297:ℝ) (1/10:ℝ)) :
 GlobalSource (649214873443013232275750000000000000000000000000000/651224200053198707279807946512675189658667566008989:ℝ) (500000000000000000000000000000/202680439651419260422778421521:ℝ) (1/10:ℝ) := by
 have heps : 0<p183.toReal.eps := by norm_num [p183,Params.toReal]
 have hcap : p183.toReal.cap=1/10 := by norm_num [p183,Params.toReal]
 have hi : GlobalSource (p183.toReal.state (((cells183 0).2:ℝ)/(p183.den:ℝ))).B (p183.toReal.state (((cells183 0).2:ℝ)/(p183.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p183,cells183,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells183 0).1 < (cells183 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p183) hw0 heps hcap (commonSigns183 0) (highSigns183 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns183 0)
   (u:=((cells183 0).1:ℝ)/(p183.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p183.toReal.state (((cells183 0).1:ℝ)/(p183.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(202680439651419260422778421521/500000000000000000000000000000:ℝ)) (by norm_num [p183,cells183,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p183,cells183,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source184 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (649214873443013232275750000000000000000000000000000/651224200053198707279807946512675189658667566008989:ℝ) (500000000000000000000000000000/202680439651419260422778421521:ℝ) (1/10:ℝ)) :
 GlobalSource (121709907834885008953625000000000000000000000000000/122089087785995297616970204674374344014200519925369:ℝ) (250000000000000000000000000000/101363499537372724860294120187:ℝ) (1/10:ℝ) := by
 have heps : 0<p184.toReal.eps := by norm_num [p184,Params.toReal]
 have hcap : p184.toReal.cap=1/10 := by norm_num [p184,Params.toReal]
 have hi : GlobalSource (p184.toReal.state (((cells184 0).2:ℝ)/(p184.den:ℝ))).B (p184.toReal.state (((cells184 0).2:ℝ)/(p184.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p184,cells184,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells184 0).1 < (cells184 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p184) hw0 heps hcap (commonSigns184 0) (highSigns184 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns184 0)
   (u:=((cells184 0).1:ℝ)/(p184.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p184.toReal.state (((cells184 0).1:ℝ)/(p184.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(101363499537372724860294120187/250000000000000000000000000000:ℝ)) (by norm_num [p184,cells184,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p184,cells184,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (21650032280463092861500000000000000000000000000000/21715717466655360639452618838659941662845654308411:ℝ) (1000000000000000000000000000000/405082000141826722826660465619:ℝ) (1/10:ℝ)) :
 GlobalSource (121709907834885008953625000000000000000000000000000/122089087785995297616970204674374344014200519925369:ℝ) (250000000000000000000000000000/101363499537372724860294120187:ℝ) (1/10:ℝ) := by
 have h181 := source181 hβ hp
 have h182 := source182 hβ h181
 have h183 := source183 hβ h182
 have h184 := source184 hβ h183
 exact h184
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0181_0184
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0185_0188
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0185_0188

theorem source185 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (121709907834885008953625000000000000000000000000000/122089087785995297616970204674374344014200519925369:ℝ) (250000000000000000000000000000/101363499537372724860294120187:ℝ) (1/10:ℝ)) :
 GlobalSource (7789148006461761019462750000000000000000000000000000/7813454462827894054089185017307156489306466784693503:ℝ) (500000000000000000000000000000/202738645155718991189416691151:ℝ) (1/10:ℝ) := by
 have heps : 0<p185.toReal.eps := by norm_num [p185,Params.toReal]
 have hcap : p185.toReal.cap=1/10 := by norm_num [p185,Params.toReal]
 have hi : GlobalSource (p185.toReal.state (((cells185 0).2:ℝ)/(p185.den:ℝ))).B (p185.toReal.state (((cells185 0).2:ℝ)/(p185.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p185,cells185,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells185 0).1 < (cells185 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p185) hw0 heps hcap (commonSigns185 0) (highSigns185 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns185 0)
   (u:=((cells185 0).1:ℝ)/(p185.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p185.toReal.state (((cells185 0).1:ℝ)/(p185.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(202738645155718991189416691151/500000000000000000000000000000:ℝ)) (by norm_num [p185,cells185,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p185,cells185,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source186 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (7789148006461761019462750000000000000000000000000000/7813454462827894054089185017307156489306466784693503:ℝ) (500000000000000000000000000000/202738645155718991189416691151:ℝ) (1/10:ℝ)) :
 GlobalSource (54184382323313539079500000000000000000000000000000/54353606198997620294903859461765578777930232653533:ℝ) (1000000000000000000000000000000/405488938260855476797168296049:ℝ) (1/10:ℝ) := by
 have heps : 0<p186.toReal.eps := by norm_num [p186,Params.toReal]
 have hcap : p186.toReal.cap=1/10 := by norm_num [p186,Params.toReal]
 have hi : GlobalSource (p186.toReal.state (((cells186 0).2:ℝ)/(p186.den:ℝ))).B (p186.toReal.state (((cells186 0).2:ℝ)/(p186.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p186,cells186,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells186 0).1 < (cells186 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p186) hw0 heps hcap (commonSigns186 0) (highSigns186 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns186 0)
   (u:=((cells186 0).1:ℝ)/(p186.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p186.toReal.state (((cells186 0).1:ℝ)/(p186.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(405488938260855476797168296049/1000000000000000000000000000000:ℝ)) (by norm_num [p186,cells186,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p186,cells186,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source187 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (54184382323313539079500000000000000000000000000000/54353606198997620294903859461765578777930232653533:ℝ) (1000000000000000000000000000000/405488938260855476797168296049:ℝ) (1/10:ℝ)) :
 GlobalSource (415411690512264602585705000000000000000000000000000/416709333269443267219908256584753093432374265954579:ℝ) (10000000000000000000000000000/4054918504428671851353596973:ℝ) (1/10:ℝ) := by
 have heps : 0<p187.toReal.eps := by norm_num [p187,Params.toReal]
 have hcap : p187.toReal.cap=1/10 := by norm_num [p187,Params.toReal]
 have hi : GlobalSource (p187.toReal.state (((cells187 0).2:ℝ)/(p187.den:ℝ))).B (p187.toReal.state (((cells187 0).2:ℝ)/(p187.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p187,cells187,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells187 0).1 < (cells187 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p187) hw0 heps hcap (commonSigns187 0) (highSigns187 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns187 0)
   (u:=((cells187 0).1:ℝ)/(p187.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p187.toReal.state (((cells187 0).1:ℝ)/(p187.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(4054918504428671851353596973/10000000000000000000000000000:ℝ)) (by norm_num [p187,cells187,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p187,cells187,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source188 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (415411690512264602585705000000000000000000000000000/416709333269443267219908256584753093432374265954579:ℝ) (10000000000000000000000000000/4054918504428671851353596973:ℝ) (1/10:ℝ)) :
 GlobalSource (996987485039493287098553500000000000000000000000000000/1000101905572058222924782792253814639441190247180261997:ℝ) (1000000000000000000000000000000/405492214471093694022618440757:ℝ) (1/10:ℝ) := by
 have heps : 0<p188.toReal.eps := by norm_num [p188,Params.toReal]
 have hcap : p188.toReal.cap=1/10 := by norm_num [p188,Params.toReal]
 have hi : GlobalSource (p188.toReal.state (((cells188 0).2:ℝ)/(p188.den:ℝ))).B (p188.toReal.state (((cells188 0).2:ℝ)/(p188.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p188,cells188,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells188 0).1 < (cells188 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p188) hw0 heps hcap (commonSigns188 0) (highSigns188 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns188 0)
   (u:=((cells188 0).1:ℝ)/(p188.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p188.toReal.state (((cells188 0).1:ℝ)/(p188.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(405492214471093694022618440757/1000000000000000000000000000000:ℝ)) (by norm_num [p188,cells188,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p188,cells188,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (121709907834885008953625000000000000000000000000000/122089087785995297616970204674374344014200519925369:ℝ) (250000000000000000000000000000/101363499537372724860294120187:ℝ) (1/10:ℝ)) :
 GlobalSource (996987485039493287098553500000000000000000000000000000/1000101905572058222924782792253814639441190247180261997:ℝ) (1000000000000000000000000000000/405492214471093694022618440757:ℝ) (1/10:ℝ) := by
 have h185 := source185 hβ hp
 have h186 := source186 hβ h185
 have h187 := source187 hβ h186
 have h188 := source188 hβ h187
 exact h188
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0185_0188
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0189_0192
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0189_0192

theorem source189 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (996987485039493287098553500000000000000000000000000000/1000101905572058222924782792253814639441190247180261997:ℝ) (1000000000000000000000000000000/405492214471093694022618440757:ℝ) (1/10:ℝ)) :
 GlobalSource (124623417749000980915221109375000000000000000000000000/125012722750435643850561458329797320871613868974341807:ℝ) (31250000000000000000000000000/12671634546198138440613026419:ℝ) (1/10:ℝ) := by
 have heps : 0<p189.toReal.eps := by norm_num [p189,Params.toReal]
 have hcap : p189.toReal.cap=1/10 := by norm_num [p189,Params.toReal]
 have hi : GlobalSource (p189.toReal.state (((cells189 3).2:ℝ)/(p189.den:ℝ))).B (p189.toReal.state (((cells189 3).2:ℝ)/(p189.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p189,cells189,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw3 : (cells189 3).1 < (cells189 3).2 := by decide
 have hs3 := combined_source_of_signs (p:=p189) hw3 heps hcap (commonSigns189 3) (highSigns189 3) hβ hi
 have hw2 : (cells189 2).1 < (cells189 2).2 := by decide
 have hs2 := combined_source_of_signs (p:=p189) hw2 heps hcap (commonSigns189 2) (highSigns189 2) hβ hs3
 have hw1 : (cells189 1).1 < (cells189 1).2 := by decide
 have hs1 := combined_source_of_signs (p:=p189) hw1 heps hcap (commonSigns189 1) (highSigns189 1) hβ hs2
 have hw0 : (cells189 0).1 < (cells189 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p189) hw0 heps hcap (commonSigns189 0) (highSigns189 0) hβ hs1
 have hpcommon := common_positive hw0 (commonSigns189 0)
   (u:=((cells189 0).1:ℝ)/(p189.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p189.toReal.state (((cells189 0).1:ℝ)/(p189.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(12671634546198138440613026419/31250000000000000000000000000:ℝ)) (by norm_num [p189,cells189,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p189,cells189,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source190 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (124623417749000980915221109375000000000000000000000000/125012722750435643850561458329797320871613868974341807:ℝ) (31250000000000000000000000000/12671634546198138440613026419:ℝ) (1/10:ℝ)) :
 GlobalSource (1328535225988862028815926500000000000000000000000000000/1332794611756224200787268978907851395937885065844973531:ℝ) (1000000000000000000000000000000/405865730748124664571155618509:ℝ) (1/10:ℝ) := by
 have heps : 0<p190.toReal.eps := by norm_num [p190,Params.toReal]
 have hcap : p190.toReal.cap=1/10 := by norm_num [p190,Params.toReal]
 have hi : GlobalSource (p190.toReal.state (((cells190 0).2:ℝ)/(p190.den:ℝ))).B (p190.toReal.state (((cells190 0).2:ℝ)/(p190.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p190,cells190,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells190 0).1 < (cells190 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p190) hw0 heps hcap (commonSigns190 0) (highSigns190 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns190 0)
   (u:=((cells190 0).1:ℝ)/(p190.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p190.toReal.state (((cells190 0).1:ℝ)/(p190.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(405865730748124664571155618509/1000000000000000000000000000000:ℝ)) (by norm_num [p190,cells190,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p190,cells190,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source191 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1328535225988862028815926500000000000000000000000000000/1332794611756224200787268978907851395937885065844973531:ℝ) (1000000000000000000000000000000/405865730748124664571155618509:ℝ) (1/10:ℝ)) :
 GlobalSource (995815496991285195902120875000000000000000000000000000/999090763381636069329000190357433392656850032495040317:ℝ) (250000000000000000000000000000/101560119713754290972236867017:ℝ) (1/10:ℝ) := by
 have heps : 0<p191.toReal.eps := by norm_num [p191,Params.toReal]
 have hcap : p191.toReal.cap=1/10 := by norm_num [p191,Params.toReal]
 have hi : GlobalSource (p191.toReal.state (((cells191 0).2:ℝ)/(p191.den:ℝ))).B (p191.toReal.state (((cells191 0).2:ℝ)/(p191.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p191,cells191,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells191 0).1 < (cells191 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p191) hw0 heps hcap (commonSigns191 0) (highSigns191 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns191 0)
   (u:=((cells191 0).1:ℝ)/(p191.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p191.toReal.state (((cells191 0).1:ℝ)/(p191.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(101560119713754290972236867017/250000000000000000000000000000:ℝ)) (by norm_num [p191,cells191,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p191,cells191,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source192 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (995815496991285195902120875000000000000000000000000000/999090763381636069329000190357433392656850032495040317:ℝ) (250000000000000000000000000000/101560119713754290972236867017:ℝ) (1/10:ℝ)) :
 GlobalSource (31847346383709563846153500000000000000000000000000000/31954758286401105134705797158311006256122268822053619:ℝ) (1000000000000000000000000000000/406616555786611362039041869963:ℝ) (1/10:ℝ) := by
 have heps : 0<p192.toReal.eps := by norm_num [p192,Params.toReal]
 have hcap : p192.toReal.cap=1/10 := by norm_num [p192,Params.toReal]
 have hi : GlobalSource (p192.toReal.state (((cells192 0).2:ℝ)/(p192.den:ℝ))).B (p192.toReal.state (((cells192 0).2:ℝ)/(p192.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p192,cells192,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells192 0).1 < (cells192 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p192) hw0 heps hcap (commonSigns192 0) (highSigns192 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns192 0)
   (u:=((cells192 0).1:ℝ)/(p192.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p192.toReal.state (((cells192 0).1:ℝ)/(p192.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(406616555786611362039041869963/1000000000000000000000000000000:ℝ)) (by norm_num [p192,cells192,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p192,cells192,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (996987485039493287098553500000000000000000000000000000/1000101905572058222924782792253814639441190247180261997:ℝ) (1000000000000000000000000000000/405492214471093694022618440757:ℝ) (1/10:ℝ)) :
 GlobalSource (31847346383709563846153500000000000000000000000000000/31954758286401105134705797158311006256122268822053619:ℝ) (1000000000000000000000000000000/406616555786611362039041869963:ℝ) (1/10:ℝ) := by
 have h189 := source189 hβ hp
 have h190 := source190 hβ h189
 have h191 := source191 hβ h190
 have h192 := source192 hβ h191
 exact h192
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0189_0192
