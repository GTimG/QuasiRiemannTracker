/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0129_0132
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0133_0136
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0137_0140
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0141_0144
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0129_0132
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0129_0132

theorem source129 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (61355620116481723223000000000000000000000000000000/61480230993877527921947485316178157028806293251433:ℝ) (500000000000000000000000000000/200179842021557947481034133033:ℝ) (1/10:ℝ)) :
 GlobalSource (52349166633507615721780000000000000000000000000000/52456444137425764162273427528459450068986262450227:ℝ) (40000000000000000000000000000/16017941787927365965704895881:ℝ) (1/10:ℝ) := by
 have heps : 0<p129.toReal.eps := by norm_num [p129,Params.toReal]
 have hcap : p129.toReal.cap=1/10 := by norm_num [p129,Params.toReal]
 have hi : GlobalSource (p129.toReal.state (((cells129 0).2:ℝ)/(p129.den:ℝ))).B (p129.toReal.state (((cells129 0).2:ℝ)/(p129.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p129,cells129,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells129 0).1 < (cells129 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p129) hw0 heps hcap (commonSigns129 0) (highSigns129 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns129 0)
   (u:=((cells129 0).1:ℝ)/(p129.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p129.toReal.state (((cells129 0).1:ℝ)/(p129.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(16017941787927365965704895881/40000000000000000000000000000:ℝ)) (by norm_num [p129,cells129,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p129,cells129,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source130 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (52349166633507615721780000000000000000000000000000/52456444137425764162273427528459450068986262450227:ℝ) (40000000000000000000000000000/16017941787927365965704895881:ℝ) (1/10:ℝ)) :
 GlobalSource (392561530757131207199500000000000000000000000000000/393373196625943455532665699474573057460894737378939:ℝ) (1000000000000000000000000000000/400537480639453087689394566887:ℝ) (1/10:ℝ) := by
 have heps : 0<p130.toReal.eps := by norm_num [p130,Params.toReal]
 have hcap : p130.toReal.cap=1/10 := by norm_num [p130,Params.toReal]
 have hi : GlobalSource (p130.toReal.state (((cells130 0).2:ℝ)/(p130.den:ℝ))).B (p130.toReal.state (((cells130 0).2:ℝ)/(p130.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p130,cells130,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells130 0).1 < (cells130 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p130) hw0 heps hcap (commonSigns130 0) (highSigns130 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns130 0)
   (u:=((cells130 0).1:ℝ)/(p130.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p130.toReal.state (((cells130 0).1:ℝ)/(p130.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(400537480639453087689394566887/1000000000000000000000000000000:ℝ)) (by norm_num [p130,cells130,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p130,cells130,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source131 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (392561530757131207199500000000000000000000000000000/393373196625943455532665699474573057460894737378939:ℝ) (1000000000000000000000000000000/400537480639453087689394566887:ℝ) (1/10:ℝ)) :
 GlobalSource (78500862352591059297130000000000000000000000000000/78664615028894695665433210391085340087588838131737:ℝ) (20000000000000000000000000000/8012529838875413746292226883:ℝ) (1/10:ℝ) := by
 have heps : 0<p131.toReal.eps := by norm_num [p131,Params.toReal]
 have hcap : p131.toReal.cap=1/10 := by norm_num [p131,Params.toReal]
 have hi : GlobalSource (p131.toReal.state (((cells131 0).2:ℝ)/(p131.den:ℝ))).B (p131.toReal.state (((cells131 0).2:ℝ)/(p131.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p131,cells131,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells131 0).1 < (cells131 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p131) hw0 heps hcap (commonSigns131 0) (highSigns131 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns131 0)
   (u:=((cells131 0).1:ℝ)/(p131.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p131.toReal.state (((cells131 0).1:ℝ)/(p131.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(8012529838875413746292226883/20000000000000000000000000000:ℝ)) (by norm_num [p131,cells131,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p131,cells131,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source132 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (78500862352591059297130000000000000000000000000000/78664615028894695665433210391085340087588838131737:ℝ) (20000000000000000000000000000/8012529838875413746292226883:ℝ) (1/10:ℝ)) :
 GlobalSource (81759810993495705369125000000000000000000000000000/81931868038376356173538731932048484478058091809799:ℝ) (250000000000000000000000000000/100178894672027337756195809661:ℝ) (1/10:ℝ) := by
 have heps : 0<p132.toReal.eps := by norm_num [p132,Params.toReal]
 have hcap : p132.toReal.cap=1/10 := by norm_num [p132,Params.toReal]
 have hi : GlobalSource (p132.toReal.state (((cells132 0).2:ℝ)/(p132.den:ℝ))).B (p132.toReal.state (((cells132 0).2:ℝ)/(p132.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p132,cells132,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells132 0).1 < (cells132 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p132) hw0 heps hcap (commonSigns132 0) (highSigns132 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns132 0)
   (u:=((cells132 0).1:ℝ)/(p132.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p132.toReal.state (((cells132 0).1:ℝ)/(p132.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(100178894672027337756195809661/250000000000000000000000000000:ℝ)) (by norm_num [p132,cells132,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p132,cells132,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (61355620116481723223000000000000000000000000000000/61480230993877527921947485316178157028806293251433:ℝ) (500000000000000000000000000000/200179842021557947481034133033:ℝ) (1/10:ℝ)) :
 GlobalSource (81759810993495705369125000000000000000000000000000/81931868038376356173538731932048484478058091809799:ℝ) (250000000000000000000000000000/100178894672027337756195809661:ℝ) (1/10:ℝ) := by
 have h129 := source129 hβ hp
 have h130 := source130 hβ h129
 have h131 := source131 hβ h130
 have h132 := source132 hβ h131
 exact h132
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0129_0132
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0133_0136
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0133_0136

theorem source133 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (81759810993495705369125000000000000000000000000000/81931868038376356173538731932048484478058091809799:ℝ) (250000000000000000000000000000/100178894672027337756195809661:ℝ) (1/10:ℝ)) :
 GlobalSource (784779747549206950115900000000000000000000000000000/786445741886164634426437606623694357630624203056757:ℝ) (200000000000000000000000000000/80160948189913219941883956641:ℝ) (1/10:ℝ) := by
 have heps : 0<p133.toReal.eps := by norm_num [p133,Params.toReal]
 have hcap : p133.toReal.cap=1/10 := by norm_num [p133,Params.toReal]
 have hi : GlobalSource (p133.toReal.state (((cells133 0).2:ℝ)/(p133.den:ℝ))).B (p133.toReal.state (((cells133 0).2:ℝ)/(p133.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p133,cells133,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells133 0).1 < (cells133 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p133) hw0 heps hcap (commonSigns133 0) (highSigns133 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns133 0)
   (u:=((cells133 0).1:ℝ)/(p133.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p133.toReal.state (((cells133 0).1:ℝ)/(p133.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(80160948189913219941883956641/200000000000000000000000000000:ℝ)) (by norm_num [p133,cells133,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p133,cells133,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source134 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (784779747549206950115900000000000000000000000000000/786445741886164634426437606623694357630624203056757:ℝ) (200000000000000000000000000000/80160948189913219941883956641:ℝ) (1/10:ℝ)) :
 GlobalSource (245207909237767227715062500000000000000000000000000/245732992636910750635081448654195063879994042949803:ℝ) (125000000000000000000000000000/50111747350670345526259572761:ℝ) (1/10:ℝ) := by
 have heps : 0<p134.toReal.eps := by norm_num [p134,Params.toReal]
 have hcap : p134.toReal.cap=1/10 := by norm_num [p134,Params.toReal]
 have hi : GlobalSource (p134.toReal.state (((cells134 0).2:ℝ)/(p134.den:ℝ))).B (p134.toReal.state (((cells134 0).2:ℝ)/(p134.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p134,cells134,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells134 0).1 < (cells134 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p134) hw0 heps hcap (commonSigns134 0) (highSigns134 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns134 0)
   (u:=((cells134 0).1:ℝ)/(p134.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p134.toReal.state (((cells134 0).1:ℝ)/(p134.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(50111747350670345526259572761/125000000000000000000000000000:ℝ)) (by norm_num [p134,cells134,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p134,cells134,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source135 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (245207909237767227715062500000000000000000000000000/245732992636910750635081448654195063879994042949803:ℝ) (125000000000000000000000000000/50111747350670345526259572761:ℝ) (1/10:ℝ)) :
 GlobalSource (261516957190834435753500000000000000000000000000000/262081812273402645113493852963085195491703322950909:ℝ) (1000000000000000000000000000000/400983292332846177834334332229:ℝ) (1/10:ℝ) := by
 have heps : 0<p135.toReal.eps := by norm_num [p135,Params.toReal]
 have hcap : p135.toReal.cap=1/10 := by norm_num [p135,Params.toReal]
 have hi : GlobalSource (p135.toReal.state (((cells135 0).2:ℝ)/(p135.den:ℝ))).B (p135.toReal.state (((cells135 0).2:ℝ)/(p135.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p135,cells135,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells135 0).1 < (cells135 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p135) hw0 heps hcap (commonSigns135 0) (highSigns135 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns135 0)
   (u:=((cells135 0).1:ℝ)/(p135.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p135.toReal.state (((cells135 0).1:ℝ)/(p135.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(400983292332846177834334332229/1000000000000000000000000000000:ℝ)) (by norm_num [p135,cells135,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p135,cells135,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source136 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (261516957190834435753500000000000000000000000000000/262081812273402645113493852963085195491703322950909:ℝ) (1000000000000000000000000000000/400983292332846177834334332229:ℝ) (1/10:ℝ)) :
 GlobalSource (245136385495047339322750000000000000000000000000000/245670413446382440645098599809460095272953320314333:ℝ) (500000000000000000000000000000/200536340804744184664114328521:ℝ) (1/10:ℝ) := by
 have heps : 0<p136.toReal.eps := by norm_num [p136,Params.toReal]
 have hcap : p136.toReal.cap=1/10 := by norm_num [p136,Params.toReal]
 have hi : GlobalSource (p136.toReal.state (((cells136 0).2:ℝ)/(p136.den:ℝ))).B (p136.toReal.state (((cells136 0).2:ℝ)/(p136.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p136,cells136,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells136 0).1 < (cells136 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p136) hw0 heps hcap (commonSigns136 0) (highSigns136 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns136 0)
   (u:=((cells136 0).1:ℝ)/(p136.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p136.toReal.state (((cells136 0).1:ℝ)/(p136.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(200536340804744184664114328521/500000000000000000000000000000:ℝ)) (by norm_num [p136,cells136,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p136,cells136,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (81759810993495705369125000000000000000000000000000/81931868038376356173538731932048484478058091809799:ℝ) (250000000000000000000000000000/100178894672027337756195809661:ℝ) (1/10:ℝ)) :
 GlobalSource (245136385495047339322750000000000000000000000000000/245670413446382440645098599809460095272953320314333:ℝ) (500000000000000000000000000000/200536340804744184664114328521:ℝ) (1/10:ℝ) := by
 have h133 := source133 hβ hp
 have h134 := source134 hβ h133
 have h135 := source135 hβ h134
 have h136 := source136 hβ h135
 exact h136
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0133_0136
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0137_0140
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0137_0140

theorem source137 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (245136385495047339322750000000000000000000000000000/245670413446382440645098599809460095272953320314333:ℝ) (500000000000000000000000000000/200536340804744184664114328521:ℝ) (1/10:ℝ)) :
 GlobalSource (3921609977978998322025500000000000000000000000000000/3930226175293867568027528350797085562810546257508127:ℝ) (1000000000000000000000000000000/401162146712886756324172640759:ℝ) (1/10:ℝ) := by
 have heps : 0<p137.toReal.eps := by norm_num [p137,Params.toReal]
 have hcap : p137.toReal.cap=1/10 := by norm_num [p137,Params.toReal]
 have hi : GlobalSource (p137.toReal.state (((cells137 0).2:ℝ)/(p137.den:ℝ))).B (p137.toReal.state (((cells137 0).2:ℝ)/(p137.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p137,cells137,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells137 0).1 < (cells137 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p137) hw0 heps hcap (commonSigns137 0) (highSigns137 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns137 0)
   (u:=((cells137 0).1:ℝ)/(p137.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p137.toReal.state (((cells137 0).1:ℝ)/(p137.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(401162146712886756324172640759/1000000000000000000000000000000:ℝ)) (by norm_num [p137,cells137,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p137,cells137,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source138 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3921609977978998322025500000000000000000000000000000/3930226175293867568027528350797085562810546257508127:ℝ) (1000000000000000000000000000000/401162146712886756324172640759:ℝ) (1/10:ℝ)) :
 GlobalSource (653506298006206535814500000000000000000000000000000/654954310756084495318802126293384239019579255234821:ℝ) (1000000000000000000000000000000/401251687720764339244707727683:ℝ) (1/10:ℝ) := by
 have heps : 0<p138.toReal.eps := by norm_num [p138,Params.toReal]
 have hcap : p138.toReal.cap=1/10 := by norm_num [p138,Params.toReal]
 have hi : GlobalSource (p138.toReal.state (((cells138 0).2:ℝ)/(p138.den:ℝ))).B (p138.toReal.state (((cells138 0).2:ℝ)/(p138.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p138,cells138,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells138 0).1 < (cells138 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p138) hw0 heps hcap (commonSigns138 0) (highSigns138 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns138 0)
   (u:=((cells138 0).1:ℝ)/(p138.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p138.toReal.state (((cells138 0).1:ℝ)/(p138.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(401251687720764339244707727683/1000000000000000000000000000000:ℝ)) (by norm_num [p138,cells138,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p138,cells138,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source139 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (653506298006206535814500000000000000000000000000000/654954310756084495318802126293384239019579255234821:ℝ) (1000000000000000000000000000000/401251687720764339244707727683:ℝ) (1/10:ℝ)) :
 GlobalSource (1960232799047740053874250000000000000000000000000000/1964612841425211528162741624091907098628924425742523:ℝ) (500000000000000000000000000000/200670652355484947834207455553:ℝ) (1/10:ℝ) := by
 have heps : 0<p139.toReal.eps := by norm_num [p139,Params.toReal]
 have hcap : p139.toReal.cap=1/10 := by norm_num [p139,Params.toReal]
 have hi : GlobalSource (p139.toReal.state (((cells139 0).2:ℝ)/(p139.den:ℝ))).B (p139.toReal.state (((cells139 0).2:ℝ)/(p139.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p139,cells139,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells139 0).1 < (cells139 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p139) hw0 heps hcap (commonSigns139 0) (highSigns139 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns139 0)
   (u:=((cells139 0).1:ℝ)/(p139.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p139.toReal.state (((cells139 0).1:ℝ)/(p139.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(200670652355484947834207455553/500000000000000000000000000000:ℝ)) (by norm_num [p139,cells139,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p139,cells139,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source140 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1960232799047740053874250000000000000000000000000000/1964612841425211528162741624091907098628924425742523:ℝ) (500000000000000000000000000000/200670652355484947834207455553:ℝ) (1/10:ℝ)) :
 GlobalSource (97997335203843025015250000000000000000000000000000/98218140755404135390326361889867531260763071014123:ℝ) (500000000000000000000000000000/200715498880739087581697790581:ℝ) (1/10:ℝ) := by
 have heps : 0<p140.toReal.eps := by norm_num [p140,Params.toReal]
 have hcap : p140.toReal.cap=1/10 := by norm_num [p140,Params.toReal]
 have hi : GlobalSource (p140.toReal.state (((cells140 0).2:ℝ)/(p140.den:ℝ))).B (p140.toReal.state (((cells140 0).2:ℝ)/(p140.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p140,cells140,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells140 0).1 < (cells140 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p140) hw0 heps hcap (commonSigns140 0) (highSigns140 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns140 0)
   (u:=((cells140 0).1:ℝ)/(p140.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p140.toReal.state (((cells140 0).1:ℝ)/(p140.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(200715498880739087581697790581/500000000000000000000000000000:ℝ)) (by norm_num [p140,cells140,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p140,cells140,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (245136385495047339322750000000000000000000000000000/245670413446382440645098599809460095272953320314333:ℝ) (500000000000000000000000000000/200536340804744184664114328521:ℝ) (1/10:ℝ)) :
 GlobalSource (97997335203843025015250000000000000000000000000000/98218140755404135390326361889867531260763071014123:ℝ) (500000000000000000000000000000/200715498880739087581697790581:ℝ) (1/10:ℝ) := by
 have h137 := source137 hβ hp
 have h138 := source138 hβ h137
 have h139 := source139 hβ h138
 have h140 := source140 hβ h139
 exact h140
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0137_0140
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0141_0144
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0141_0144

theorem source141 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (97997335203843025015250000000000000000000000000000/98218140755404135390326361889867531260763071014123:ℝ) (500000000000000000000000000000/200715498880739087581697790581:ℝ) (1/10:ℝ)) :
 GlobalSource (1306440406070653964490500000000000000000000000000000/1309408568871482397518124232101245414266940011939917:ℝ) (1000000000000000000000000000000/401520766950390094601287280019:ℝ) (1/10:ℝ) := by
 have heps : 0<p141.toReal.eps := by norm_num [p141,Params.toReal]
 have hcap : p141.toReal.cap=1/10 := by norm_num [p141,Params.toReal]
 have hi : GlobalSource (p141.toReal.state (((cells141 0).2:ℝ)/(p141.den:ℝ))).B (p141.toReal.state (((cells141 0).2:ℝ)/(p141.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p141,cells141,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells141 0).1 < (cells141 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p141) hw0 heps hcap (commonSigns141 0) (highSigns141 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns141 0)
   (u:=((cells141 0).1:ℝ)/(p141.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p141.toReal.state (((cells141 0).1:ℝ)/(p141.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(401520766950390094601287280019/1000000000000000000000000000000:ℝ)) (by norm_num [p141,cells141,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p141,cells141,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source142 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1306440406070653964490500000000000000000000000000000/1309408568871482397518124232101245414266940011939917:ℝ) (1000000000000000000000000000000/401520766950390094601287280019:ℝ) (1/10:ℝ)) :
 GlobalSource (1959374514135101393166500000000000000000000000000000/1963862956013072413554454590112689188455003053282807:ℝ) (1000000000000000000000000000000/401610612355932933915113238193:ℝ) (1/10:ℝ) := by
 have heps : 0<p142.toReal.eps := by norm_num [p142,Params.toReal]
 have hcap : p142.toReal.cap=1/10 := by norm_num [p142,Params.toReal]
 have hi : GlobalSource (p142.toReal.state (((cells142 0).2:ℝ)/(p142.den:ℝ))).B (p142.toReal.state (((cells142 0).2:ℝ)/(p142.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p142,cells142,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells142 0).1 < (cells142 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p142) hw0 heps hcap (commonSigns142 0) (highSigns142 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns142 0)
   (u:=((cells142 0).1:ℝ)/(p142.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p142.toReal.state (((cells142 0).1:ℝ)/(p142.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(401610612355932933915113238193/1000000000000000000000000000000:ℝ)) (by norm_num [p142,cells142,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p142,cells142,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source143 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (1959374514135101393166500000000000000000000000000000/1963862956013072413554454590112689188455003053282807:ℝ) (1000000000000000000000000000000/401610612355932933915113238193:ℝ) (1/10:ℝ)) :
 GlobalSource (3918176838328443679194500000000000000000000000000000/3927226246432297805897464241317284757238926743285057:ℝ) (1000000000000000000000000000000/401700534056460532344401756671:ℝ) (1/10:ℝ) := by
 have heps : 0<p143.toReal.eps := by norm_num [p143,Params.toReal]
 have hcap : p143.toReal.cap=1/10 := by norm_num [p143,Params.toReal]
 have hi : GlobalSource (p143.toReal.state (((cells143 0).2:ℝ)/(p143.den:ℝ))).B (p143.toReal.state (((cells143 0).2:ℝ)/(p143.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p143,cells143,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells143 0).1 < (cells143 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p143) hw0 heps hcap (commonSigns143 0) (highSigns143 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns143 0)
   (u:=((cells143 0).1:ℝ)/(p143.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p143.toReal.state (((cells143 0).1:ℝ)/(p143.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(401700534056460532344401756671/1000000000000000000000000000000:ℝ)) (by norm_num [p143,cells143,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p143,cells143,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source144 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (3918176838328443679194500000000000000000000000000000/3927226246432297805897464241317284757238926743285057:ℝ) (1000000000000000000000000000000/401700534056460532344401756671:ℝ) (1/10:ℝ)) :
 GlobalSource (20404190877013982146125000000000000000000000000000/20451701613615147980541431400315629750785834406299:ℝ) (250000000000000000000000000000/100447633032613371288347966507:ℝ) (1/10:ℝ) := by
 have heps : 0<p144.toReal.eps := by norm_num [p144,Params.toReal]
 have hcap : p144.toReal.cap=1/10 := by norm_num [p144,Params.toReal]
 have hi : GlobalSource (p144.toReal.state (((cells144 0).2:ℝ)/(p144.den:ℝ))).B (p144.toReal.state (((cells144 0).2:ℝ)/(p144.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p144,cells144,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells144 0).1 < (cells144 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p144) hw0 heps hcap (commonSigns144 0) (highSigns144 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns144 0)
   (u:=((cells144 0).1:ℝ)/(p144.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p144.toReal.state (((cells144 0).1:ℝ)/(p144.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(100447633032613371288347966507/250000000000000000000000000000:ℝ)) (by norm_num [p144,cells144,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p144,cells144,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (97997335203843025015250000000000000000000000000000/98218140755404135390326361889867531260763071014123:ℝ) (500000000000000000000000000000/200715498880739087581697790581:ℝ) (1/10:ℝ)) :
 GlobalSource (20404190877013982146125000000000000000000000000000/20451701613615147980541431400315629750785834406299:ℝ) (250000000000000000000000000000/100447633032613371288347966507:ℝ) (1/10:ℝ) := by
 have h141 := source141 hβ hp
 have h142 := source142 hβ h141
 have h143 := source143 hβ h142
 have h144 := source144 hβ h143
 exact h144
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0141_0144
