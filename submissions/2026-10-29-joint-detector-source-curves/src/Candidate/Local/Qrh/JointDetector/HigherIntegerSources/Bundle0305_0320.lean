/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0305_0308
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0309_0312
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0313_0316
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0317_0320
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0305_0308
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0305_0308

theorem source305 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24802906250000000000000000000000000/25243236227959016986755807395199093:ℝ) (62500000000000000000000000000/28650366457444811403694569267:ℝ) (1/10:ℝ)) :
 GlobalSource (396596500000000000000000000000000000/403708824079267355909408119692097161:ℝ) (1000000000000000000000000000000/458979607379516059284507838059:ℝ) (1/10:ℝ) := by
 have heps : 0<p305.toReal.eps := by norm_num [p305,Params.toReal]
 have hcap : p305.toReal.cap=1/10 := by norm_num [p305,Params.toReal]
 have hi : GlobalSource (p305.toReal.state (((cells305 0).2:ℝ)/(p305.den:ℝ))).B (p305.toReal.state (((cells305 0).2:ℝ)/(p305.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p305,cells305,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells305 0).1 < (cells305 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p305) hw0 heps hcap (commonSigns305 0) (highSigns305 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns305 0)
   (u:=((cells305 0).1:ℝ)/(p305.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p305.toReal.state (((cells305 0).1:ℝ)/(p305.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(458979607379516059284507838059/1000000000000000000000000000000:ℝ)) (by norm_num [p305,cells305,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p305,cells305,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source306 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (396596500000000000000000000000000000/403708824079267355909408119692097161:ℝ) (1000000000000000000000000000000/458979607379516059284507838059:ℝ) (1/10:ℝ)) :
 GlobalSource (132115500000000000000000000000000000/134508726282575582059894375337890721:ℝ) (1000000000000000000000000000000/459555665091326345556246221597:ℝ) (1/10:ℝ) := by
 have heps : 0<p306.toReal.eps := by norm_num [p306,Params.toReal]
 have hcap : p306.toReal.cap=1/10 := by norm_num [p306,Params.toReal]
 have hi : GlobalSource (p306.toReal.state (((cells306 0).2:ℝ)/(p306.den:ℝ))).B (p306.toReal.state (((cells306 0).2:ℝ)/(p306.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p306,cells306,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells306 0).1 < (cells306 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p306) hw0 heps hcap (commonSigns306 0) (highSigns306 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns306 0)
   (u:=((cells306 0).1:ℝ)/(p306.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p306.toReal.state (((cells306 0).1:ℝ)/(p306.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(459555665091326345556246221597/1000000000000000000000000000000:ℝ)) (by norm_num [p306,cells306,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p306,cells306,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source307 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (132115500000000000000000000000000000/134508726282575582059894375337890721:ℝ) (1000000000000000000000000000000/459555665091326345556246221597:ℝ) (1/10:ℝ)) :
 GlobalSource (396096500000000000000000000000000000/403343844385657501986376376612689011:ℝ) (1000000000000000000000000000000/460134048825784671987780196209:ℝ) (1/10:ℝ) := by
 have heps : 0<p307.toReal.eps := by norm_num [p307,Params.toReal]
 have hcap : p307.toReal.cap=1/10 := by norm_num [p307,Params.toReal]
 have hi : GlobalSource (p307.toReal.state (((cells307 0).2:ℝ)/(p307.den:ℝ))).B (p307.toReal.state (((cells307 0).2:ℝ)/(p307.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p307,cells307,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells307 0).1 < (cells307 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p307) hw0 heps hcap (commonSigns307 0) (highSigns307 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns307 0)
   (u:=((cells307 0).1:ℝ)/(p307.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p307.toReal.state (((cells307 0).1:ℝ)/(p307.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(460134048825784671987780196209/1000000000000000000000000000000:ℝ)) (by norm_num [p307,cells307,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p307,cells307,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source308 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (396096500000000000000000000000000000/403343844385657501986376376612689011:ℝ) (1000000000000000000000000000000/460134048825784671987780196209:ℝ) (1/10:ℝ)) :
 GlobalSource (197923250000000000000000000000000000/201580910563625276534055691222511709:ℝ) (500000000000000000000000000000/230357385520193350010748390971:ℝ) (1/10:ℝ) := by
 have heps : 0<p308.toReal.eps := by norm_num [p308,Params.toReal]
 have hcap : p308.toReal.cap=1/10 := by norm_num [p308,Params.toReal]
 have hi : GlobalSource (p308.toReal.state (((cells308 0).2:ℝ)/(p308.den:ℝ))).B (p308.toReal.state (((cells308 0).2:ℝ)/(p308.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p308,cells308,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells308 0).1 < (cells308 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p308) hw0 heps hcap (commonSigns308 0) (highSigns308 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns308 0)
   (u:=((cells308 0).1:ℝ)/(p308.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p308.toReal.state (((cells308 0).1:ℝ)/(p308.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(230357385520193350010748390971/500000000000000000000000000000:ℝ)) (by norm_num [p308,cells308,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p308,cells308,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24802906250000000000000000000000000/25243236227959016986755807395199093:ℝ) (62500000000000000000000000000/28650366457444811403694569267:ℝ) (1/10:ℝ)) :
 GlobalSource (197923250000000000000000000000000000/201580910563625276534055691222511709:ℝ) (500000000000000000000000000000/230357385520193350010748390971:ℝ) (1/10:ℝ) := by
 have h305 := source305 hβ hp
 have h306 := source306 hβ h305
 have h307 := source307 hβ h306
 have h308 := source308 hβ h307
 exact h308
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0305_0308
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0309_0312
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0309_0312

theorem source309 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (197923250000000000000000000000000000/201580910563625276534055691222511709:ℝ) (500000000000000000000000000000/230357385520193350010748390971:ℝ) (1/10:ℝ)) :
 GlobalSource (131865500000000000000000000000000000/134326703169319735817976138813048743:ℝ) (1000000000000000000000000000000/461297844279634935654277880351:ℝ) (1/10:ℝ) := by
 have heps : 0<p309.toReal.eps := by norm_num [p309,Params.toReal]
 have hcap : p309.toReal.cap=1/10 := by norm_num [p309,Params.toReal]
 have hi : GlobalSource (p309.toReal.state (((cells309 0).2:ℝ)/(p309.den:ℝ))).B (p309.toReal.state (((cells309 0).2:ℝ)/(p309.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p309,cells309,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells309 0).1 < (cells309 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p309) hw0 heps hcap (commonSigns309 0) (highSigns309 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns309 0)
   (u:=((cells309 0).1:ℝ)/(p309.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p309.toReal.state (((cells309 0).1:ℝ)/(p309.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(461297844279634935654277880351/1000000000000000000000000000000:ℝ)) (by norm_num [p309,cells309,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p309,cells309,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source310 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (131865500000000000000000000000000000/134326703169319735817976138813048743:ℝ) (1000000000000000000000000000000/461297844279634935654277880351:ℝ) (1/10:ℝ)) :
 GlobalSource (24709156250000000000000000000000000/25174919372781607674720595667402427:ℝ) (62500000000000000000000000000/28867705073487158473854542613:ℝ) (1/10:ℝ) := by
 have heps : 0<p310.toReal.eps := by norm_num [p310,Params.toReal]
 have hcap : p310.toReal.cap=1/10 := by norm_num [p310,Params.toReal]
 have hi : GlobalSource (p310.toReal.state (((cells310 0).2:ℝ)/(p310.den:ℝ))).B (p310.toReal.state (((cells310 0).2:ℝ)/(p310.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p310,cells310,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells310 0).1 < (cells310 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p310) hw0 heps hcap (commonSigns310 0) (highSigns310 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns310 0)
   (u:=((cells310 0).1:ℝ)/(p310.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p310.toReal.state (((cells310 0).1:ℝ)/(p310.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(28867705073487158473854542613/62500000000000000000000000000:ℝ)) (by norm_num [p310,cells310,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p310,cells310,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source311 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (24709156250000000000000000000000000/25174919372781607674720595667402427:ℝ) (62500000000000000000000000000/28867705073487158473854542613:ℝ) (1/10:ℝ)) :
 GlobalSource (197548250000000000000000000000000000/201308811467443971087767218625318337:ℝ) (500000000000000000000000000000/231235547224828500443690025403:ℝ) (1/10:ℝ) := by
 have heps : 0<p311.toReal.eps := by norm_num [p311,Params.toReal]
 have hcap : p311.toReal.cap=1/10 := by norm_num [p311,Params.toReal]
 have hi : GlobalSource (p311.toReal.state (((cells311 0).2:ℝ)/(p311.den:ℝ))).B (p311.toReal.state (((cells311 0).2:ℝ)/(p311.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p311,cells311,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells311 0).1 < (cells311 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p311) hw0 heps hcap (commonSigns311 0) (highSigns311 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns311 0)
   (u:=((cells311 0).1:ℝ)/(p311.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p311.toReal.state (((cells311 0).1:ℝ)/(p311.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(231235547224828500443690025403/500000000000000000000000000000:ℝ)) (by norm_num [p311,cells311,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p311,cells311,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source312 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (197548250000000000000000000000000000/201308811467443971087767218625318337:ℝ) (500000000000000000000000000000/231235547224828500443690025403:ℝ) (1/10:ℝ)) :
 GlobalSource (131615500000000000000000000000000000/134145616286128665167066707059143689:ℝ) (1000000000000000000000000000000/463061296911311854850019527773:ℝ) (1/10:ℝ) := by
 have heps : 0<p312.toReal.eps := by norm_num [p312,Params.toReal]
 have hcap : p312.toReal.cap=1/10 := by norm_num [p312,Params.toReal]
 have hi : GlobalSource (p312.toReal.state (((cells312 0).2:ℝ)/(p312.den:ℝ))).B (p312.toReal.state (((cells312 0).2:ℝ)/(p312.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p312,cells312,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells312 0).1 < (cells312 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p312) hw0 heps hcap (commonSigns312 0) (highSigns312 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns312 0)
   (u:=((cells312 0).1:ℝ)/(p312.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p312.toReal.state (((cells312 0).1:ℝ)/(p312.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(463061296911311854850019527773/1000000000000000000000000000000:ℝ)) (by norm_num [p312,cells312,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p312,cells312,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (197923250000000000000000000000000000/201580910563625276534055691222511709:ℝ) (500000000000000000000000000000/230357385520193350010748390971:ℝ) (1/10:ℝ)) :
 GlobalSource (131615500000000000000000000000000000/134145616286128665167066707059143689:ℝ) (1000000000000000000000000000000/463061296911311854850019527773:ℝ) (1/10:ℝ) := by
 have h309 := source309 hβ hp
 have h310 := source310 hβ h309
 have h311 := source311 hβ h310
 have h312 := source312 hβ h311
 exact h312
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0309_0312
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0313_0316
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0313_0316

theorem source313 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (131615500000000000000000000000000000/134145616286128665167066707059143689:ℝ) (1000000000000000000000000000000/463061296911311854850019527773:ℝ) (1/10:ℝ)) :
 GlobalSource (394596500000000000000000000000000000/402256388175569067620289603417446793:ℝ) (1000000000000000000000000000000/463653901460926402806303061067:ℝ) (1/10:ℝ) := by
 have heps : 0<p313.toReal.eps := by norm_num [p313,Params.toReal]
 have hcap : p313.toReal.cap=1/10 := by norm_num [p313,Params.toReal]
 have hi : GlobalSource (p313.toReal.state (((cells313 0).2:ℝ)/(p313.den:ℝ))).B (p313.toReal.state (((cells313 0).2:ℝ)/(p313.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p313,cells313,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells313 0).1 < (cells313 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p313) hw0 heps hcap (commonSigns313 0) (highSigns313 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns313 0)
   (u:=((cells313 0).1:ℝ)/(p313.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p313.toReal.state (((cells313 0).1:ℝ)/(p313.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(463653901460926402806303061067/1000000000000000000000000000000:ℝ)) (by norm_num [p313,cells313,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p313,cells313,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source314 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (394596500000000000000000000000000000/402256388175569067620289603417446793:ℝ) (1000000000000000000000000000000/463653901460926402806303061067:ℝ) (1/10:ℝ)) :
 GlobalSource (394346500000000000000000000000000000/402076241328302234323832891528413749:ℝ) (1000000000000000000000000000000/464248921089533673399115890731:ℝ) (1/10:ℝ) := by
 have heps : 0<p314.toReal.eps := by norm_num [p314,Params.toReal]
 have hcap : p314.toReal.cap=1/10 := by norm_num [p314,Params.toReal]
 have hi : GlobalSource (p314.toReal.state (((cells314 0).2:ℝ)/(p314.den:ℝ))).B (p314.toReal.state (((cells314 0).2:ℝ)/(p314.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p314,cells314,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells314 0).1 < (cells314 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p314) hw0 heps hcap (commonSigns314 0) (highSigns314 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns314 0)
   (u:=((cells314 0).1:ℝ)/(p314.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p314.toReal.state (((cells314 0).1:ℝ)/(p314.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(464248921089533673399115890731/1000000000000000000000000000000:ℝ)) (by norm_num [p314,cells314,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p314,cells314,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source315 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (394346500000000000000000000000000000/402076241328302234323832891528413749:ℝ) (1000000000000000000000000000000/464248921089533673399115890731:ℝ) (1/10:ℝ)) :
 GlobalSource (32841375000000000000000000000000000/33491367396646113952452899451519971:ℝ) (250000000000000000000000000000/116211592219957160487773469347:ℝ) (1/10:ℝ) := by
 have heps : 0<p315.toReal.eps := by norm_num [p315,Params.toReal]
 have hcap : p315.toReal.cap=1/10 := by norm_num [p315,Params.toReal]
 have hi : GlobalSource (p315.toReal.state (((cells315 0).2:ℝ)/(p315.den:ℝ))).B (p315.toReal.state (((cells315 0).2:ℝ)/(p315.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p315,cells315,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells315 0).1 < (cells315 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p315) hw0 heps hcap (commonSigns315 0) (highSigns315 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns315 0)
   (u:=((cells315 0).1:ℝ)/(p315.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p315.toReal.state (((cells315 0).1:ℝ)/(p315.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(116211592219957160487773469347/250000000000000000000000000000:ℝ)) (by norm_num [p315,cells315,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p315,cells315,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source316 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (32841375000000000000000000000000000/33491367396646113952452899451519971:ℝ) (250000000000000000000000000000/116211592219957160487773469347:ℝ) (1/10:ℝ)) :
 GlobalSource (78769300000000000000000000000000000/80343378182880022033716003600880461:ℝ) (200000000000000000000000000000/93089251601394567627895017259:ℝ) (1/10:ℝ) := by
 have heps : 0<p316.toReal.eps := by norm_num [p316,Params.toReal]
 have hcap : p316.toReal.cap=1/10 := by norm_num [p316,Params.toReal]
 have hi : GlobalSource (p316.toReal.state (((cells316 0).2:ℝ)/(p316.den:ℝ))).B (p316.toReal.state (((cells316 0).2:ℝ)/(p316.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p316,cells316,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells316 0).1 < (cells316 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p316) hw0 heps hcap (commonSigns316 0) (highSigns316 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns316 0)
   (u:=((cells316 0).1:ℝ)/(p316.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p316.toReal.state (((cells316 0).1:ℝ)/(p316.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(93089251601394567627895017259/200000000000000000000000000000:ℝ)) (by norm_num [p316,cells316,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p316,cells316,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (131615500000000000000000000000000000/134145616286128665167066707059143689:ℝ) (1000000000000000000000000000000/463061296911311854850019527773:ℝ) (1/10:ℝ)) :
 GlobalSource (78769300000000000000000000000000000/80343378182880022033716003600880461:ℝ) (200000000000000000000000000000/93089251601394567627895017259:ℝ) (1/10:ℝ) := by
 have h313 := source313 hβ hp
 have h314 := source314 hβ h313
 have h315 := source315 hβ h314
 have h316 := source316 hβ h315
 exact h316
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0313_0316
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0317_0320
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0317_0320

theorem source317 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (78769300000000000000000000000000000/80343378182880022033716003600880461:ℝ) (200000000000000000000000000000/93089251601394567627895017259:ℝ) (1/10:ℝ)) :
 GlobalSource (196798250000000000000000000000000000/200768844119018462066048566093787961:ℝ) (500000000000000000000000000000/233024300869703720803372141259:ℝ) (1/10:ℝ) := by
 have heps : 0<p317.toReal.eps := by norm_num [p317,Params.toReal]
 have hcap : p317.toReal.cap=1/10 := by norm_num [p317,Params.toReal]
 have hi : GlobalSource (p317.toReal.state (((cells317 0).2:ℝ)/(p317.den:ℝ))).B (p317.toReal.state (((cells317 0).2:ℝ)/(p317.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p317,cells317,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells317 0).1 < (cells317 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p317) hw0 heps hcap (commonSigns317 0) (highSigns317 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns317 0)
   (u:=((cells317 0).1:ℝ)/(p317.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p317.toReal.state (((cells317 0).1:ℝ)/(p317.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(233024300869703720803372141259/500000000000000000000000000000:ℝ)) (by norm_num [p317,cells317,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p317,cells317,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source318 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (196798250000000000000000000000000000/200768844119018462066048566093787961:ℝ) (500000000000000000000000000000/233024300869703720803372141259:ℝ) (1/10:ℝ)) :
 GlobalSource (131115500000000000000000000000000000/133786267059260736353200673258804033:ℝ) (1000000000000000000000000000000/466653413439674970624328718381:ℝ) (1/10:ℝ) := by
 have heps : 0<p318.toReal.eps := by norm_num [p318,Params.toReal]
 have hcap : p318.toReal.cap=1/10 := by norm_num [p318,Params.toReal]
 have hi : GlobalSource (p318.toReal.state (((cells318 0).2:ℝ)/(p318.den:ℝ))).B (p318.toReal.state (((cells318 0).2:ℝ)/(p318.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p318,cells318,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells318 0).1 < (cells318 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p318) hw0 heps hcap (commonSigns318 0) (highSigns318 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns318 0)
   (u:=((cells318 0).1:ℝ)/(p318.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p318.toReal.state (((cells318 0).1:ℝ)/(p318.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(466653413439674970624328718381/1000000000000000000000000000000:ℝ)) (by norm_num [p318,cells318,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p318,cells318,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source319 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (131115500000000000000000000000000000/133786267059260736353200673258804033:ℝ) (1000000000000000000000000000000/466653413439674970624328718381:ℝ) (1/10:ℝ)) :
 GlobalSource (196548250000000000000000000000000000/200590115091042748395691165204084827:ℝ) (500000000000000000000000000000/233630353282624835216900442713:ℝ) (1/10:ℝ) := by
 have heps : 0<p319.toReal.eps := by norm_num [p319,Params.toReal]
 have hcap : p319.toReal.cap=1/10 := by norm_num [p319,Params.toReal]
 have hi : GlobalSource (p319.toReal.state (((cells319 0).2:ℝ)/(p319.den:ℝ))).B (p319.toReal.state (((cells319 0).2:ℝ)/(p319.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p319,cells319,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells319 0).1 < (cells319 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p319) hw0 heps hcap (commonSigns319 0) (highSigns319 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns319 0)
   (u:=((cells319 0).1:ℝ)/(p319.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p319.toReal.state (((cells319 0).1:ℝ)/(p319.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(233630353282624835216900442713/500000000000000000000000000000:ℝ)) (by norm_num [p319,cells319,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p319,cells319,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source320 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (196548250000000000000000000000000000/200590115091042748395691165204084827:ℝ) (500000000000000000000000000000/233630353282624835216900442713:ℝ) (1/10:ℝ)) :
 GlobalSource (392846500000000000000000000000000000/401001975700734720734842210504414119:ℝ) (1000000000000000000000000000000/467870494669376709422167863761:ℝ) (1/10:ℝ) := by
 have heps : 0<p320.toReal.eps := by norm_num [p320,Params.toReal]
 have hcap : p320.toReal.cap=1/10 := by norm_num [p320,Params.toReal]
 have hi : GlobalSource (p320.toReal.state (((cells320 0).2:ℝ)/(p320.den:ℝ))).B (p320.toReal.state (((cells320 0).2:ℝ)/(p320.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p320,cells320,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells320 0).1 < (cells320 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p320) hw0 heps hcap (commonSigns320 0) (highSigns320 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns320 0)
   (u:=((cells320 0).1:ℝ)/(p320.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p320.toReal.state (((cells320 0).1:ℝ)/(p320.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(467870494669376709422167863761/1000000000000000000000000000000:ℝ)) (by norm_num [p320,cells320,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p320,cells320,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (78769300000000000000000000000000000/80343378182880022033716003600880461:ℝ) (200000000000000000000000000000/93089251601394567627895017259:ℝ) (1/10:ℝ)) :
 GlobalSource (392846500000000000000000000000000000/401001975700734720734842210504414119:ℝ) (1000000000000000000000000000000/467870494669376709422167863761:ℝ) (1/10:ℝ) := by
 have h317 := source317 hβ hp
 have h318 := source318 hβ h317
 have h319 := source319 hβ h318
 have h320 := source320 hβ h319
 exact h320
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0317_0320
