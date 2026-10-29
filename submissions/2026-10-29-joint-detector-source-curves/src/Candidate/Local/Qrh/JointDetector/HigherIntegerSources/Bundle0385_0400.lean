/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Generated source bundle; original declaration bodies and namespaces retained. -/
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0385_0388
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCertificates
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0389_0392
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0393_0396
import Candidate.Local.Qrh.JointDetector.HigherIntegerBank.Pieces0397_0400
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0385_0388
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0385_0388

theorem source385 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (62807750000000000000000000000000000/65045622302200574228907592881370479:ℝ) (500000000000000000000000000000/256395021944636131974108835803:ℝ) (1/10:ℝ)) :
 GlobalSource (94149125000000000000000000000000000/97529272170852953372746857328395933:ℝ) (250000000000000000000000000000/128399116050934732756891458727:ℝ) (1/10:ℝ) := by
 have heps : 0<p385.toReal.eps := by norm_num [p385,Params.toReal]
 have hcap : p385.toReal.cap=1/10 := by norm_num [p385,Params.toReal]
 have hi : GlobalSource (p385.toReal.state (((cells385 0).2:ℝ)/(p385.den:ℝ))).B (p385.toReal.state (((cells385 0).2:ℝ)/(p385.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p385,cells385,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells385 0).1 < (cells385 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p385) hw0 heps hcap (commonSigns385 0) (highSigns385 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns385 0)
   (u:=((cells385 0).1:ℝ)/(p385.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p385.toReal.state (((cells385 0).1:ℝ)/(p385.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(128399116050934732756891458727/250000000000000000000000000000:ℝ)) (by norm_num [p385,cells385,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p385,cells385,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source386 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (94149125000000000000000000000000000/97529272170852953372746857328395933:ℝ) (250000000000000000000000000000/128399116050934732756891458727:ℝ) (1/10:ℝ)) :
 GlobalSource (376346500000000000000000000000000000/389960793166151832623318155857066927:ℝ) (1000000000000000000000000000000/514406537004918791607890676113:ℝ) (1/10:ℝ) := by
 have heps : 0<p386.toReal.eps := by norm_num [p386,Params.toReal]
 have hcap : p386.toReal.cap=1/10 := by norm_num [p386,Params.toReal]
 have hi : GlobalSource (p386.toReal.state (((cells386 0).2:ℝ)/(p386.den:ℝ))).B (p386.toReal.state (((cells386 0).2:ℝ)/(p386.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p386,cells386,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells386 0).1 < (cells386 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p386) hw0 heps hcap (commonSigns386 0) (highSigns386 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns386 0)
   (u:=((cells386 0).1:ℝ)/(p386.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p386.toReal.state (((cells386 0).1:ℝ)/(p386.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(514406537004918791607890676113/1000000000000000000000000000000:ℝ)) (by norm_num [p386,cells386,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p386,cells386,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source387 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (376346500000000000000000000000000000/389960793166151832623318155857066927:ℝ) (1000000000000000000000000000000/514406537004918791607890676113:ℝ) (1/10:ℝ)) :
 GlobalSource (125365500000000000000000000000000000/129934949274442200976769625417779221:ℝ) (1000000000000000000000000000000/515220284759855352752731540597:ℝ) (1/10:ℝ) := by
 have heps : 0<p387.toReal.eps := by norm_num [p387,Params.toReal]
 have hcap : p387.toReal.cap=1/10 := by norm_num [p387,Params.toReal]
 have hi : GlobalSource (p387.toReal.state (((cells387 0).2:ℝ)/(p387.den:ℝ))).B (p387.toReal.state (((cells387 0).2:ℝ)/(p387.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p387,cells387,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells387 0).1 < (cells387 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p387) hw0 heps hcap (commonSigns387 0) (highSigns387 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns387 0)
   (u:=((cells387 0).1:ℝ)/(p387.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p387.toReal.state (((cells387 0).1:ℝ)/(p387.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(515220284759855352752731540597/1000000000000000000000000000000:ℝ)) (by norm_num [p387,cells387,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p387,cells387,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source388 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (125365500000000000000000000000000000/129934949274442200976769625417779221:ℝ) (1000000000000000000000000000000/515220284759855352752731540597:ℝ) (1/10:ℝ)) :
 GlobalSource (375846500000000000000000000000000000/389649253218980088194045775924100533:ℝ) (1000000000000000000000000000000/516037730116954766579451654627:ℝ) (1/10:ℝ) := by
 have heps : 0<p388.toReal.eps := by norm_num [p388,Params.toReal]
 have hcap : p388.toReal.cap=1/10 := by norm_num [p388,Params.toReal]
 have hi : GlobalSource (p388.toReal.state (((cells388 0).2:ℝ)/(p388.den:ℝ))).B (p388.toReal.state (((cells388 0).2:ℝ)/(p388.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p388,cells388,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells388 0).1 < (cells388 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p388) hw0 heps hcap (commonSigns388 0) (highSigns388 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns388 0)
   (u:=((cells388 0).1:ℝ)/(p388.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p388.toReal.state (((cells388 0).1:ℝ)/(p388.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(516037730116954766579451654627/1000000000000000000000000000000:ℝ)) (by norm_num [p388,cells388,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p388,cells388,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (62807750000000000000000000000000000/65045622302200574228907592881370479:ℝ) (500000000000000000000000000000/256395021944636131974108835803:ℝ) (1/10:ℝ)) :
 GlobalSource (375846500000000000000000000000000000/389649253218980088194045775924100533:ℝ) (1000000000000000000000000000000/516037730116954766579451654627:ℝ) (1/10:ℝ) := by
 have h385 := source385 hβ hp
 have h386 := source386 hβ h385
 have h387 := source387 hβ h386
 have h388 := source388 hβ h387
 exact h388
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0385_0388
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0389_0392
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0389_0392

theorem source389 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (375846500000000000000000000000000000/389649253218980088194045775924100533:ℝ) (1000000000000000000000000000000/516037730116954766579451654627:ℝ) (1/10:ℝ)) :
 GlobalSource (375596500000000000000000000000000000/389494009919316814161780908569369599:ℝ) (1000000000000000000000000000000/516858895907816982906610864381:ℝ) (1/10:ℝ) := by
 have heps : 0<p389.toReal.eps := by norm_num [p389,Params.toReal]
 have hcap : p389.toReal.cap=1/10 := by norm_num [p389,Params.toReal]
 have hi : GlobalSource (p389.toReal.state (((cells389 0).2:ℝ)/(p389.den:ℝ))).B (p389.toReal.state (((cells389 0).2:ℝ)/(p389.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p389,cells389,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells389 0).1 < (cells389 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p389) hw0 heps hcap (commonSigns389 0) (highSigns389 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns389 0)
   (u:=((cells389 0).1:ℝ)/(p389.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p389.toReal.state (((cells389 0).1:ℝ)/(p389.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(516858895907816982906610864381/1000000000000000000000000000000:ℝ)) (by norm_num [p389,cells389,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p389,cells389,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source390 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (375596500000000000000000000000000000/389494009919316814161780908569369599:ℝ) (1000000000000000000000000000000/516858895907816982906610864381:ℝ) (1/10:ℝ)) :
 GlobalSource (31278875000000000000000000000000000/32444926541060163690618792699699491:ℝ) (250000000000000000000000000000/129420951287272335847505884487:ℝ) (1/10:ℝ) := by
 have heps : 0<p390.toReal.eps := by norm_num [p390,Params.toReal]
 have hcap : p390.toReal.cap=1/10 := by norm_num [p390,Params.toReal]
 have hi : GlobalSource (p390.toReal.state (((cells390 0).2:ℝ)/(p390.den:ℝ))).B (p390.toReal.state (((cells390 0).2:ℝ)/(p390.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p390,cells390,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells390 0).1 < (cells390 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p390) hw0 heps hcap (commonSigns390 0) (highSigns390 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns390 0)
   (u:=((cells390 0).1:ℝ)/(p390.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p390.toReal.state (((cells390 0).1:ℝ)/(p390.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(129420951287272335847505884487/250000000000000000000000000000:ℝ)) (by norm_num [p390,cells390,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p390,cells390,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source391 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (31278875000000000000000000000000000/32444926541060163690618792699699491:ℝ) (250000000000000000000000000000/129420951287272335847505884487:ℝ) (1/10:ℝ)) :
 GlobalSource (75019300000000000000000000000000000/77836915901956377041880408962456883:ℝ) (200000000000000000000000000000/103702496208868589504742883777:ℝ) (1/10:ℝ) := by
 have heps : 0<p391.toReal.eps := by norm_num [p391,Params.toReal]
 have hcap : p391.toReal.cap=1/10 := by norm_num [p391,Params.toReal]
 have hi : GlobalSource (p391.toReal.state (((cells391 0).2:ℝ)/(p391.den:ℝ))).B (p391.toReal.state (((cells391 0).2:ℝ)/(p391.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p391,cells391,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells391 0).1 < (cells391 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p391) hw0 heps hcap (commonSigns391 0) (highSigns391 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns391 0)
   (u:=((cells391 0).1:ℝ)/(p391.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p391.toReal.state (((cells391 0).1:ℝ)/(p391.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(103702496208868589504742883777/200000000000000000000000000000:ℝ)) (by norm_num [p391,cells391,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p391,cells391,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source392 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (75019300000000000000000000000000000/77836915901956377041880408962456883:ℝ) (200000000000000000000000000000/103702496208868589504742883777:ℝ) (1/10:ℝ)) :
 GlobalSource (23437656250000015625000000000000000000000000/24320410258901672587691572883557749069322683:ℝ) (31250000000000000000000000000/16213282573616276973023107561:ℝ) (1/10:ℝ) := by
 have heps : 0<p392.toReal.eps := by norm_num [p392,Params.toReal]
 have hcap : p392.toReal.cap=1/10 := by norm_num [p392,Params.toReal]
 have hi : GlobalSource (p392.toReal.state (((cells392 0).2:ℝ)/(p392.den:ℝ))).B (p392.toReal.state (((cells392 0).2:ℝ)/(p392.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p392,cells392,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells392 0).1 < (cells392 0).2 := by decide
 have hs0 := combined_source_of_signs (p:=p392) hw0 heps hcap (commonSigns392 0) (highSigns392 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns392 0)
   (u:=((cells392 0).1:ℝ)/(p392.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p392.toReal.state (((cells392 0).1:ℝ)/(p392.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(16213282573616276973023107561/31250000000000000000000000000:ℝ)) (by norm_num [p392,cells392,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p392,cells392,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (375846500000000000000000000000000000/389649253218980088194045775924100533:ℝ) (1000000000000000000000000000000/516037730116954766579451654627:ℝ) (1/10:ℝ)) :
 GlobalSource (23437656250000015625000000000000000000000000/24320410258901672587691572883557749069322683:ℝ) (31250000000000000000000000000/16213282573616276973023107561:ℝ) (1/10:ℝ) := by
 have h389 := source389 hβ hp
 have h390 := source390 hβ h389
 have h391 := source391 hβ h390
 have h392 := source392 hβ h391
 exact h392
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0389_0392
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0393_0396
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0393_0396

theorem source393 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (23437656250000015625000000000000000000000000/24320410258901672587691572883557749069322683:ℝ) (31250000000000000000000000000/16213282573616276973023107561:ℝ) (1/10:ℝ)) :
 GlobalSource (749505000000000500000000000000000000000000000/777944975918813317551264675840754746107735763:ℝ) (1000000000000000000000000000000/519658908584872553372035911921:ℝ) (1/10:ℝ) := by
 have heps : 0<p393.toReal.eps := by norm_num [p393,Params.toReal]
 have hcap : p393.toReal.cap=1/10 := by norm_num [p393,Params.toReal]
 have hi : GlobalSource (p393.toReal.state (((cells393 0).2:ℝ)/(p393.den:ℝ))).B (p393.toReal.state (((cells393 0).2:ℝ)/(p393.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p393,cells393,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells393 0).1 < (cells393 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p393) hw0 heps hcap (commonSigns393 0) (highSigns393 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns393 0)
   (u:=((cells393 0).1:ℝ)/(p393.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p393.toReal.state (((cells393 0).1:ℝ)/(p393.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(519658908584872553372035911921/1000000000000000000000000000000:ℝ)) (by norm_num [p393,cells393,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p393,cells393,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source394 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (749505000000000500000000000000000000000000000/777944975918813317551264675840754746107735763:ℝ) (1000000000000000000000000000000/519658908584872553372035911921:ℝ) (1/10:ℝ)) :
 GlobalSource (249668333333333500000000000000000000000000000/259212478928123119642987377052147686354119879:ℝ) (1000000000000000000000000000000/520496534061811206896354119879:ℝ) (1/10:ℝ) := by
 have heps : 0<p394.toReal.eps := by norm_num [p394,Params.toReal]
 have hcap : p394.toReal.cap=1/10 := by norm_num [p394,Params.toReal]
 have hi : GlobalSource (p394.toReal.state (((cells394 0).2:ℝ)/(p394.den:ℝ))).B (p394.toReal.state (((cells394 0).2:ℝ)/(p394.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p394,cells394,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells394 0).1 < (cells394 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p394) hw0 heps hcap (commonSigns394 0) (highSigns394 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns394 0)
   (u:=((cells394 0).1:ℝ)/(p394.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p394.toReal.state (((cells394 0).1:ℝ)/(p394.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(520496534061811206896354119879/1000000000000000000000000000000:ℝ)) (by norm_num [p394,cells394,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p394,cells394,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source395 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (249668333333333500000000000000000000000000000/259212478928123119642987377052147686354119879:ℝ) (1000000000000000000000000000000/520496534061811206896354119879:ℝ) (1/10:ℝ)) :
 GlobalSource (187126250000000125000000000000000000000000000/194332627971686862395889885045211648023522909:ℝ) (250000000000000000000000000000/130334485537974736519341174303:ℝ) (1/10:ℝ) := by
 have heps : 0<p395.toReal.eps := by norm_num [p395,Params.toReal]
 have hcap : p395.toReal.cap=1/10 := by norm_num [p395,Params.toReal]
 have hi : GlobalSource (p395.toReal.state (((cells395 0).2:ℝ)/(p395.den:ℝ))).B (p395.toReal.state (((cells395 0).2:ℝ)/(p395.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p395,cells395,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells395 0).1 < (cells395 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p395) hw0 heps hcap (commonSigns395 0) (highSigns395 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns395 0)
   (u:=((cells395 0).1:ℝ)/(p395.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p395.toReal.state (((cells395 0).1:ℝ)/(p395.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(130334485537974736519341174303/250000000000000000000000000000:ℝ)) (by norm_num [p395,cells395,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p395,cells395,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source396 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (187126250000000125000000000000000000000000000/194332627971686862395889885045211648023522909:ℝ) (250000000000000000000000000000/130334485537974736519341174303:ℝ) (1/10:ℝ)) :
 GlobalSource (93500625000000062500000000000000000000000000/97128025280081242651132096491479540383340571:ℝ) (125000000000000000000000000000/65272894551911619276794446857:ℝ) (1/10:ℝ) := by
 have heps : 0<p396.toReal.eps := by norm_num [p396,Params.toReal]
 have hcap : p396.toReal.cap=1/10 := by norm_num [p396,Params.toReal]
 have hi : GlobalSource (p396.toReal.state (((cells396 0).2:ℝ)/(p396.den:ℝ))).B (p396.toReal.state (((cells396 0).2:ℝ)/(p396.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p396,cells396,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells396 0).1 < (cells396 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p396) hw0 heps hcap (commonSigns396 0) (highSigns396 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns396 0)
   (u:=((cells396 0).1:ℝ)/(p396.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p396.toReal.state (((cells396 0).1:ℝ)/(p396.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(65272894551911619276794446857/125000000000000000000000000000:ℝ)) (by norm_num [p396,cells396,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p396,cells396,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (23437656250000015625000000000000000000000000/24320410258901672587691572883557749069322683:ℝ) (31250000000000000000000000000/16213282573616276973023107561:ℝ) (1/10:ℝ)) :
 GlobalSource (93500625000000062500000000000000000000000000/97128025280081242651132096491479540383340571:ℝ) (125000000000000000000000000000/65272894551911619276794446857:ℝ) (1/10:ℝ) := by
 have h393 := source393 hβ hp
 have h394 := source394 hβ h393
 have h395 := source395 hβ h394
 have h396 := source396 hβ h395
 exact h396
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0393_0396
namespace Qrh.JointDetector.HigherIntegerSources.Pieces0397_0400
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
open OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks.SourceCurveHigherInteger
open Qrh.JointDetector.HigherIntegerBank.Pieces0397_0400

theorem source397 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (93500625000000062500000000000000000000000000/97128025280081242651132096491479540383340571:ℝ) (125000000000000000000000000000/65272894551911619276794446857:ℝ) (1/10:ℝ)) :
 GlobalSource (249168333333333500000000000000000000000000000/258906169623447499823530141293439373311311533:ℝ) (1000000000000000000000000000000/523032200608971489043311311533:ℝ) (1/10:ℝ) := by
 have heps : 0<p397.toReal.eps := by norm_num [p397,Params.toReal]
 have hcap : p397.toReal.cap=1/10 := by norm_num [p397,Params.toReal]
 have hi : GlobalSource (p397.toReal.state (((cells397 0).2:ℝ)/(p397.den:ℝ))).B (p397.toReal.state (((cells397 0).2:ℝ)/(p397.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p397,cells397,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells397 0).1 < (cells397 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p397) hw0 heps hcap (commonSigns397 0) (highSigns397 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns397 0)
   (u:=((cells397 0).1:ℝ)/(p397.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p397.toReal.state (((cells397 0).1:ℝ)/(p397.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(523032200608971489043311311533/1000000000000000000000000000000:ℝ)) (by norm_num [p397,cells397,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p397,cells397,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source398 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (249168333333333500000000000000000000000000000/258906169623447499823530141293439373311311533:ℝ) (1000000000000000000000000000000/523032200608971489043311311533:ℝ) (1/10:ℝ)) :
 GlobalSource (373502500000000250000000000000000000000000000/388206716404871042542213439397566907790340721:ℝ) (500000000000000000000000000000/261942549344392661899263446907:ℝ) (1/10:ℝ) := by
 have heps : 0<p398.toReal.eps := by norm_num [p398,Params.toReal]
 have hcap : p398.toReal.cap=1/10 := by norm_num [p398,Params.toReal]
 have hi : GlobalSource (p398.toReal.state (((cells398 0).2:ℝ)/(p398.den:ℝ))).B (p398.toReal.state (((cells398 0).2:ℝ)/(p398.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p398,cells398,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells398 0).1 < (cells398 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p398) hw0 heps hcap (commonSigns398 0) (highSigns398 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns398 0)
   (u:=((cells398 0).1:ℝ)/(p398.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p398.toReal.state (((cells398 0).1:ℝ)/(p398.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(261942549344392661899263446907/500000000000000000000000000000:ℝ)) (by norm_num [p398,cells398,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p398,cells398,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source399 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (373502500000000250000000000000000000000000000/388206716404871042542213439397566907790340721:ℝ) (500000000000000000000000000000/261942549344392661899263446907:ℝ) (1/10:ℝ)) :
 GlobalSource (5972040000000004000000000000000000000000000/6208871800820049372281386383401567035741479:ℝ) (8000000000000000000000000000/4197934998492279925678580493:ℝ) (1/10:ℝ) := by
 have heps : 0<p399.toReal.eps := by norm_num [p399,Params.toReal]
 have hcap : p399.toReal.cap=1/10 := by norm_num [p399,Params.toReal]
 have hi : GlobalSource (p399.toReal.state (((cells399 0).2:ℝ)/(p399.den:ℝ))).B (p399.toReal.state (((cells399 0).2:ℝ)/(p399.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p399,cells399,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells399 0).1 < (cells399 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p399) hw0 heps hcap (commonSigns399 0) (highSigns399 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns399 0)
   (u:=((cells399 0).1:ℝ)/(p399.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p399.toReal.state (((cells399 0).1:ℝ)/(p399.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(4197934998492279925678580493/8000000000000000000000000000:ℝ)) (by norm_num [p399,cells399,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p399,cells399,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source400 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (5972040000000004000000000000000000000000000/6208871800820049372281386383401567035741479:ℝ) (8000000000000000000000000000/4197934998492279925678580493:ℝ) (1/10:ℝ)) :
 GlobalSource (124334166666666750000000000000000000000000000/129300856133687203388245773923500987414900889:ℝ) (500000000000000000000000000000/262801276668537104097414900889:ℝ) (1/10:ℝ) := by
 have heps : 0<p400.toReal.eps := by norm_num [p400,Params.toReal]
 have hcap : p400.toReal.cap=1/10 := by norm_num [p400,Params.toReal]
 have hi : GlobalSource (p400.toReal.state (((cells400 0).2:ℝ)/(p400.den:ℝ))).B (p400.toReal.state (((cells400 0).2:ℝ)/(p400.den:ℝ))).L (1/10) := by
  convert hp using 1 <;> norm_num [p400,cells400,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]
 have hw0 : (cells400 0).1 < (cells400 0).2 := by decide
 have hs0 := pure_source_of_signs (p:=p400) hw0 heps hcap (commonSigns400 0) (highSigns400 0) hβ hi
 have hpcommon := common_positive hw0 (commonSigns400 0)
   (u:=((cells400 0).1:ℝ)/(p400.den:ℝ))
   (by constructor; exact le_rfl; exact div_le_div_of_nonneg_right (by exact_mod_cast hw0.le) (by positivity))
 have hjoined := state_source_join (p400.toReal.state (((cells400 0).1:ℝ)/(p400.den:ℝ))) heps hcap
   (fun i => by rw [←commonGate_state]; exact hpcommon i)
   (nextY:=(262801276668537104097414900889/500000000000000000000000000000:ℝ)) (by norm_num [p400,cells400,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]) hs0
 convert hjoined using 1 <;> norm_num [p400,cells400,Params.toReal,RealParams.state, RepeatedMarks.SourceCurveCertificate.State.B,RepeatedMarks.SourceCurveCertificate.State.L]

theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (93500625000000062500000000000000000000000000/97128025280081242651132096491479540383340571:ℝ) (125000000000000000000000000000/65272894551911619276794446857:ℝ) (1/10:ℝ)) :
 GlobalSource (124334166666666750000000000000000000000000000/129300856133687203388245773923500987414900889:ℝ) (500000000000000000000000000000/262801276668537104097414900889:ℝ) (1/10:ℝ) := by
 have h397 := source397 hβ hp
 have h398 := source398 hβ h397
 have h399 := source399 hβ h398
 have h400 := source400 hβ h399
 exact h400
end
end Qrh.JointDetector.HigherIntegerSources.Pieces0397_0400
