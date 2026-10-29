/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.LowOnlyStep
import Candidate.Local.Qrh.JointDetector.NativeDirectSource
namespace Qrh.JointDetector.FollowupLowBank.Refined
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
def p1 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(4:ℝ),(1/10:ℝ),(3598006744456386443/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates1 : LowOnlyStep.Gates p1 := by
  constructor <;> norm_num [p1,Set.mem_Icc]
def p2 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(3598006744456386443/1000000000000000000:ℝ),(1/10:ℝ),(1654385959643130751/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates2 : LowOnlyStep.Gates p2 := by
  constructor <;> norm_num [p2,Set.mem_Icc]
def p3 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1654385959643130751/500000000000000000:ℝ),(1/10:ℝ),(620133394978688121/200000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates3 : LowOnlyStep.Gates p3 := by
  constructor <;> norm_num [p3,Set.mem_Icc]
def p4 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(620133394978688121/200000000000000000:ℝ),(1/10:ℝ),(2950935116514125617/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates4 : LowOnlyStep.Gates p4 := by
  constructor <;> norm_num [p4,Set.mem_Icc]
def p5 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2950935116514125617/1000000000000000000:ℝ),(1/10:ℝ),(2843202791945211331/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates5 : LowOnlyStep.Gates p5 := by
  constructor <;> norm_num [p5,Set.mem_Icc]
def p6 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2843202791945211331/1000000000000000000:ℝ),(1/10:ℝ),(2765689202768886367/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates6 : LowOnlyStep.Gates p6 := by
  constructor <;> norm_num [p6,Set.mem_Icc]
def p7 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2765689202768886367/1000000000000000000:ℝ),(1/10:ℝ),(84684938895617661/31250000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates7 : LowOnlyStep.Gates p7 := by
  constructor <;> norm_num [p7,Set.mem_Icc]
def p8 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(84684938895617661/31250000000000000:ℝ),(1/10:ℝ),(667447650590929139/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates8 : LowOnlyStep.Gates p8 := by
  constructor <;> norm_num [p8,Set.mem_Icc]
def p9 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(667447650590929139/250000000000000000:ℝ),(1/10:ℝ),(2640918839972263467/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates9 : LowOnlyStep.Gates p9 := by
  constructor <;> norm_num [p9,Set.mem_Icc]
def p10 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2640918839972263467/1000000000000000000:ℝ),(1/10:ℝ),(1310072779125263701/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates10 : LowOnlyStep.Gates p10 := by
  constructor <;> norm_num [p10,Set.mem_Icc]
def p11 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1310072779125263701/500000000000000000:ℝ),(1/10:ℝ),(651299786756403789/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates11 : LowOnlyStep.Gates p11 := by
  constructor <;> norm_num [p11,Set.mem_Icc]
def p12 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(651299786756403789/250000000000000000:ℝ),(1/10:ℝ),(648611294736984033/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates12 : LowOnlyStep.Gates p12 := by
  constructor <;> norm_num [p12,Set.mem_Icc]
def p13 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(648611294736984033/250000000000000000:ℝ),(1/10:ℝ),(1293353840391814451/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates13 : LowOnlyStep.Gates p13 := by
  constructor <;> norm_num [p13,Set.mem_Icc]
def p14 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1293353840391814451/500000000000000000:ℝ),(1/10:ℝ),(2581140537808105121/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates14 : LowOnlyStep.Gates p14 := by
  constructor <;> norm_num [p14,Set.mem_Icc]
def p15 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2581140537808105121/1000000000000000000:ℝ),(1/10:ℝ),(2577134969050377511/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates15 : LowOnlyStep.Gates p15 := by
  constructor <;> norm_num [p15,Set.mem_Icc]
def p16 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2577134969050377511/1000000000000000000:ℝ),(1/10:ℝ),(643563238893836637/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates16 : LowOnlyStep.Gates p16 := by
  constructor <;> norm_num [p16,Set.mem_Icc]
def p17 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(643563238893836637/250000000000000000:ℝ),(1/10:ℝ),(1286089671010329111/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates17 : LowOnlyStep.Gates p17 := by
  constructor <;> norm_num [p17,Set.mem_Icc]
def p18 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1286089671010329111/500000000000000000:ℝ),(1/10:ℝ),(1285343686785855463/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates18 : LowOnlyStep.Gates p18 := by
  constructor <;> norm_num [p18,Set.mem_Icc]
def p19 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1285343686785855463/500000000000000000:ℝ),(1/10:ℝ),(2569613899757064313/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates19 : LowOnlyStep.Gates p19 := by
  constructor <;> norm_num [p19,Set.mem_Icc]
def p20 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2569613899757064313/1000000000000000000:ℝ),(1/10:ℝ),(2568841533537426743/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates20 : LowOnlyStep.Gates p20 := by
  constructor <;> norm_num [p20,Set.mem_Icc]
def p21 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2568841533537426743/1000000000000000000:ℝ),(1/10:ℝ),(2568285814740099941/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates21 : LowOnlyStep.Gates p21 := by
  constructor <;> norm_num [p21,Set.mem_Icc]
def p22 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2568285814740099941/1000000000000000000:ℝ),(1/10:ℝ),(2567885974128418009/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates22 : LowOnlyStep.Gates p22 := by
  constructor <;> norm_num [p22,Set.mem_Icc]
def p23 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2567885974128418009/1000000000000000000:ℝ),(1/10:ℝ),(2567598288134135967/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates23 : LowOnlyStep.Gates p23 := by
  constructor <;> norm_num [p23,Set.mem_Icc]
def p24 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2567598288134135967/1000000000000000000:ℝ),(1/10:ℝ),(2567391297576178627/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates24 : LowOnlyStep.Gates p24 := by
  constructor <;> norm_num [p24,Set.mem_Icc]
def p25 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2567391297576178627/1000000000000000000:ℝ),(1/10:ℝ),(80226323985022457/31250000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates25 : LowOnlyStep.Gates p25 := by
  constructor <;> norm_num [p25,Set.mem_Icc]
def p26 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(80226323985022457/31250000000000000:ℝ),(1/10:ℝ),(513427042418940417/200000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates26 : LowOnlyStep.Gates p26 := by
  constructor <;> norm_num [p26,Set.mem_Icc]
def p27 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(513427042418940417/200000000000000000:ℝ),(1/10:ℝ),(2567058113585006911/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates27 : LowOnlyStep.Gates p27 := by
  constructor <;> norm_num [p27,Set.mem_Icc]
def p28 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2567058113585006911/1000000000000000000:ℝ),(1/10:ℝ),(51340052821545687/20000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates28 : LowOnlyStep.Gates p28 := by
  constructor <;> norm_num [p28,Set.mem_Icc]
def p29 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(51340052821545687/20000000000000000:ℝ),(1/10:ℝ),(256696272851444499/100000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates29 : LowOnlyStep.Gates p29 := by
  constructor <;> norm_num [p29,Set.mem_Icc]
def p30 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(256696272851444499/100000000000000000:ℝ),(1/10:ℝ),(513386802271636987/200000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates30 : LowOnlyStep.Gates p30 := by
  constructor <;> norm_num [p30,Set.mem_Icc]
def p31 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(513386802271636987/200000000000000000:ℝ),(1/10:ℝ),(80216042166119857/31250000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates31 : LowOnlyStep.Gates p31 := by
  constructor <;> norm_num [p31,Set.mem_Icc]
def p32 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(80216042166119857/31250000000000000:ℝ),(1/10:ℝ),(256689848294152639/100000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates32 : LowOnlyStep.Gates p32 := by
  constructor <;> norm_num [p32,Set.mem_Icc]
def p33 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(256689848294152639/100000000000000000:ℝ),(1/10:ℝ),(641721946640036159/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates33 : LowOnlyStep.Gates p33 := by
  constructor <;> norm_num [p33,Set.mem_Icc]
def p34 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641721946640036159/250000000000000000:ℝ),(1/10:ℝ),(513376018099141029/200000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates34 : LowOnlyStep.Gates p34 := by
  constructor <;> norm_num [p34,Set.mem_Icc]
def p35 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(513376018099141029/200000000000000000:ℝ),(1/10:ℝ),(320859319145545561/125000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates35 : LowOnlyStep.Gates p35 := by
  constructor <;> norm_num [p35,Set.mem_Icc]
def p36 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(320859319145545561/125000000000000000:ℝ),(1/10:ℝ),(2566870569045128313/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates36 : LowOnlyStep.Gates p36 := by
  constructor <;> norm_num [p36,Set.mem_Icc]
def p37 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566870569045128313/1000000000000000000:ℝ),(1/10:ℝ),(1283433851232310103/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates37 : LowOnlyStep.Gates p37 := by
  constructor <;> norm_num [p37,Set.mem_Icc]
def p38 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283433851232310103/500000000000000000:ℝ),(1/10:ℝ),(2566865639955111241/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates38 : LowOnlyStep.Gates p38 := by
  constructor <;> norm_num [p38,Set.mem_Icc]
def p39 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566865639955111241/1000000000000000000:ℝ),(1/10:ℝ),(1283432077988020957/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates39 : LowOnlyStep.Gates p39 := by
  constructor <;> norm_num [p39,Set.mem_Icc]
def p40 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283432077988020957/500000000000000000:ℝ),(1/10:ℝ),(160428943015662461/62500000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates40 : LowOnlyStep.Gates p40 := by
  constructor <;> norm_num [p40,Set.mem_Icc]
def p41 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(160428943015662461/62500000000000000:ℝ),(1/10:ℝ),(1283431160010171581/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates41 : LowOnlyStep.Gates p41 := by
  constructor <;> norm_num [p41,Set.mem_Icc]
def p42 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283431160010171581/500000000000000000:ℝ),(1/10:ℝ),(2566861767277378493/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates42 : LowOnlyStep.Gates p42 := by
  constructor <;> norm_num [p42,Set.mem_Icc]
def p43 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566861767277378493/1000000000000000000:ℝ),(1/10:ℝ),(1283430684788941713/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates43 : LowOnlyStep.Gates p43 := by
  constructor <;> norm_num [p43,Set.mem_Icc]
def p44 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430684788941713/500000000000000000:ℝ),(1/10:ℝ),(1283430541716213079/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates44 : LowOnlyStep.Gates p44 := by
  constructor <;> norm_num [p44,Set.mem_Icc]
def p45 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430541716213079/500000000000000000:ℝ),(1/10:ℝ),(128343043877514359/50000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates45 : LowOnlyStep.Gates p45 := by
  constructor <;> norm_num [p45,Set.mem_Icc]
def p46 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(128343043877514359/50000000000000000:ℝ),(1/10:ℝ),(513372145883548209/200000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates46 : LowOnlyStep.Gates p46 := by
  constructor <;> norm_num [p46,Set.mem_Icc]
def p47 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(513372145883548209/200000000000000000:ℝ),(1/10:ℝ),(641715155709031083/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates47 : LowOnlyStep.Gates p47 := by
  constructor <;> norm_num [p47,Set.mem_Icc]
def p48 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715155709031083/250000000000000000:ℝ),(1/10:ℝ),(1283430273075235699/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates48 : LowOnlyStep.Gates p48 := by
  constructor <;> norm_num [p48,Set.mem_Icc]
def p49 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430273075235699/500000000000000000:ℝ),(1/10:ℝ),(2566860490975014811/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates49 : LowOnlyStep.Gates p49 := by
  constructor <;> norm_num [p49,Set.mem_Icc]
def p50 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860490975014811/1000000000000000000:ℝ),(1/10:ℝ),(513372090255236153/200000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates50 : LowOnlyStep.Gates p50 := by
  constructor <;> norm_num [p50,Set.mem_Icc]
def p51 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(513372090255236153/200000000000000000:ℝ),(1/10:ℝ),(641715105678200683/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates51 : LowOnlyStep.Gates p51 := by
  constructor <;> norm_num [p51,Set.mem_Icc]
def p52 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715105678200683/250000000000000000:ℝ),(1/10:ℝ),(641715100540351019/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates52 : LowOnlyStep.Gates p52 := by
  constructor <;> norm_num [p52,Set.mem_Icc]
def p53 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715100540351019/250000000000000000:ℝ),(1/10:ℝ),(2566860387374638091/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates53 : LowOnlyStep.Gates p53 := by
  constructor <;> norm_num [p53,Set.mem_Icc]
def p54 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860387374638091/1000000000000000000:ℝ),(1/10:ℝ),(2566860376735535033/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates54 : LowOnlyStep.Gates p54 := by
  constructor <;> norm_num [p54,Set.mem_Icc]
def p55 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860376735535033/1000000000000000000:ℝ),(1/10:ℝ),(641715092270170611/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates55 : LowOnlyStep.Gates p55 := by
  constructor <;> norm_num [p55,Set.mem_Icc]
def p56 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715092270170611/250000000000000000:ℝ),(1/10:ℝ),(2566860363573003099/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates56 : LowOnlyStep.Gates p56 := by
  constructor <;> norm_num [p56,Set.mem_Icc]
def p57 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860363573003099/1000000000000000000:ℝ),(1/10:ℝ),(641715089902554631/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates57 : LowOnlyStep.Gates p57 := by
  constructor <;> norm_num [p57,Set.mem_Icc]
def p58 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715089902554631/250000000000000000:ℝ),(1/10:ℝ),(128343017837949417/50000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates58 : LowOnlyStep.Gates p58 := by
  constructor <;> norm_num [p58,Set.mem_Icc]
def p59 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(128343017837949417/50000000000000000:ℝ),(1/10:ℝ),(320857544338440427/125000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates59 : LowOnlyStep.Gates p59 := by
  constructor <;> norm_num [p59,Set.mem_Icc]
def p60 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(320857544338440427/125000000000000000:ℝ),(1/10:ℝ),(20053596509621023/7812500000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates60 : LowOnlyStep.Gates p60 := by
  constructor <;> norm_num [p60,Set.mem_Icc]
def p61 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(20053596509621023/7812500000000000:ℝ),(1/10:ℝ),(2566860352169483091/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates61 : LowOnlyStep.Gates p61 := by
  constructor <;> norm_num [p61,Set.mem_Icc]
def p62 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860352169483091/1000000000000000000:ℝ),(1/10:ℝ),(51337207028107333/20000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates62 : LowOnlyStep.Gates p62 := by
  constructor <;> norm_num [p62,Set.mem_Icc]
def p63 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(51337207028107333/20000000000000000:ℝ),(1/10:ℝ),(2566860350855583583/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates63 : LowOnlyStep.Gates p63 := by
  constructor <;> norm_num [p63,Set.mem_Icc]
def p64 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860350855583583/1000000000000000000:ℝ),(1/10:ℝ),(2566860350460013739/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates64 : LowOnlyStep.Gates p64 := by
  constructor <;> norm_num [p64,Set.mem_Icc]
def p65 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860350460013739/1000000000000000000:ℝ),(1/10:ℝ),(2566860350175400569/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates65 : LowOnlyStep.Gates p65 := by
  constructor <;> norm_num [p65,Set.mem_Icc]
def p66 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860350175400569/1000000000000000000:ℝ),(1/10:ℝ),(1283430174985310457/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates66 : LowOnlyStep.Gates p66 := by
  constructor <;> norm_num [p66,Set.mem_Icc]
def p67 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430174985310457/500000000000000000:ℝ),(1/10:ℝ),(2566860349823281607/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates67 : LowOnlyStep.Gates p67 := by
  constructor <;> norm_num [p67,Set.mem_Icc]
def p68 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349823281607/1000000000000000000:ℝ),(1/10:ℝ),(2566860349717270727/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates68 : LowOnlyStep.Gates p68 := by
  constructor <;> norm_num [p68,Set.mem_Icc]
def p69 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349717270727/1000000000000000000:ℝ),(1/10:ℝ),(64171508741024893/25000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates69 : LowOnlyStep.Gates p69 := by
  constructor <;> norm_num [p69,Set.mem_Icc]
def p70 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(64171508741024893/25000000000000000:ℝ),(1/10:ℝ),(641715087396528931/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates70 : LowOnlyStep.Gates p70 := by
  constructor <;> norm_num [p70,Set.mem_Icc]
def p71 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715087396528931/250000000000000000:ℝ),(1/10:ℝ),(1283430174773314737/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates71 : LowOnlyStep.Gates p71 := by
  constructor <;> norm_num [p71,Set.mem_Icc]
def p72 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430174773314737/500000000000000000:ℝ),(1/10:ℝ),(2566860349518219051/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates72 : LowOnlyStep.Gates p72 := by
  constructor <;> norm_num [p72,Set.mem_Icc]
def p73 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349518219051/1000000000000000000:ℝ),(1/10:ℝ),(2566860349497777703/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates73 : LowOnlyStep.Gates p73 := by
  constructor <;> norm_num [p73,Set.mem_Icc]
def p74 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349497777703/1000000000000000000:ℝ),(1/10:ℝ),(2566860349483070119/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates74 : LowOnlyStep.Gates p74 := by
  constructor <;> norm_num [p74,Set.mem_Icc]
def p75 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349483070119/1000000000000000000:ℝ),(1/10:ℝ),(641715087368121997/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates75 : LowOnlyStep.Gates p75 := by
  constructor <;> norm_num [p75,Set.mem_Icc]
def p76 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715087368121997/250000000000000000:ℝ),(1/10:ℝ),(1283430174732437063/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates76 : LowOnlyStep.Gates p76 := by
  constructor <;> norm_num [p76,Set.mem_Icc]
def p77 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430174732437063/500000000000000000:ℝ),(1/10:ℝ),(128343017472969797/50000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates77 : LowOnlyStep.Gates p77 := by
  constructor <;> norm_num [p77,Set.mem_Icc]
def p78 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(128343017472969797/50000000000000000:ℝ),(1/10:ℝ),(320857543681931797/125000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates78 : LowOnlyStep.Gates p78 := by
  constructor <;> norm_num [p78,Set.mem_Icc]
def p79 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(320857543681931797/125000000000000000:ℝ),(1/10:ℝ),(1283430174726309207/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates79 : LowOnlyStep.Gates p79 := by
  constructor <;> norm_num [p79,Set.mem_Icc]
def p80 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430174726309207/500000000000000000:ℝ),(1/10:ℝ),(1283430174725288967/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates80 : LowOnlyStep.Gates p80 := by
  constructor <;> norm_num [p80,Set.mem_Icc]
def p81 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430174725288967/500000000000000000:ℝ),(1/10:ℝ),(1283430174724554903/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates81 : LowOnlyStep.Gates p81 := by
  constructor <;> norm_num [p81,Set.mem_Icc]
def p82 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430174724554903/500000000000000000:ℝ),(1/10:ℝ),(513372069889610697/200000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates82 : LowOnlyStep.Gates p82 := by
  constructor <;> norm_num [p82,Set.mem_Icc]
def p83 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(513372069889610697/200000000000000000:ℝ),(1/10:ℝ),(128343017472364673/50000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates83 : LowOnlyStep.Gates p83 := by
  constructor <;> norm_num [p83,Set.mem_Icc]
def p84 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(128343017472364673/50000000000000000:ℝ),(1/10:ℝ),(2566860349446746621/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates84 : LowOnlyStep.Gates p84 := by
  constructor <;> norm_num [p84,Set.mem_Icc]
def p85 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349446746621/1000000000000000000:ℝ),(1/10:ℝ),(2566860349446353169/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates85 : LowOnlyStep.Gates p85 := by
  constructor <;> norm_num [p85,Set.mem_Icc]
def p86 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349446353169/1000000000000000000:ℝ),(1/10:ℝ),(8021438592018969/3125000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates86 : LowOnlyStep.Gates p86 := by
  constructor <;> norm_num [p86,Set.mem_Icc]
def p87 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(8021438592018969/3125000000000000:ℝ),(1/10:ℝ),(2566860349445866397/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates87 : LowOnlyStep.Gates p87 := by
  constructor <;> norm_num [p87,Set.mem_Icc]
def p88 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349445866397/1000000000000000000:ℝ),(1/10:ℝ),(2566860349445719847/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates88 : LowOnlyStep.Gates p88 := by
  constructor <;> norm_num [p88,Set.mem_Icc]
def p89 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349445719847/1000000000000000000:ℝ),(1/10:ℝ),(641715087361403601/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates89 : LowOnlyStep.Gates p89 := by
  constructor <;> norm_num [p89,Set.mem_Icc]
def p90 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715087361403601/250000000000000000:ℝ),(1/10:ℝ),(2566860349445538537/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates90 : LowOnlyStep.Gates p90 := by
  constructor <;> norm_num [p90,Set.mem_Icc]
def p91 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349445538537/1000000000000000000:ℝ),(1/10:ℝ),(2566860349445483951/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates91 : LowOnlyStep.Gates p91 := by
  constructor <;> norm_num [p91,Set.mem_Icc]
def p92 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349445483951/1000000000000000000:ℝ),(1/10:ℝ),(641715087361361169/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates92 : LowOnlyStep.Gates p92 := by
  constructor <;> norm_num [p92,Set.mem_Icc]
def p93 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715087361361169/250000000000000000:ℝ),(1/10:ℝ),(1283430174722708209/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates93 : LowOnlyStep.Gates p93 := by
  constructor <;> norm_num [p93,Set.mem_Icc]
def p94 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430174722708209/500000000000000000:ℝ),(1/10:ℝ),(1283430174722698043/500000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates94 : LowOnlyStep.Gates p94 := by
  constructor <;> norm_num [p94,Set.mem_Icc]
def p95 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(1283430174722698043/500000000000000000:ℝ),(1/10:ℝ),(2566860349445381457/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates95 : LowOnlyStep.Gates p95 := by
  constructor <;> norm_num [p95,Set.mem_Icc]
def p96 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349445381457/1000000000000000000:ℝ),(1/10:ℝ),(641715087361342733/250000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates96 : LowOnlyStep.Gates p96 := by
  constructor <;> norm_num [p96,Set.mem_Icc]
def p97 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(641715087361342733/250000000000000000:ℝ),(1/10:ℝ),(2566860349445363359/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates97 : LowOnlyStep.Gates p97 := by
  constructor <;> norm_num [p97,Set.mem_Icc]
def p98 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(2566860349445363359/1000000000000000000:ℝ),(1/10:ℝ),(256686034944535791/100000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates98 : LowOnlyStep.Gates p98 := by
  constructor <;> norm_num [p98,Set.mem_Icc]
def p99 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(256686034944535791/100000000000000000:ℝ),(1/10:ℝ),(256686034944535399/100000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates99 : LowOnlyStep.Gates p99 := by
  constructor <;> norm_num [p99,Set.mem_Icc]
def p100 : LowOnlyStep.Params := ⟨(999999999999999/1000000000000000:ℝ),(256686034944535399/100000000000000000:ℝ),(1/10:ℝ),(2566860349445351169/1000000000000000000:ℝ),(1/10:ℝ),(74767140597693/100000000000000:ℝ),(3/25:ℝ)⟩
theorem gates100 : LowOnlyStep.Gates p100 := by
  constructor <;> norm_num [p100,Set.mem_Icc]
theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ (43691785149423/50000000000000:ℝ)) :
    GlobalSource (999999999999999/1000000000000000:ℝ) (2566860349445351169/1000000000000000000:ℝ) (1/10:ℝ) := by
  have hcut : 2*HeckeZeroSupremum.beta-1 < (74767140597693/100000000000000:ℝ) := by linarith
  have hseed : GlobalSource (999999999999999/1000000000000000:ℝ) (4:ℝ) (1/10:ℝ) :=
    NativeDirectSource.global_source (999999999999999/1000000000000000:ℝ) (by norm_num) hβ
  have h1 := gates1.global_source hβ hcut hseed
  have h2 := gates2.global_source hβ hcut h1
  have h3 := gates3.global_source hβ hcut h2
  have h4 := gates4.global_source hβ hcut h3
  have h5 := gates5.global_source hβ hcut h4
  have h6 := gates6.global_source hβ hcut h5
  have h7 := gates7.global_source hβ hcut h6
  have h8 := gates8.global_source hβ hcut h7
  have h9 := gates9.global_source hβ hcut h8
  have h10 := gates10.global_source hβ hcut h9
  have h11 := gates11.global_source hβ hcut h10
  have h12 := gates12.global_source hβ hcut h11
  have h13 := gates13.global_source hβ hcut h12
  have h14 := gates14.global_source hβ hcut h13
  have h15 := gates15.global_source hβ hcut h14
  have h16 := gates16.global_source hβ hcut h15
  have h17 := gates17.global_source hβ hcut h16
  have h18 := gates18.global_source hβ hcut h17
  have h19 := gates19.global_source hβ hcut h18
  have h20 := gates20.global_source hβ hcut h19
  have h21 := gates21.global_source hβ hcut h20
  have h22 := gates22.global_source hβ hcut h21
  have h23 := gates23.global_source hβ hcut h22
  have h24 := gates24.global_source hβ hcut h23
  have h25 := gates25.global_source hβ hcut h24
  have h26 := gates26.global_source hβ hcut h25
  have h27 := gates27.global_source hβ hcut h26
  have h28 := gates28.global_source hβ hcut h27
  have h29 := gates29.global_source hβ hcut h28
  have h30 := gates30.global_source hβ hcut h29
  have h31 := gates31.global_source hβ hcut h30
  have h32 := gates32.global_source hβ hcut h31
  have h33 := gates33.global_source hβ hcut h32
  have h34 := gates34.global_source hβ hcut h33
  have h35 := gates35.global_source hβ hcut h34
  have h36 := gates36.global_source hβ hcut h35
  have h37 := gates37.global_source hβ hcut h36
  have h38 := gates38.global_source hβ hcut h37
  have h39 := gates39.global_source hβ hcut h38
  have h40 := gates40.global_source hβ hcut h39
  have h41 := gates41.global_source hβ hcut h40
  have h42 := gates42.global_source hβ hcut h41
  have h43 := gates43.global_source hβ hcut h42
  have h44 := gates44.global_source hβ hcut h43
  have h45 := gates45.global_source hβ hcut h44
  have h46 := gates46.global_source hβ hcut h45
  have h47 := gates47.global_source hβ hcut h46
  have h48 := gates48.global_source hβ hcut h47
  have h49 := gates49.global_source hβ hcut h48
  have h50 := gates50.global_source hβ hcut h49
  have h51 := gates51.global_source hβ hcut h50
  have h52 := gates52.global_source hβ hcut h51
  have h53 := gates53.global_source hβ hcut h52
  have h54 := gates54.global_source hβ hcut h53
  have h55 := gates55.global_source hβ hcut h54
  have h56 := gates56.global_source hβ hcut h55
  have h57 := gates57.global_source hβ hcut h56
  have h58 := gates58.global_source hβ hcut h57
  have h59 := gates59.global_source hβ hcut h58
  have h60 := gates60.global_source hβ hcut h59
  have h61 := gates61.global_source hβ hcut h60
  have h62 := gates62.global_source hβ hcut h61
  have h63 := gates63.global_source hβ hcut h62
  have h64 := gates64.global_source hβ hcut h63
  have h65 := gates65.global_source hβ hcut h64
  have h66 := gates66.global_source hβ hcut h65
  have h67 := gates67.global_source hβ hcut h66
  have h68 := gates68.global_source hβ hcut h67
  have h69 := gates69.global_source hβ hcut h68
  have h70 := gates70.global_source hβ hcut h69
  have h71 := gates71.global_source hβ hcut h70
  have h72 := gates72.global_source hβ hcut h71
  have h73 := gates73.global_source hβ hcut h72
  have h74 := gates74.global_source hβ hcut h73
  have h75 := gates75.global_source hβ hcut h74
  have h76 := gates76.global_source hβ hcut h75
  have h77 := gates77.global_source hβ hcut h76
  have h78 := gates78.global_source hβ hcut h77
  have h79 := gates79.global_source hβ hcut h78
  have h80 := gates80.global_source hβ hcut h79
  have h81 := gates81.global_source hβ hcut h80
  have h82 := gates82.global_source hβ hcut h81
  have h83 := gates83.global_source hβ hcut h82
  have h84 := gates84.global_source hβ hcut h83
  have h85 := gates85.global_source hβ hcut h84
  have h86 := gates86.global_source hβ hcut h85
  have h87 := gates87.global_source hβ hcut h86
  have h88 := gates88.global_source hβ hcut h87
  have h89 := gates89.global_source hβ hcut h88
  have h90 := gates90.global_source hβ hcut h89
  have h91 := gates91.global_source hβ hcut h90
  have h92 := gates92.global_source hβ hcut h91
  have h93 := gates93.global_source hβ hcut h92
  have h94 := gates94.global_source hβ hcut h93
  have h95 := gates95.global_source hβ hcut h94
  have h96 := gates96.global_source hβ hcut h95
  have h97 := gates97.global_source hβ hcut h96
  have h98 := gates98.global_source hβ hcut h97
  have h99 := gates99.global_source hβ hcut h98
  have h100 := gates100.global_source hβ hcut h99
  exact h100
#print axioms source
end
end Qrh.JointDetector.FollowupLowBank.Refined
