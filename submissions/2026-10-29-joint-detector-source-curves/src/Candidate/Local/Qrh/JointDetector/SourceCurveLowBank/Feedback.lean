/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.LowOnlyStep
import Candidate.Local.Qrh.JointDetector.NativeDirectSource
namespace Qrh.JointDetector.SourceCurveLowBank.Feedback
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
def p1 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(4:ℝ),(1/10:ℝ),(719601349009/200000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates1 : LowOnlyStep.Gates p1 := by
  constructor <;> norm_num [p1,Set.mem_Icc]
def p2 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(719601349009/200000000000:ℝ),(1/10:ℝ),(3308771920167/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates2 : LowOnlyStep.Gates p2 := by
  constructor <;> norm_num [p2,Set.mem_Icc]
def p3 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(3308771920167/1000000000000:ℝ),(1/10:ℝ),(310066697589/100000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates3 : LowOnlyStep.Gates p3 := by
  constructor <;> norm_num [p3,Set.mem_Icc]
def p4 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(310066697589/100000000000:ℝ),(1/10:ℝ),(1475467558763/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates4 : LowOnlyStep.Gates p4 := by
  constructor <;> norm_num [p4,Set.mem_Icc]
def p5 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1475467558763/500000000000:ℝ),(1/10:ℝ),(2843202792919/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates5 : LowOnlyStep.Gates p5 := by
  constructor <;> norm_num [p5,Set.mem_Icc]
def p6 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2843202792919/1000000000000:ℝ),(1/10:ℝ),(17285557523/6250000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates6 : LowOnlyStep.Gates p6 := by
  constructor <;> norm_num [p6,Set.mem_Icc]
def p7 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(17285557523/6250000000:ℝ),(1/10:ℝ),(5419836091/2000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates7 : LowOnlyStep.Gates p7 := by
  constructor <;> norm_num [p7,Set.mem_Icc]
def p8 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(5419836091/2000000000:ℝ),(1/10:ℝ),(533958120627/200000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates8 : LowOnlyStep.Gates p8 := by
  constructor <;> norm_num [p8,Set.mem_Icc]
def p9 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(533958120627/200000000000:ℝ),(1/10:ℝ),(2640918840681/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates9 : LowOnlyStep.Gates p9 := by
  constructor <;> norm_num [p9,Set.mem_Icc]
def p10 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2640918840681/1000000000000:ℝ),(1/10:ℝ),(524029111781/200000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates10 : LowOnlyStep.Gates p10 := by
  constructor <;> norm_num [p10,Set.mem_Icc]
def p11 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(524029111781/200000000000:ℝ),(1/10:ℝ),(1302599573817/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates11 : LowOnlyStep.Gates p11 := by
  constructor <;> norm_num [p11,Set.mem_Icc]
def p12 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1302599573817/500000000000:ℝ),(1/10:ℝ),(1297222589759/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates12 : LowOnlyStep.Gates p12 := by
  constructor <;> norm_num [p12,Set.mem_Icc]
def p13 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1297222589759/500000000000:ℝ),(1/10:ℝ),(2586707681323/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates13 : LowOnlyStep.Gates p13 := by
  constructor <;> norm_num [p13,Set.mem_Icc]
def p14 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2586707681323/1000000000000:ℝ),(1/10:ℝ),(2581140538323/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates14 : LowOnlyStep.Gates p14 := by
  constructor <;> norm_num [p14,Set.mem_Icc]
def p15 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2581140538323/1000000000000:ℝ),(1/10:ℝ),(1288567484773/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates15 : LowOnlyStep.Gates p15 := by
  constructor <;> norm_num [p15,Set.mem_Icc]
def p16 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1288567484773/500000000000:ℝ),(1/10:ℝ),(514850591211/200000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates16 : LowOnlyStep.Gates p16 := by
  constructor <;> norm_num [p16,Set.mem_Icc]
def p17 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(514850591211/200000000000:ℝ),(1/10:ℝ),(321522417811/125000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates17 : LowOnlyStep.Gates p17 := by
  constructor <;> norm_num [p17,Set.mem_Icc]
def p18 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(321522417811/125000000000:ℝ),(1/10:ℝ),(257068737403/100000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates18 : LowOnlyStep.Gates p18 := by
  constructor <;> norm_num [p18,Set.mem_Icc]
def p19 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(257068737403/100000000000:ℝ),(1/10:ℝ),(160600868763/62500000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates19 : LowOnlyStep.Gates p19 := by
  constructor <;> norm_num [p19,Set.mem_Icc]
def p20 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(160600868763/62500000000:ℝ),(1/10:ℝ),(2568841533983/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates20 : LowOnlyStep.Gates p20 := by
  constructor <;> norm_num [p20,Set.mem_Icc]
def p21 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2568841533983/1000000000000:ℝ),(1/10:ℝ),(2568285815181/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates21 : LowOnlyStep.Gates p21 := by
  constructor <;> norm_num [p21,Set.mem_Icc]
def p22 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2568285815181/1000000000000:ℝ),(1/10:ℝ),(1283942987283/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates22 : LowOnlyStep.Gates p22 := by
  constructor <;> norm_num [p22,Set.mem_Icc]
def p23 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283942987283/500000000000:ℝ),(1/10:ℝ),(2567598288569/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates23 : LowOnlyStep.Gates p23 := by
  constructor <;> norm_num [p23,Set.mem_Icc]
def p24 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2567598288569/1000000000000:ℝ),(1/10:ℝ),(2567391298009/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates24 : LowOnlyStep.Gates p24 := by
  constructor <;> norm_num [p24,Set.mem_Icc]
def p25 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2567391298009/1000000000000:ℝ),(1/10:ℝ),(160452647997/62500000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates25 : LowOnlyStep.Gates p25 := by
  constructor <;> norm_num [p25,Set.mem_Icc]
def p26 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(160452647997/62500000000:ℝ),(1/10:ℝ),(102685408501/40000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates26 : LowOnlyStep.Gates p26 := by
  constructor <;> norm_num [p26,Set.mem_Icc]
def p27 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(102685408501/40000000000:ℝ),(1/10:ℝ),(513411622803/200000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates27 : LowOnlyStep.Gates p27 := by
  constructor <;> norm_num [p27,Set.mem_Icc]
def p28 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(513411622803/200000000000:ℝ),(1/10:ℝ),(2567002641507/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates28 : LowOnlyStep.Gates p28 := by
  constructor <;> norm_num [p28,Set.mem_Icc]
def p29 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2567002641507/1000000000000:ℝ),(1/10:ℝ),(160435170559/62500000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates29 : LowOnlyStep.Gates p29 := by
  constructor <;> norm_num [p29,Set.mem_Icc]
def p30 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(160435170559/62500000000:ℝ),(1/10:ℝ),(2566934011787/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates30 : LowOnlyStep.Gates p30 := by
  constructor <;> norm_num [p30,Set.mem_Icc]
def p31 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566934011787/1000000000000:ℝ),(1/10:ℝ),(513382669949/200000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates31 : LowOnlyStep.Gates p31 := by
  constructor <;> norm_num [p31,Set.mem_Icc]
def p32 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(513382669949/200000000000:ℝ),(1/10:ℝ),(256689848337/100000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates32 : LowOnlyStep.Gates p32 := by
  constructor <;> norm_num [p32,Set.mem_Icc]
def p33 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(256689848337/100000000000:ℝ),(1/10:ℝ),(2566887786989/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates33 : LowOnlyStep.Gates p33 := by
  constructor <;> norm_num [p33,Set.mem_Icc]
def p34 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566887786989/1000000000000:ℝ),(1/10:ℝ),(641720022731/250000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates34 : LowOnlyStep.Gates p34 := by
  constructor <;> norm_num [p34,Set.mem_Icc]
def p35 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(641720022731/250000000000:ℝ),(1/10:ℝ),(2566874553593/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates35 : LowOnlyStep.Gates p35 := by
  constructor <;> norm_num [p35,Set.mem_Icc]
def p36 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566874553593/1000000000000:ℝ),(1/10:ℝ),(1283435284737/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates36 : LowOnlyStep.Gates p36 := by
  constructor <;> norm_num [p36,Set.mem_Icc]
def p37 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283435284737/500000000000:ℝ),(1/10:ℝ),(2566867702893/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates37 : LowOnlyStep.Gates p37 := by
  constructor <;> norm_num [p37,Set.mem_Icc]
def p38 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566867702893/1000000000000:ℝ),(1/10:ℝ),(2566865640383/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates38 : LowOnlyStep.Gates p38 := by
  constructor <;> norm_num [p38,Set.mem_Icc]
def p39 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566865640383/1000000000000:ℝ),(1/10:ℝ),(641716039101/250000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates39 : LowOnlyStep.Gates p39 := by
  constructor <;> norm_num [p39,Set.mem_Icc]
def p40 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(641716039101/250000000000:ℝ),(1/10:ℝ),(2566863088679/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates40 : LowOnlyStep.Gates p40 := by
  constructor <;> norm_num [p40,Set.mem_Icc]
def p41 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566863088679/1000000000000:ℝ),(1/10:ℝ),(2566862320449/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates41 : LowOnlyStep.Gates p41 := by
  constructor <;> norm_num [p41,Set.mem_Icc]
def p42 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566862320449/1000000000000:ℝ),(1/10:ℝ),(1283430883853/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates42 : LowOnlyStep.Gates p42 := by
  constructor <;> norm_num [p42,Set.mem_Icc]
def p43 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430883853/500000000000:ℝ),(1/10:ℝ),(1283430685003/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates43 : LowOnlyStep.Gates p43 := by
  constructor <;> norm_num [p43,Set.mem_Icc]
def p44 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430685003/500000000000:ℝ),(1/10:ℝ),(2566861083861/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates44 : LowOnlyStep.Gates p44 := by
  constructor <;> norm_num [p44,Set.mem_Icc]
def p45 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566861083861/1000000000000:ℝ),(1/10:ℝ),(2566860877979/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates45 : LowOnlyStep.Gates p45 := by
  constructor <;> norm_num [p45,Set.mem_Icc]
def p46 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860877979/1000000000000:ℝ),(1/10:ℝ),(1283430364923/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates46 : LowOnlyStep.Gates p46 := by
  constructor <;> norm_num [p46,Set.mem_Icc]
def p47 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430364923/500000000000:ℝ),(1/10:ℝ),(80214394477/31250000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates47 : LowOnlyStep.Gates p47 := by
  constructor <;> norm_num [p47,Set.mem_Icc]
def p48 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(80214394477/31250000000:ℝ),(1/10:ℝ),(1283430273289/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates48 : LowOnlyStep.Gates p48 := by
  constructor <;> norm_num [p48,Set.mem_Icc]
def p49 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430273289/500000000000:ℝ),(1/10:ℝ),(2566860491403/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates49 : LowOnlyStep.Gates p49 := by
  constructor <;> norm_num [p49,Set.mem_Icc]
def p50 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860491403/1000000000000:ℝ),(1/10:ℝ),(320857556463/125000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates50 : LowOnlyStep.Gates p50 := by
  constructor <;> norm_num [p50,Set.mem_Icc]
def p51 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(320857556463/125000000000:ℝ),(1/10:ℝ),(2566860423141/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates51 : LowOnlyStep.Gates p51 := by
  constructor <;> norm_num [p51,Set.mem_Icc]
def p52 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860423141/1000000000000:ℝ),(1/10:ℝ),(256686040259/100000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates52 : LowOnlyStep.Gates p52 := by
  constructor <;> norm_num [p52,Set.mem_Icc]
def p53 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(256686040259/100000000000:ℝ),(1/10:ℝ),(2566860387803/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates53 : LowOnlyStep.Gates p53 := by
  constructor <;> norm_num [p53,Set.mem_Icc]
def p54 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860387803/1000000000000:ℝ),(1/10:ℝ),(641715094291/250000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates54 : LowOnlyStep.Gates p54 := by
  constructor <;> norm_num [p54,Set.mem_Icc]
def p55 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(641715094291/250000000000:ℝ),(1/10:ℝ),(2566860369509/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates55 : LowOnlyStep.Gates p55 := by
  constructor <;> norm_num [p55,Set.mem_Icc]
def p56 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860369509/1000000000000:ℝ),(1/10:ℝ),(2566860364001/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates56 : LowOnlyStep.Gates p56 := by
  constructor <;> norm_num [p56,Set.mem_Icc]
def p57 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860364001/1000000000000:ℝ),(1/10:ℝ),(1283430180019/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates57 : LowOnlyStep.Gates p57 := by
  constructor <;> norm_num [p57,Set.mem_Icc]
def p58 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430180019/500000000000:ℝ),(1/10:ℝ),(2566860357187/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates58 : LowOnlyStep.Gates p58 := by
  constructor <;> norm_num [p58,Set.mem_Icc]
def p59 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860357187/1000000000000:ℝ),(1/10:ℝ),(40107193049/15625000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates59 : LowOnlyStep.Gates p59 := by
  constructor <;> norm_num [p59,Set.mem_Icc]
def p60 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(40107193049/15625000000:ℝ),(1/10:ℝ),(128343017683/50000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates60 : LowOnlyStep.Gates p60 := by
  constructor <;> norm_num [p60,Set.mem_Icc]
def p61 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(128343017683/50000000000:ℝ),(1/10:ℝ),(1283430176299/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates61 : LowOnlyStep.Gates p61 := by
  constructor <;> norm_num [p61,Set.mem_Icc]
def p62 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430176299/500000000000:ℝ),(1/10:ℝ),(1283430175917/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates62 : LowOnlyStep.Gates p62 := by
  constructor <;> norm_num [p62,Set.mem_Icc]
def p63 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430175917/500000000000:ℝ),(1/10:ℝ),(641715087821/250000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates63 : LowOnlyStep.Gates p63 := by
  constructor <;> norm_num [p63,Set.mem_Icc]
def p64 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(641715087821/250000000000:ℝ),(1/10:ℝ),(320857543861/125000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates64 : LowOnlyStep.Gates p64 := by
  constructor <;> norm_num [p64,Set.mem_Icc]
def p65 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(320857543861/125000000000:ℝ),(1/10:ℝ),(2566860350603/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates65 : LowOnlyStep.Gates p65 := by
  constructor <;> norm_num [p65,Set.mem_Icc]
def p66 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860350603/1000000000000:ℝ),(1/10:ℝ),(1283430175199/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates66 : LowOnlyStep.Gates p66 := by
  constructor <;> norm_num [p66,Set.mem_Icc]
def p67 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430175199/500000000000:ℝ),(1/10:ℝ),(2566860350251/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates67 : LowOnlyStep.Gates p67 := by
  constructor <;> norm_num [p67,Set.mem_Icc]
def p68 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860350251/1000000000000:ℝ),(1/10:ℝ),(513372070029/200000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates68 : LowOnlyStep.Gates p68 := by
  constructor <;> norm_num [p68,Set.mem_Icc]
def p69 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(513372070029/200000000000:ℝ),(1/10:ℝ),(2566860350069/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates69 : LowOnlyStep.Gates p69 := by
  constructor <;> norm_num [p69,Set.mem_Icc]
def p70 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860350069/1000000000000:ℝ),(1/10:ℝ),(1283430175007/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates70 : LowOnlyStep.Gates p70 := by
  constructor <;> norm_num [p70,Set.mem_Icc]
def p71 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430175007/500000000000:ℝ),(1/10:ℝ),(102674413999/40000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates71 : LowOnlyStep.Gates p71 := by
  constructor <;> norm_num [p71,Set.mem_Icc]
def p72 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(102674413999/40000000000:ℝ),(1/10:ℝ),(2566860349947/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates72 : LowOnlyStep.Gates p72 := by
  constructor <;> norm_num [p72,Set.mem_Icc]
def p73 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860349947/1000000000000:ℝ),(1/10:ℝ),(1283430174963/500000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates73 : LowOnlyStep.Gates p73 := by
  constructor <;> norm_num [p73,Set.mem_Icc]
def p74 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(1283430174963/500000000000:ℝ),(1/10:ℝ),(2566860349911/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates74 : LowOnlyStep.Gates p74 := by
  constructor <;> norm_num [p74,Set.mem_Icc]
def p75 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860349911/1000000000000:ℝ),(1/10:ℝ),(2566860349901/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates75 : LowOnlyStep.Gates p75 := by
  constructor <;> norm_num [p75,Set.mem_Icc]
def p76 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860349901/1000000000000:ℝ),(1/10:ℝ),(2566860349893/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates76 : LowOnlyStep.Gates p76 := by
  constructor <;> norm_num [p76,Set.mem_Icc]
def p77 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860349893/1000000000000:ℝ),(1/10:ℝ),(40107192967/15625000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates77 : LowOnlyStep.Gates p77 := by
  constructor <;> norm_num [p77,Set.mem_Icc]
def p78 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(40107192967/15625000000:ℝ),(1/10:ℝ),(641715087471/250000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates78 : LowOnlyStep.Gates p78 := by
  constructor <;> norm_num [p78,Set.mem_Icc]
def p79 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(641715087471/250000000000:ℝ),(1/10:ℝ),(2566860349881/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates79 : LowOnlyStep.Gates p79 := by
  constructor <;> norm_num [p79,Set.mem_Icc]
def p80 : LowOnlyStep.Params := ⟨(999999999/1000000000:ℝ),(2566860349881/1000000000000:ℝ),(1/10:ℝ),(2566860349879/1000000000000:ℝ),(1/10:ℝ),(299068563/400000000:ℝ),(3/25:ℝ)⟩
theorem gates80 : LowOnlyStep.Gates p80 := by
  constructor <;> norm_num [p80,Set.mem_Icc]
theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
    GlobalSource (999999999/1000000000:ℝ) (2566860349879/1000000000000:ℝ) (1/10:ℝ) := by
  have hcut : 2*HeckeZeroSupremum.beta-1 < (299068563/400000000:ℝ) := by linarith
  have hseed : GlobalSource (999999999/1000000000:ℝ) (4:ℝ) (1/10:ℝ) :=
    NativeDirectSource.global_source (999999999/1000000000:ℝ) (by norm_num) hβ
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
  exact h80
#print axioms source
end
end Qrh.JointDetector.SourceCurveLowBank.Feedback
