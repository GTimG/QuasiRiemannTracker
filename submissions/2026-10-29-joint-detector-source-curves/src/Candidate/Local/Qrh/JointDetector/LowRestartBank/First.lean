/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.LowOnlyStep
namespace Qrh.JointDetector.LowRestartBank.First
noncomputable section
open Set OAI.SevenEighths QRH.Record1252270103Source
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
def p1 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(5143/2000:ℝ),(1397/10000:ℝ),(2570305808727/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates1 : LowOnlyStep.Gates p1 := by
  constructor <;> norm_num [p1,Set.mem_Icc]
def p2 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2570305808727/1000000000000:ℝ),(1/10:ℝ),(513889306591/200000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates2 : LowOnlyStep.Gates p2 := by
  constructor <;> norm_num [p2,Set.mem_Icc]
def p3 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(513889306591/200000000000:ℝ),(1/10:ℝ),(2568828244353/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates3 : LowOnlyStep.Gates p3 := by
  constructor <;> norm_num [p3,Set.mem_Icc]
def p4 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2568828244353/1000000000000:ℝ),(1/10:ℝ),(51367667143/20000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates4 : LowOnlyStep.Gates p4 := by
  constructor <;> norm_num [p4,Set.mem_Icc]
def p5 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(51367667143/20000000000:ℝ),(1/10:ℝ),(2568063240261/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates5 : LowOnlyStep.Gates p5 := by
  constructor <;> norm_num [p5,Set.mem_Icc]
def p6 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2568063240261/1000000000000:ℝ),(1/10:ℝ),(10030597271/3906250000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates6 : LowOnlyStep.Gates p6 := by
  constructor <;> norm_num [p6,Set.mem_Icc]
def p7 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(10030597271/3906250000:ℝ),(1/10:ℝ),(256766716191/100000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates7 : LowOnlyStep.Gates p7 := by
  constructor <;> norm_num [p7,Set.mem_Icc]
def p8 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(256766716191/100000000000:ℝ),(1/10:ℝ),(256754790471/100000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates8 : LowOnlyStep.Gates p8 := by
  constructor <;> norm_num [p8,Set.mem_Icc]
def p9 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(256754790471/100000000000:ℝ),(1/10:ℝ),(2567462093647/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates9 : LowOnlyStep.Gates p9 := by
  constructor <;> norm_num [p9,Set.mem_Icc]
def p10 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567462093647/1000000000000:ℝ),(1/10:ℝ),(160462521789/62500000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates10 : LowOnlyStep.Gates p10 := by
  constructor <;> norm_num [p10,Set.mem_Icc]
def p11 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(160462521789/62500000000:ℝ),(1/10:ℝ),(2567355920229/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates11 : LowOnlyStep.Gates p11 := by
  constructor <;> norm_num [p11,Set.mem_Icc]
def p12 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567355920229/1000000000000:ℝ),(1/10:ℝ),(2567323951947/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates12 : LowOnlyStep.Gates p12 := by
  constructor <;> norm_num [p12,Set.mem_Icc]
def p13 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567323951947/1000000000000:ℝ),(1/10:ℝ),(2567300949291/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates13 : LowOnlyStep.Gates p13 := by
  constructor <;> norm_num [p13,Set.mem_Icc]
def p14 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567300949291/1000000000000:ℝ),(1/10:ℝ),(1283642198909/500000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates14 : LowOnlyStep.Gates p14 := by
  constructor <;> norm_num [p14,Set.mem_Icc]
def p15 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(1283642198909/500000000000:ℝ),(1/10:ℝ),(2567272488269/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates15 : LowOnlyStep.Gates p15 := by
  constructor <;> norm_num [p15,Set.mem_Icc]
def p16 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567272488269/1000000000000:ℝ),(1/10:ℝ),(1283631959399/500000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates16 : LowOnlyStep.Gates p16 := by
  constructor <;> norm_num [p16,Set.mem_Icc]
def p17 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(1283631959399/500000000000:ℝ),(1/10:ℝ),(641814438167/250000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates17 : LowOnlyStep.Gates p17 := by
  constructor <;> norm_num [p17,Set.mem_Icc]
def p18 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(641814438167/250000000000:ℝ),(1/10:ℝ),(2567253315853/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates18 : LowOnlyStep.Gates p18 := by
  constructor <;> norm_num [p18,Set.mem_Icc]
def p19 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567253315853/1000000000000:ℝ),(1/10:ℝ),(16045313271/6250000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates19 : LowOnlyStep.Gates p19 := by
  constructor <;> norm_num [p19,Set.mem_Icc]
def p20 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(16045313271/6250000000:ℝ),(1/10:ℝ),(2567247826213/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates20 : LowOnlyStep.Gates p20 := by
  constructor <;> norm_num [p20,Set.mem_Icc]
def p21 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567247826213/1000000000000:ℝ),(1/10:ℝ),(256724617331/100000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates21 : LowOnlyStep.Gates p21 := by
  constructor <;> norm_num [p21,Set.mem_Icc]
def p22 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(256724617331/100000000000:ℝ),(1/10:ℝ),(256724498397/100000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates22 : LowOnlyStep.Gates p22 := by
  constructor <;> norm_num [p22,Set.mem_Icc]
def p23 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(256724498397/100000000000:ℝ),(1/10:ℝ),(513448825637/200000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates23 : LowOnlyStep.Gates p23 := by
  constructor <;> norm_num [p23,Set.mem_Icc]
def p24 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(513448825637/200000000000:ℝ),(1/10:ℝ),(320905439051/125000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates24 : LowOnlyStep.Gates p24 := by
  constructor <;> norm_num [p24,Set.mem_Icc]
def p25 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(320905439051/125000000000:ℝ),(1/10:ℝ),(160452691833/62500000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates25 : LowOnlyStep.Gates p25 := by
  constructor <;> norm_num [p25,Set.mem_Icc]
def p26 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(160452691833/62500000000:ℝ),(1/10:ℝ),(160452671907/62500000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates26 : LowOnlyStep.Gates p26 := by
  constructor <;> norm_num [p26,Set.mem_Icc]
def p27 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(160452671907/62500000000:ℝ),(1/10:ℝ),(2567242521109/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates27 : LowOnlyStep.Gates p27 := by
  constructor <;> norm_num [p27,Set.mem_Icc]
def p28 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567242521109/1000000000000:ℝ),(1/10:ℝ),(2567242356043/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates28 : LowOnlyStep.Gates p28 := by
  constructor <;> norm_num [p28,Set.mem_Icc]
def p29 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567242356043/1000000000000:ℝ),(1/10:ℝ),(256724223727/100000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates29 : LowOnlyStep.Gates p29 := by
  constructor <;> norm_num [p29,Set.mem_Icc]
def p30 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(256724223727/100000000000:ℝ),(1/10:ℝ),(2567242151807/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates30 : LowOnlyStep.Gates p30 := by
  constructor <;> norm_num [p30,Set.mem_Icc]
def p31 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567242151807/1000000000000:ℝ),(1/10:ℝ),(2567242090313/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates31 : LowOnlyStep.Gates p31 := by
  constructor <;> norm_num [p31,Set.mem_Icc]
def p32 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567242090313/1000000000000:ℝ),(1/10:ℝ),(513448409213/200000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates32 : LowOnlyStep.Gates p32 := by
  constructor <;> norm_num [p32,Set.mem_Icc]
def p33 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(513448409213/200000000000:ℝ),(1/10:ℝ),(2567242014227/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates33 : LowOnlyStep.Gates p33 := by
  constructor <;> norm_num [p33,Set.mem_Icc]
def p34 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567242014227/1000000000000:ℝ),(1/10:ℝ),(1283620995659/500000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates34 : LowOnlyStep.Gates p34 := by
  constructor <;> norm_num [p34,Set.mem_Icc]
def p35 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(1283620995659/500000000000:ℝ),(1/10:ℝ),(1283620987417/500000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates35 : LowOnlyStep.Gates p35 := by
  constructor <;> norm_num [p35,Set.mem_Icc]
def p36 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(1283620987417/500000000000:ℝ),(1/10:ℝ),(2567241962973/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates36 : LowOnlyStep.Gates p36 := by
  constructor <;> norm_num [p36,Set.mem_Icc]
def p37 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567241962973/1000000000000:ℝ),(1/10:ℝ),(1283620977219/500000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates37 : LowOnlyStep.Gates p37 := by
  constructor <;> norm_num [p37,Set.mem_Icc]
def p38 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(1283620977219/500000000000:ℝ),(1/10:ℝ),(2567241948297/1000000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates38 : LowOnlyStep.Gates p38 := by
  constructor <;> norm_num [p38,Set.mem_Icc]
def p39 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(2567241948297/1000000000000:ℝ),(1/10:ℝ),(1283620971939/500000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates39 : LowOnlyStep.Gates p39 := by
  constructor <;> norm_num [p39,Set.mem_Icc]
def p40 : LowOnlyStep.Params := ⟨(99999/100000:ℝ),(1283620971939/500000000000:ℝ),(1/10:ℝ),(1283620970349/500000000000:ℝ),(1/10:ℝ),(373939/500000:ℝ),(3/25:ℝ)⟩
theorem gates40 : LowOnlyStep.Gates p40 := by
  constructor <;> norm_num [p40,Set.mem_Icc]
theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ (87393871/100000000:ℝ))
    (hseed : GlobalSource (99999/100000:ℝ) (5143/2000:ℝ) (1397/10000:ℝ)) :
    GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ) := by
  have hcut : 2*HeckeZeroSupremum.beta-1 < (373939/500000:ℝ) := by linarith
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
  exact h40
#print axioms source
end
end Qrh.JointDetector.LowRestartBank.First
