/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15041_15072
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95380020203865,95379562207791,95379104195656,95378646167460,95378188123202,95377730062883,95377271986503,95376813894063,95376355785562,95375897661000,95375439520378,95374981363695,95374523190952,95374065002149,95373606797285,95373148576361,95372690339378,95372232086335,95371773817232,95371315532069,95370857230847,95370398913566,95369940580225,95369482230825,95369023865366,95368565483848,95368107086271,95367648672636,95367190242942,95366731797189,95366273335378,95365814857509,95365356363582]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15040+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15041 := params 0
abbrev ray15041 := rays 0
def bank15041 : Fin 1 → Cell := oneBank p15041 ray15041
theorem signs15041 : ∀ j, Signs p15041 (bank15041 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15042 := params 1
abbrev ray15042 := rays 1
def bank15042 : Fin 1 → Cell := oneBank p15042 ray15042
theorem signs15042 : ∀ j, Signs p15042 (bank15042 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15043 := params 2
abbrev ray15043 := rays 2
def bank15043 : Fin 1 → Cell := oneBank p15043 ray15043
theorem signs15043 : ∀ j, Signs p15043 (bank15043 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15044 := params 3
abbrev ray15044 := rays 3
def bank15044 : Fin 1 → Cell := oneBank p15044 ray15044
theorem signs15044 : ∀ j, Signs p15044 (bank15044 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15045 := params 4
abbrev ray15045 := rays 4
def bank15045 : Fin 1 → Cell := oneBank p15045 ray15045
theorem signs15045 : ∀ j, Signs p15045 (bank15045 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15046 := params 5
abbrev ray15046 := rays 5
def bank15046 : Fin 1 → Cell := oneBank p15046 ray15046
theorem signs15046 : ∀ j, Signs p15046 (bank15046 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15047 := params 6
abbrev ray15047 := rays 6
def bank15047 : Fin 1 → Cell := oneBank p15047 ray15047
theorem signs15047 : ∀ j, Signs p15047 (bank15047 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15048 := params 7
abbrev ray15048 := rays 7
def bank15048 : Fin 1 → Cell := oneBank p15048 ray15048
theorem signs15048 : ∀ j, Signs p15048 (bank15048 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15049 := params 8
abbrev ray15049 := rays 8
def bank15049 : Fin 1 → Cell := oneBank p15049 ray15049
theorem signs15049 : ∀ j, Signs p15049 (bank15049 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15050 := params 9
abbrev ray15050 := rays 9
def bank15050 : Fin 1 → Cell := oneBank p15050 ray15050
theorem signs15050 : ∀ j, Signs p15050 (bank15050 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15051 := params 10
abbrev ray15051 := rays 10
def bank15051 : Fin 1 → Cell := oneBank p15051 ray15051
theorem signs15051 : ∀ j, Signs p15051 (bank15051 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15052 := params 11
abbrev ray15052 := rays 11
def bank15052 : Fin 1 → Cell := oneBank p15052 ray15052
theorem signs15052 : ∀ j, Signs p15052 (bank15052 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15053 := params 12
abbrev ray15053 := rays 12
def bank15053 : Fin 1 → Cell := oneBank p15053 ray15053
theorem signs15053 : ∀ j, Signs p15053 (bank15053 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15054 := params 13
abbrev ray15054 := rays 13
def bank15054 : Fin 1 → Cell := oneBank p15054 ray15054
theorem signs15054 : ∀ j, Signs p15054 (bank15054 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15055 := params 14
abbrev ray15055 := rays 14
def bank15055 : Fin 1 → Cell := oneBank p15055 ray15055
theorem signs15055 : ∀ j, Signs p15055 (bank15055 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15056 := params 15
abbrev ray15056 := rays 15
def bank15056 : Fin 1 → Cell := oneBank p15056 ray15056
theorem signs15056 : ∀ j, Signs p15056 (bank15056 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15057 := params 16
abbrev ray15057 := rays 16
def bank15057 : Fin 1 → Cell := oneBank p15057 ray15057
theorem signs15057 : ∀ j, Signs p15057 (bank15057 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15058 := params 17
abbrev ray15058 := rays 17
def bank15058 : Fin 1 → Cell := oneBank p15058 ray15058
theorem signs15058 : ∀ j, Signs p15058 (bank15058 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15059 := params 18
abbrev ray15059 := rays 18
def bank15059 : Fin 1 → Cell := oneBank p15059 ray15059
theorem signs15059 : ∀ j, Signs p15059 (bank15059 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15060 := params 19
abbrev ray15060 := rays 19
def bank15060 : Fin 1 → Cell := oneBank p15060 ray15060
theorem signs15060 : ∀ j, Signs p15060 (bank15060 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15061 := params 20
abbrev ray15061 := rays 20
def bank15061 : Fin 1 → Cell := oneBank p15061 ray15061
theorem signs15061 : ∀ j, Signs p15061 (bank15061 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15062 := params 21
abbrev ray15062 := rays 21
def bank15062 : Fin 1 → Cell := oneBank p15062 ray15062
theorem signs15062 : ∀ j, Signs p15062 (bank15062 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15063 := params 22
abbrev ray15063 := rays 22
def bank15063 : Fin 1 → Cell := oneBank p15063 ray15063
theorem signs15063 : ∀ j, Signs p15063 (bank15063 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15064 := params 23
abbrev ray15064 := rays 23
def bank15064 : Fin 1 → Cell := oneBank p15064 ray15064
theorem signs15064 : ∀ j, Signs p15064 (bank15064 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15065 := params 24
abbrev ray15065 := rays 24
def bank15065 : Fin 1 → Cell := oneBank p15065 ray15065
theorem signs15065 : ∀ j, Signs p15065 (bank15065 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15066 := params 25
abbrev ray15066 := rays 25
def bank15066 : Fin 1 → Cell := oneBank p15066 ray15066
theorem signs15066 : ∀ j, Signs p15066 (bank15066 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15067 := params 26
abbrev ray15067 := rays 26
def bank15067 : Fin 1 → Cell := oneBank p15067 ray15067
theorem signs15067 : ∀ j, Signs p15067 (bank15067 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15068 := params 27
abbrev ray15068 := rays 27
def bank15068 : Fin 1 → Cell := oneBank p15068 ray15068
theorem signs15068 : ∀ j, Signs p15068 (bank15068 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15069 := params 28
abbrev ray15069 := rays 28
def bank15069 : Fin 1 → Cell := oneBank p15069 ray15069
theorem signs15069 : ∀ j, Signs p15069 (bank15069 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15070 := params 29
abbrev ray15070 := rays 29
def bank15070 : Fin 1 → Cell := oneBank p15070 ray15070
theorem signs15070 : ∀ j, Signs p15070 (bank15070 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15071 := params 30
abbrev ray15071 := rays 30
def bank15071 : Fin 1 → Cell := oneBank p15071 ray15071
theorem signs15071 : ∀ j, Signs p15071 (bank15071 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15072 := params 31
abbrev ray15072 := rays 31
def bank15072 : Fin 1 → Cell := oneBank p15072 ray15072
theorem signs15072 : ∀ j, Signs p15072 (bank15072 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15041_15072
