/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16033_16064
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94917807847847,94917333959799,94916860055760,94916386135730,94915912199709,94915438247697,94914964279694,94914490295701,94914016295717,94913542279742,94913068247776,94912594199820,94912120135873,94911646055935,94911171960007,94910697848088,94910223720178,94909749576278,94909275416388,94908801240507,94908327048636,94907852840774,94907378616922,94906904377080,94906430121247,94905955849424,94905481561611,94905007257808,94904532938015,94904058602231,94903584250457,94903109882693,94902635498939]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16032+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16033 := params 0
abbrev ray16033 := rays 0
def bank16033 : Fin 1 → Cell := oneBank p16033 ray16033
theorem signs16033 : ∀ j, Signs p16033 (bank16033 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16034 := params 1
abbrev ray16034 := rays 1
def bank16034 : Fin 1 → Cell := oneBank p16034 ray16034
theorem signs16034 : ∀ j, Signs p16034 (bank16034 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16035 := params 2
abbrev ray16035 := rays 2
def bank16035 : Fin 1 → Cell := oneBank p16035 ray16035
theorem signs16035 : ∀ j, Signs p16035 (bank16035 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16036 := params 3
abbrev ray16036 := rays 3
def bank16036 : Fin 1 → Cell := oneBank p16036 ray16036
theorem signs16036 : ∀ j, Signs p16036 (bank16036 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16037 := params 4
abbrev ray16037 := rays 4
def bank16037 : Fin 1 → Cell := oneBank p16037 ray16037
theorem signs16037 : ∀ j, Signs p16037 (bank16037 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16038 := params 5
abbrev ray16038 := rays 5
def bank16038 : Fin 1 → Cell := oneBank p16038 ray16038
theorem signs16038 : ∀ j, Signs p16038 (bank16038 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16039 := params 6
abbrev ray16039 := rays 6
def bank16039 : Fin 1 → Cell := oneBank p16039 ray16039
theorem signs16039 : ∀ j, Signs p16039 (bank16039 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16040 := params 7
abbrev ray16040 := rays 7
def bank16040 : Fin 1 → Cell := oneBank p16040 ray16040
theorem signs16040 : ∀ j, Signs p16040 (bank16040 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16041 := params 8
abbrev ray16041 := rays 8
def bank16041 : Fin 1 → Cell := oneBank p16041 ray16041
theorem signs16041 : ∀ j, Signs p16041 (bank16041 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16042 := params 9
abbrev ray16042 := rays 9
def bank16042 : Fin 1 → Cell := oneBank p16042 ray16042
theorem signs16042 : ∀ j, Signs p16042 (bank16042 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16043 := params 10
abbrev ray16043 := rays 10
def bank16043 : Fin 1 → Cell := oneBank p16043 ray16043
theorem signs16043 : ∀ j, Signs p16043 (bank16043 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16044 := params 11
abbrev ray16044 := rays 11
def bank16044 : Fin 1 → Cell := oneBank p16044 ray16044
theorem signs16044 : ∀ j, Signs p16044 (bank16044 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16045 := params 12
abbrev ray16045 := rays 12
def bank16045 : Fin 1 → Cell := oneBank p16045 ray16045
theorem signs16045 : ∀ j, Signs p16045 (bank16045 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16046 := params 13
abbrev ray16046 := rays 13
def bank16046 : Fin 1 → Cell := oneBank p16046 ray16046
theorem signs16046 : ∀ j, Signs p16046 (bank16046 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16047 := params 14
abbrev ray16047 := rays 14
def bank16047 : Fin 1 → Cell := oneBank p16047 ray16047
theorem signs16047 : ∀ j, Signs p16047 (bank16047 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16048 := params 15
abbrev ray16048 := rays 15
def bank16048 : Fin 1 → Cell := oneBank p16048 ray16048
theorem signs16048 : ∀ j, Signs p16048 (bank16048 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16049 := params 16
abbrev ray16049 := rays 16
def bank16049 : Fin 1 → Cell := oneBank p16049 ray16049
theorem signs16049 : ∀ j, Signs p16049 (bank16049 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16050 := params 17
abbrev ray16050 := rays 17
def bank16050 : Fin 1 → Cell := oneBank p16050 ray16050
theorem signs16050 : ∀ j, Signs p16050 (bank16050 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16051 := params 18
abbrev ray16051 := rays 18
def bank16051 : Fin 1 → Cell := oneBank p16051 ray16051
theorem signs16051 : ∀ j, Signs p16051 (bank16051 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16052 := params 19
abbrev ray16052 := rays 19
def bank16052 : Fin 1 → Cell := oneBank p16052 ray16052
theorem signs16052 : ∀ j, Signs p16052 (bank16052 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16053 := params 20
abbrev ray16053 := rays 20
def bank16053 : Fin 1 → Cell := oneBank p16053 ray16053
theorem signs16053 : ∀ j, Signs p16053 (bank16053 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16054 := params 21
abbrev ray16054 := rays 21
def bank16054 : Fin 1 → Cell := oneBank p16054 ray16054
theorem signs16054 : ∀ j, Signs p16054 (bank16054 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16055 := params 22
abbrev ray16055 := rays 22
def bank16055 : Fin 1 → Cell := oneBank p16055 ray16055
theorem signs16055 : ∀ j, Signs p16055 (bank16055 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16056 := params 23
abbrev ray16056 := rays 23
def bank16056 : Fin 1 → Cell := oneBank p16056 ray16056
theorem signs16056 : ∀ j, Signs p16056 (bank16056 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16057 := params 24
abbrev ray16057 := rays 24
def bank16057 : Fin 1 → Cell := oneBank p16057 ray16057
theorem signs16057 : ∀ j, Signs p16057 (bank16057 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16058 := params 25
abbrev ray16058 := rays 25
def bank16058 : Fin 1 → Cell := oneBank p16058 ray16058
theorem signs16058 : ∀ j, Signs p16058 (bank16058 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16059 := params 26
abbrev ray16059 := rays 26
def bank16059 : Fin 1 → Cell := oneBank p16059 ray16059
theorem signs16059 : ∀ j, Signs p16059 (bank16059 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16060 := params 27
abbrev ray16060 := rays 27
def bank16060 : Fin 1 → Cell := oneBank p16060 ray16060
theorem signs16060 : ∀ j, Signs p16060 (bank16060 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16061 := params 28
abbrev ray16061 := rays 28
def bank16061 : Fin 1 → Cell := oneBank p16061 ray16061
theorem signs16061 : ∀ j, Signs p16061 (bank16061 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16062 := params 29
abbrev ray16062 := rays 29
def bank16062 : Fin 1 → Cell := oneBank p16062 ray16062
theorem signs16062 : ∀ j, Signs p16062 (bank16062 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16063 := params 30
abbrev ray16063 := rays 30
def bank16063 : Fin 1 → Cell := oneBank p16063 ray16063
theorem signs16063 : ∀ j, Signs p16063 (bank16063 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16064 := params 31
abbrev ray16064 := rays 31
def bank16064 : Fin 1 → Cell := oneBank p16064 ray16064
theorem signs16064 : ∀ j, Signs p16064 (bank16064 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16033_16064
