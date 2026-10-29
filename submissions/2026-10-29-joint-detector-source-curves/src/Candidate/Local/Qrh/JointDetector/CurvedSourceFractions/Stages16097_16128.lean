/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16097_16128
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94887446776273,94886971864866,94886496937470,94886021994085,94885547034711,94885072059348,94884597067996,94884122060655,94883647037326,94883171998008,94882696942701,94882221871405,94881746784121,94881271680848,94880796561586,94880321426336,94879846275097,94879371107869,94878895924653,94878420725448,94877945510255,94877470279073,94876995031903,94876519768745,94876044489598,94875569194463,94875093883340,94874618556228,94874143213128,94873667854040,94873192478964,94872717087900,94872241680847]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16096+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16097 := params 0
abbrev ray16097 := rays 0
def bank16097 : Fin 1 → Cell := oneBank p16097 ray16097
theorem signs16097 : ∀ j, Signs p16097 (bank16097 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16098 := params 1
abbrev ray16098 := rays 1
def bank16098 : Fin 1 → Cell := oneBank p16098 ray16098
theorem signs16098 : ∀ j, Signs p16098 (bank16098 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16099 := params 2
abbrev ray16099 := rays 2
def bank16099 : Fin 1 → Cell := oneBank p16099 ray16099
theorem signs16099 : ∀ j, Signs p16099 (bank16099 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16100 := params 3
abbrev ray16100 := rays 3
def bank16100 : Fin 1 → Cell := oneBank p16100 ray16100
theorem signs16100 : ∀ j, Signs p16100 (bank16100 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16101 := params 4
abbrev ray16101 := rays 4
def bank16101 : Fin 1 → Cell := oneBank p16101 ray16101
theorem signs16101 : ∀ j, Signs p16101 (bank16101 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16102 := params 5
abbrev ray16102 := rays 5
def bank16102 : Fin 1 → Cell := oneBank p16102 ray16102
theorem signs16102 : ∀ j, Signs p16102 (bank16102 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16103 := params 6
abbrev ray16103 := rays 6
def bank16103 : Fin 1 → Cell := oneBank p16103 ray16103
theorem signs16103 : ∀ j, Signs p16103 (bank16103 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16104 := params 7
abbrev ray16104 := rays 7
def bank16104 : Fin 1 → Cell := oneBank p16104 ray16104
theorem signs16104 : ∀ j, Signs p16104 (bank16104 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16105 := params 8
abbrev ray16105 := rays 8
def bank16105 : Fin 1 → Cell := oneBank p16105 ray16105
theorem signs16105 : ∀ j, Signs p16105 (bank16105 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16106 := params 9
abbrev ray16106 := rays 9
def bank16106 : Fin 1 → Cell := oneBank p16106 ray16106
theorem signs16106 : ∀ j, Signs p16106 (bank16106 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16107 := params 10
abbrev ray16107 := rays 10
def bank16107 : Fin 1 → Cell := oneBank p16107 ray16107
theorem signs16107 : ∀ j, Signs p16107 (bank16107 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16108 := params 11
abbrev ray16108 := rays 11
def bank16108 : Fin 1 → Cell := oneBank p16108 ray16108
theorem signs16108 : ∀ j, Signs p16108 (bank16108 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16109 := params 12
abbrev ray16109 := rays 12
def bank16109 : Fin 1 → Cell := oneBank p16109 ray16109
theorem signs16109 : ∀ j, Signs p16109 (bank16109 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16110 := params 13
abbrev ray16110 := rays 13
def bank16110 : Fin 1 → Cell := oneBank p16110 ray16110
theorem signs16110 : ∀ j, Signs p16110 (bank16110 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16111 := params 14
abbrev ray16111 := rays 14
def bank16111 : Fin 1 → Cell := oneBank p16111 ray16111
theorem signs16111 : ∀ j, Signs p16111 (bank16111 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16112 := params 15
abbrev ray16112 := rays 15
def bank16112 : Fin 1 → Cell := oneBank p16112 ray16112
theorem signs16112 : ∀ j, Signs p16112 (bank16112 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16113 := params 16
abbrev ray16113 := rays 16
def bank16113 : Fin 1 → Cell := oneBank p16113 ray16113
theorem signs16113 : ∀ j, Signs p16113 (bank16113 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16114 := params 17
abbrev ray16114 := rays 17
def bank16114 : Fin 1 → Cell := oneBank p16114 ray16114
theorem signs16114 : ∀ j, Signs p16114 (bank16114 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16115 := params 18
abbrev ray16115 := rays 18
def bank16115 : Fin 1 → Cell := oneBank p16115 ray16115
theorem signs16115 : ∀ j, Signs p16115 (bank16115 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16116 := params 19
abbrev ray16116 := rays 19
def bank16116 : Fin 1 → Cell := oneBank p16116 ray16116
theorem signs16116 : ∀ j, Signs p16116 (bank16116 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16117 := params 20
abbrev ray16117 := rays 20
def bank16117 : Fin 1 → Cell := oneBank p16117 ray16117
theorem signs16117 : ∀ j, Signs p16117 (bank16117 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16118 := params 21
abbrev ray16118 := rays 21
def bank16118 : Fin 1 → Cell := oneBank p16118 ray16118
theorem signs16118 : ∀ j, Signs p16118 (bank16118 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16119 := params 22
abbrev ray16119 := rays 22
def bank16119 : Fin 1 → Cell := oneBank p16119 ray16119
theorem signs16119 : ∀ j, Signs p16119 (bank16119 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16120 := params 23
abbrev ray16120 := rays 23
def bank16120 : Fin 1 → Cell := oneBank p16120 ray16120
theorem signs16120 : ∀ j, Signs p16120 (bank16120 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16121 := params 24
abbrev ray16121 := rays 24
def bank16121 : Fin 1 → Cell := oneBank p16121 ray16121
theorem signs16121 : ∀ j, Signs p16121 (bank16121 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16122 := params 25
abbrev ray16122 := rays 25
def bank16122 : Fin 1 → Cell := oneBank p16122 ray16122
theorem signs16122 : ∀ j, Signs p16122 (bank16122 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16123 := params 26
abbrev ray16123 := rays 26
def bank16123 : Fin 1 → Cell := oneBank p16123 ray16123
theorem signs16123 : ∀ j, Signs p16123 (bank16123 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16124 := params 27
abbrev ray16124 := rays 27
def bank16124 : Fin 1 → Cell := oneBank p16124 ray16124
theorem signs16124 : ∀ j, Signs p16124 (bank16124 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16125 := params 28
abbrev ray16125 := rays 28
def bank16125 : Fin 1 → Cell := oneBank p16125 ray16125
theorem signs16125 : ∀ j, Signs p16125 (bank16125 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16126 := params 29
abbrev ray16126 := rays 29
def bank16126 : Fin 1 → Cell := oneBank p16126 ray16126
theorem signs16126 : ∀ j, Signs p16126 (bank16126 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16127 := params 30
abbrev ray16127 := rays 30
def bank16127 : Fin 1 → Cell := oneBank p16127 ray16127
theorem signs16127 : ∀ j, Signs p16127 (bank16127 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16128 := params 31
abbrev ray16128 := rays 31
def bank16128 : Fin 1 → Cell := oneBank p16128 ray16128
theorem signs16128 : ∀ j, Signs p16128 (bank16128 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16097_16128
