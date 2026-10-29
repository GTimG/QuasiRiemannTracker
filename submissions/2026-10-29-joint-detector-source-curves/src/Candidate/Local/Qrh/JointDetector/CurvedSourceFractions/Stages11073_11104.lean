/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11073_11104
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97065150824713,97064762692074,97064374539654,97063986367454,97063598175475,97063209963717,97062821732181,97062433480867,97062045209775,97061656918907,97061268608262,97060880277841,97060491927645,97060103557674,97059715167928,97059326758408,97058938329115,97058549880049,97058161411210,97057772922599,97057384414216,97056995886062,97056607338138,97056218770443,97055830182979,97055441575746,97055052948744,97054664301974,97054275635436,97053886949131,97053498243059,97053109517221,97052720771617]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11072+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11073 := params 0
abbrev ray11073 := rays 0
def bank11073 : Fin 2 → Cell := twoBank p11073 ray11073
theorem signs11073 : ∀ j, Signs p11073 (bank11073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11074 := params 1
abbrev ray11074 := rays 1
def bank11074 : Fin 2 → Cell := twoBank p11074 ray11074
theorem signs11074 : ∀ j, Signs p11074 (bank11074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11075 := params 2
abbrev ray11075 := rays 2
def bank11075 : Fin 2 → Cell := twoBank p11075 ray11075
theorem signs11075 : ∀ j, Signs p11075 (bank11075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11076 := params 3
abbrev ray11076 := rays 3
def bank11076 : Fin 2 → Cell := twoBank p11076 ray11076
theorem signs11076 : ∀ j, Signs p11076 (bank11076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11077 := params 4
abbrev ray11077 := rays 4
def bank11077 : Fin 2 → Cell := twoBank p11077 ray11077
theorem signs11077 : ∀ j, Signs p11077 (bank11077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11078 := params 5
abbrev ray11078 := rays 5
def bank11078 : Fin 2 → Cell := twoBank p11078 ray11078
theorem signs11078 : ∀ j, Signs p11078 (bank11078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11079 := params 6
abbrev ray11079 := rays 6
def bank11079 : Fin 2 → Cell := twoBank p11079 ray11079
theorem signs11079 : ∀ j, Signs p11079 (bank11079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11080 := params 7
abbrev ray11080 := rays 7
def bank11080 : Fin 2 → Cell := twoBank p11080 ray11080
theorem signs11080 : ∀ j, Signs p11080 (bank11080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11081 := params 8
abbrev ray11081 := rays 8
def bank11081 : Fin 2 → Cell := twoBank p11081 ray11081
theorem signs11081 : ∀ j, Signs p11081 (bank11081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11082 := params 9
abbrev ray11082 := rays 9
def bank11082 : Fin 2 → Cell := twoBank p11082 ray11082
theorem signs11082 : ∀ j, Signs p11082 (bank11082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11083 := params 10
abbrev ray11083 := rays 10
def bank11083 : Fin 2 → Cell := twoBank p11083 ray11083
theorem signs11083 : ∀ j, Signs p11083 (bank11083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11084 := params 11
abbrev ray11084 := rays 11
def bank11084 : Fin 2 → Cell := twoBank p11084 ray11084
theorem signs11084 : ∀ j, Signs p11084 (bank11084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11085 := params 12
abbrev ray11085 := rays 12
def bank11085 : Fin 2 → Cell := twoBank p11085 ray11085
theorem signs11085 : ∀ j, Signs p11085 (bank11085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11086 := params 13
abbrev ray11086 := rays 13
def bank11086 : Fin 2 → Cell := twoBank p11086 ray11086
theorem signs11086 : ∀ j, Signs p11086 (bank11086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11087 := params 14
abbrev ray11087 := rays 14
def bank11087 : Fin 2 → Cell := twoBank p11087 ray11087
theorem signs11087 : ∀ j, Signs p11087 (bank11087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11088 := params 15
abbrev ray11088 := rays 15
def bank11088 : Fin 2 → Cell := twoBank p11088 ray11088
theorem signs11088 : ∀ j, Signs p11088 (bank11088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11089 := params 16
abbrev ray11089 := rays 16
def bank11089 : Fin 2 → Cell := twoBank p11089 ray11089
theorem signs11089 : ∀ j, Signs p11089 (bank11089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11090 := params 17
abbrev ray11090 := rays 17
def bank11090 : Fin 2 → Cell := twoBank p11090 ray11090
theorem signs11090 : ∀ j, Signs p11090 (bank11090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11091 := params 18
abbrev ray11091 := rays 18
def bank11091 : Fin 2 → Cell := twoBank p11091 ray11091
theorem signs11091 : ∀ j, Signs p11091 (bank11091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11092 := params 19
abbrev ray11092 := rays 19
def bank11092 : Fin 2 → Cell := twoBank p11092 ray11092
theorem signs11092 : ∀ j, Signs p11092 (bank11092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11093 := params 20
abbrev ray11093 := rays 20
def bank11093 : Fin 2 → Cell := twoBank p11093 ray11093
theorem signs11093 : ∀ j, Signs p11093 (bank11093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11094 := params 21
abbrev ray11094 := rays 21
def bank11094 : Fin 2 → Cell := twoBank p11094 ray11094
theorem signs11094 : ∀ j, Signs p11094 (bank11094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11095 := params 22
abbrev ray11095 := rays 22
def bank11095 : Fin 2 → Cell := twoBank p11095 ray11095
theorem signs11095 : ∀ j, Signs p11095 (bank11095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11096 := params 23
abbrev ray11096 := rays 23
def bank11096 : Fin 2 → Cell := twoBank p11096 ray11096
theorem signs11096 : ∀ j, Signs p11096 (bank11096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11097 := params 24
abbrev ray11097 := rays 24
def bank11097 : Fin 2 → Cell := twoBank p11097 ray11097
theorem signs11097 : ∀ j, Signs p11097 (bank11097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11098 := params 25
abbrev ray11098 := rays 25
def bank11098 : Fin 2 → Cell := twoBank p11098 ray11098
theorem signs11098 : ∀ j, Signs p11098 (bank11098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11099 := params 26
abbrev ray11099 := rays 26
def bank11099 : Fin 2 → Cell := twoBank p11099 ray11099
theorem signs11099 : ∀ j, Signs p11099 (bank11099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11100 := params 27
abbrev ray11100 := rays 27
def bank11100 : Fin 2 → Cell := twoBank p11100 ray11100
theorem signs11100 : ∀ j, Signs p11100 (bank11100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11101 := params 28
abbrev ray11101 := rays 28
def bank11101 : Fin 2 → Cell := twoBank p11101 ray11101
theorem signs11101 : ∀ j, Signs p11101 (bank11101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11102 := params 29
abbrev ray11102 := rays 29
def bank11102 : Fin 2 → Cell := twoBank p11102 ray11102
theorem signs11102 : ∀ j, Signs p11102 (bank11102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11103 := params 30
abbrev ray11103 := rays 30
def bank11103 : Fin 2 → Cell := twoBank p11103 ray11103
theorem signs11103 : ∀ j, Signs p11103 (bank11103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11104 := params 31
abbrev ray11104 := rays 31
def bank11104 : Fin 2 → Cell := twoBank p11104 ray11104
theorem signs11104 : ∀ j, Signs p11104 (bank11104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11073_11104
