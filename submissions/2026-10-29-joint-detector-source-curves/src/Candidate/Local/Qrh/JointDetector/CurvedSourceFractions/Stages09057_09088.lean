/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09057_09088
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97806702786890,97806355605050,97806008402321,97805661178703,97805313934196,97804966668802,97804619382520,97804272075352,97803924747298,97803577398359,97803230028535,97802882637827,97802535226236,97802187793762,97801840340405,97801492866167,97801145371048,97800797855049,97800450318170,97800102760412,97799755181775,97799407582260,97799059961868,97798712320599,97798364658454,97798016975434,97797669271539,97797321546770,97796973801128,97796626034613,97796278247225,97795930438966,97795582609836]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9056+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9057 := params 0
abbrev ray9057 := rays 0
def bank9057 : Fin 2 → Cell := twoBank p9057 ray9057
theorem signs9057 : ∀ j, Signs p9057 (bank9057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9058 := params 1
abbrev ray9058 := rays 1
def bank9058 : Fin 2 → Cell := twoBank p9058 ray9058
theorem signs9058 : ∀ j, Signs p9058 (bank9058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9059 := params 2
abbrev ray9059 := rays 2
def bank9059 : Fin 2 → Cell := twoBank p9059 ray9059
theorem signs9059 : ∀ j, Signs p9059 (bank9059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9060 := params 3
abbrev ray9060 := rays 3
def bank9060 : Fin 2 → Cell := twoBank p9060 ray9060
theorem signs9060 : ∀ j, Signs p9060 (bank9060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9061 := params 4
abbrev ray9061 := rays 4
def bank9061 : Fin 2 → Cell := twoBank p9061 ray9061
theorem signs9061 : ∀ j, Signs p9061 (bank9061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9062 := params 5
abbrev ray9062 := rays 5
def bank9062 : Fin 2 → Cell := twoBank p9062 ray9062
theorem signs9062 : ∀ j, Signs p9062 (bank9062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9063 := params 6
abbrev ray9063 := rays 6
def bank9063 : Fin 2 → Cell := twoBank p9063 ray9063
theorem signs9063 : ∀ j, Signs p9063 (bank9063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9064 := params 7
abbrev ray9064 := rays 7
def bank9064 : Fin 2 → Cell := twoBank p9064 ray9064
theorem signs9064 : ∀ j, Signs p9064 (bank9064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9065 := params 8
abbrev ray9065 := rays 8
def bank9065 : Fin 2 → Cell := twoBank p9065 ray9065
theorem signs9065 : ∀ j, Signs p9065 (bank9065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9066 := params 9
abbrev ray9066 := rays 9
def bank9066 : Fin 2 → Cell := twoBank p9066 ray9066
theorem signs9066 : ∀ j, Signs p9066 (bank9066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9067 := params 10
abbrev ray9067 := rays 10
def bank9067 : Fin 2 → Cell := twoBank p9067 ray9067
theorem signs9067 : ∀ j, Signs p9067 (bank9067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9068 := params 11
abbrev ray9068 := rays 11
def bank9068 : Fin 2 → Cell := twoBank p9068 ray9068
theorem signs9068 : ∀ j, Signs p9068 (bank9068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9069 := params 12
abbrev ray9069 := rays 12
def bank9069 : Fin 2 → Cell := twoBank p9069 ray9069
theorem signs9069 : ∀ j, Signs p9069 (bank9069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9070 := params 13
abbrev ray9070 := rays 13
def bank9070 : Fin 2 → Cell := twoBank p9070 ray9070
theorem signs9070 : ∀ j, Signs p9070 (bank9070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9071 := params 14
abbrev ray9071 := rays 14
def bank9071 : Fin 2 → Cell := twoBank p9071 ray9071
theorem signs9071 : ∀ j, Signs p9071 (bank9071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9072 := params 15
abbrev ray9072 := rays 15
def bank9072 : Fin 2 → Cell := twoBank p9072 ray9072
theorem signs9072 : ∀ j, Signs p9072 (bank9072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9073 := params 16
abbrev ray9073 := rays 16
def bank9073 : Fin 2 → Cell := twoBank p9073 ray9073
theorem signs9073 : ∀ j, Signs p9073 (bank9073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9074 := params 17
abbrev ray9074 := rays 17
def bank9074 : Fin 2 → Cell := twoBank p9074 ray9074
theorem signs9074 : ∀ j, Signs p9074 (bank9074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9075 := params 18
abbrev ray9075 := rays 18
def bank9075 : Fin 2 → Cell := twoBank p9075 ray9075
theorem signs9075 : ∀ j, Signs p9075 (bank9075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9076 := params 19
abbrev ray9076 := rays 19
def bank9076 : Fin 2 → Cell := twoBank p9076 ray9076
theorem signs9076 : ∀ j, Signs p9076 (bank9076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9077 := params 20
abbrev ray9077 := rays 20
def bank9077 : Fin 2 → Cell := twoBank p9077 ray9077
theorem signs9077 : ∀ j, Signs p9077 (bank9077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9078 := params 21
abbrev ray9078 := rays 21
def bank9078 : Fin 2 → Cell := twoBank p9078 ray9078
theorem signs9078 : ∀ j, Signs p9078 (bank9078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9079 := params 22
abbrev ray9079 := rays 22
def bank9079 : Fin 2 → Cell := twoBank p9079 ray9079
theorem signs9079 : ∀ j, Signs p9079 (bank9079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9080 := params 23
abbrev ray9080 := rays 23
def bank9080 : Fin 2 → Cell := twoBank p9080 ray9080
theorem signs9080 : ∀ j, Signs p9080 (bank9080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9081 := params 24
abbrev ray9081 := rays 24
def bank9081 : Fin 2 → Cell := twoBank p9081 ray9081
theorem signs9081 : ∀ j, Signs p9081 (bank9081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9082 := params 25
abbrev ray9082 := rays 25
def bank9082 : Fin 2 → Cell := twoBank p9082 ray9082
theorem signs9082 : ∀ j, Signs p9082 (bank9082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9083 := params 26
abbrev ray9083 := rays 26
def bank9083 : Fin 2 → Cell := twoBank p9083 ray9083
theorem signs9083 : ∀ j, Signs p9083 (bank9083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9084 := params 27
abbrev ray9084 := rays 27
def bank9084 : Fin 2 → Cell := twoBank p9084 ray9084
theorem signs9084 : ∀ j, Signs p9084 (bank9084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9085 := params 28
abbrev ray9085 := rays 28
def bank9085 : Fin 2 → Cell := twoBank p9085 ray9085
theorem signs9085 : ∀ j, Signs p9085 (bank9085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9086 := params 29
abbrev ray9086 := rays 29
def bank9086 : Fin 2 → Cell := twoBank p9086 ray9086
theorem signs9086 : ∀ j, Signs p9086 (bank9086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9087 := params 30
abbrev ray9087 := rays 30
def bank9087 : Fin 2 → Cell := twoBank p9087 ray9087
theorem signs9087 : ∀ j, Signs p9087 (bank9087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9088 := params 31
abbrev ray9088 := rays 31
def bank9088 : Fin 2 → Cell := twoBank p9088 ray9088
theorem signs9088 : ∀ j, Signs p9088 (bank9088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09057_09088
