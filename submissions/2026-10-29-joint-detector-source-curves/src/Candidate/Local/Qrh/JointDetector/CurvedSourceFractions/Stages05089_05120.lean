/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05089_05120
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99012552088517,99012293520381,99012034928230,99011776312065,99011517671886,99011259007695,99011000319493,99010741607281,99010482871060,99010224110831,99009965326595,99009706518353,99009447686105,99009188829853,99008929949598,99008671045341,99008412117083,99008153164824,99007894188566,99007635188310,99007376164056,99007117115806,99006858043561,99006598947321,99006339827088,99006080682863,99005821514646,99005562322439,99005303106242,99005043866057,99004784601884,99004525313725,99004266001580]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5088+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5089 := params 0
abbrev ray5089 := rays 0
def bank5089 : Fin 2 → Cell := twoBank p5089 ray5089
theorem signs5089 : ∀ j, Signs p5089 (bank5089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5090 := params 1
abbrev ray5090 := rays 1
def bank5090 : Fin 2 → Cell := twoBank p5090 ray5090
theorem signs5090 : ∀ j, Signs p5090 (bank5090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5091 := params 2
abbrev ray5091 := rays 2
def bank5091 : Fin 2 → Cell := twoBank p5091 ray5091
theorem signs5091 : ∀ j, Signs p5091 (bank5091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5092 := params 3
abbrev ray5092 := rays 3
def bank5092 : Fin 2 → Cell := twoBank p5092 ray5092
theorem signs5092 : ∀ j, Signs p5092 (bank5092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5093 := params 4
abbrev ray5093 := rays 4
def bank5093 : Fin 2 → Cell := twoBank p5093 ray5093
theorem signs5093 : ∀ j, Signs p5093 (bank5093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5094 := params 5
abbrev ray5094 := rays 5
def bank5094 : Fin 2 → Cell := twoBank p5094 ray5094
theorem signs5094 : ∀ j, Signs p5094 (bank5094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5095 := params 6
abbrev ray5095 := rays 6
def bank5095 : Fin 2 → Cell := twoBank p5095 ray5095
theorem signs5095 : ∀ j, Signs p5095 (bank5095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5096 := params 7
abbrev ray5096 := rays 7
def bank5096 : Fin 2 → Cell := twoBank p5096 ray5096
theorem signs5096 : ∀ j, Signs p5096 (bank5096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5097 := params 8
abbrev ray5097 := rays 8
def bank5097 : Fin 2 → Cell := twoBank p5097 ray5097
theorem signs5097 : ∀ j, Signs p5097 (bank5097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5098 := params 9
abbrev ray5098 := rays 9
def bank5098 : Fin 2 → Cell := twoBank p5098 ray5098
theorem signs5098 : ∀ j, Signs p5098 (bank5098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5099 := params 10
abbrev ray5099 := rays 10
def bank5099 : Fin 2 → Cell := twoBank p5099 ray5099
theorem signs5099 : ∀ j, Signs p5099 (bank5099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5100 := params 11
abbrev ray5100 := rays 11
def bank5100 : Fin 2 → Cell := twoBank p5100 ray5100
theorem signs5100 : ∀ j, Signs p5100 (bank5100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5101 := params 12
abbrev ray5101 := rays 12
def bank5101 : Fin 2 → Cell := twoBank p5101 ray5101
theorem signs5101 : ∀ j, Signs p5101 (bank5101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5102 := params 13
abbrev ray5102 := rays 13
def bank5102 : Fin 2 → Cell := twoBank p5102 ray5102
theorem signs5102 : ∀ j, Signs p5102 (bank5102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5103 := params 14
abbrev ray5103 := rays 14
def bank5103 : Fin 2 → Cell := twoBank p5103 ray5103
theorem signs5103 : ∀ j, Signs p5103 (bank5103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5104 := params 15
abbrev ray5104 := rays 15
def bank5104 : Fin 2 → Cell := twoBank p5104 ray5104
theorem signs5104 : ∀ j, Signs p5104 (bank5104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5105 := params 16
abbrev ray5105 := rays 16
def bank5105 : Fin 2 → Cell := twoBank p5105 ray5105
theorem signs5105 : ∀ j, Signs p5105 (bank5105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5106 := params 17
abbrev ray5106 := rays 17
def bank5106 : Fin 2 → Cell := twoBank p5106 ray5106
theorem signs5106 : ∀ j, Signs p5106 (bank5106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5107 := params 18
abbrev ray5107 := rays 18
def bank5107 : Fin 2 → Cell := twoBank p5107 ray5107
theorem signs5107 : ∀ j, Signs p5107 (bank5107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5108 := params 19
abbrev ray5108 := rays 19
def bank5108 : Fin 2 → Cell := twoBank p5108 ray5108
theorem signs5108 : ∀ j, Signs p5108 (bank5108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5109 := params 20
abbrev ray5109 := rays 20
def bank5109 : Fin 2 → Cell := twoBank p5109 ray5109
theorem signs5109 : ∀ j, Signs p5109 (bank5109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5110 := params 21
abbrev ray5110 := rays 21
def bank5110 : Fin 2 → Cell := twoBank p5110 ray5110
theorem signs5110 : ∀ j, Signs p5110 (bank5110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5111 := params 22
abbrev ray5111 := rays 22
def bank5111 : Fin 2 → Cell := twoBank p5111 ray5111
theorem signs5111 : ∀ j, Signs p5111 (bank5111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5112 := params 23
abbrev ray5112 := rays 23
def bank5112 : Fin 2 → Cell := twoBank p5112 ray5112
theorem signs5112 : ∀ j, Signs p5112 (bank5112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5113 := params 24
abbrev ray5113 := rays 24
def bank5113 : Fin 2 → Cell := twoBank p5113 ray5113
theorem signs5113 : ∀ j, Signs p5113 (bank5113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5114 := params 25
abbrev ray5114 := rays 25
def bank5114 : Fin 2 → Cell := twoBank p5114 ray5114
theorem signs5114 : ∀ j, Signs p5114 (bank5114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5115 := params 26
abbrev ray5115 := rays 26
def bank5115 : Fin 2 → Cell := twoBank p5115 ray5115
theorem signs5115 : ∀ j, Signs p5115 (bank5115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5116 := params 27
abbrev ray5116 := rays 27
def bank5116 : Fin 2 → Cell := twoBank p5116 ray5116
theorem signs5116 : ∀ j, Signs p5116 (bank5116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5117 := params 28
abbrev ray5117 := rays 28
def bank5117 : Fin 2 → Cell := twoBank p5117 ray5117
theorem signs5117 : ∀ j, Signs p5117 (bank5117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5118 := params 29
abbrev ray5118 := rays 29
def bank5118 : Fin 2 → Cell := twoBank p5118 ray5118
theorem signs5118 : ∀ j, Signs p5118 (bank5118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5119 := params 30
abbrev ray5119 := rays 30
def bank5119 : Fin 2 → Cell := twoBank p5119 ray5119
theorem signs5119 : ∀ j, Signs p5119 (bank5119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5120 := params 31
abbrev ray5120 := rays 31
def bank5120 : Fin 2 → Cell := twoBank p5120 ray5120
theorem signs5120 : ∀ j, Signs p5120 (bank5120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05089_05120
