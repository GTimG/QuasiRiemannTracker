/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06113_06144
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98735370522395,98735087858957,98734805172455,98734522462889,98734239730260,98733956974570,98733674195819,98733391394008,98733108569137,98732825721208,98732542850222,98732259956179,98731977039080,98731694098927,98731411135720,98731128149460,98730845140147,98730562107783,98730279052369,98729995973905,98729712872392,98729429747831,98729146600223,98728863429569,98728580235870,98728297019127,98728013779340,98727730516511,98727447230640,98727163921728,98726880589776,98726597234785,98726313856756]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6112+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6113 := params 0
abbrev ray6113 := rays 0
def bank6113 : Fin 2 → Cell := twoBank p6113 ray6113
theorem signs6113 : ∀ j, Signs p6113 (bank6113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6114 := params 1
abbrev ray6114 := rays 1
def bank6114 : Fin 2 → Cell := twoBank p6114 ray6114
theorem signs6114 : ∀ j, Signs p6114 (bank6114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6115 := params 2
abbrev ray6115 := rays 2
def bank6115 : Fin 2 → Cell := twoBank p6115 ray6115
theorem signs6115 : ∀ j, Signs p6115 (bank6115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6116 := params 3
abbrev ray6116 := rays 3
def bank6116 : Fin 2 → Cell := twoBank p6116 ray6116
theorem signs6116 : ∀ j, Signs p6116 (bank6116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6117 := params 4
abbrev ray6117 := rays 4
def bank6117 : Fin 2 → Cell := twoBank p6117 ray6117
theorem signs6117 : ∀ j, Signs p6117 (bank6117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6118 := params 5
abbrev ray6118 := rays 5
def bank6118 : Fin 2 → Cell := twoBank p6118 ray6118
theorem signs6118 : ∀ j, Signs p6118 (bank6118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6119 := params 6
abbrev ray6119 := rays 6
def bank6119 : Fin 2 → Cell := twoBank p6119 ray6119
theorem signs6119 : ∀ j, Signs p6119 (bank6119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6120 := params 7
abbrev ray6120 := rays 7
def bank6120 : Fin 2 → Cell := twoBank p6120 ray6120
theorem signs6120 : ∀ j, Signs p6120 (bank6120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6121 := params 8
abbrev ray6121 := rays 8
def bank6121 : Fin 2 → Cell := twoBank p6121 ray6121
theorem signs6121 : ∀ j, Signs p6121 (bank6121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6122 := params 9
abbrev ray6122 := rays 9
def bank6122 : Fin 2 → Cell := twoBank p6122 ray6122
theorem signs6122 : ∀ j, Signs p6122 (bank6122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6123 := params 10
abbrev ray6123 := rays 10
def bank6123 : Fin 2 → Cell := twoBank p6123 ray6123
theorem signs6123 : ∀ j, Signs p6123 (bank6123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6124 := params 11
abbrev ray6124 := rays 11
def bank6124 : Fin 2 → Cell := twoBank p6124 ray6124
theorem signs6124 : ∀ j, Signs p6124 (bank6124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6125 := params 12
abbrev ray6125 := rays 12
def bank6125 : Fin 2 → Cell := twoBank p6125 ray6125
theorem signs6125 : ∀ j, Signs p6125 (bank6125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6126 := params 13
abbrev ray6126 := rays 13
def bank6126 : Fin 2 → Cell := twoBank p6126 ray6126
theorem signs6126 : ∀ j, Signs p6126 (bank6126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6127 := params 14
abbrev ray6127 := rays 14
def bank6127 : Fin 2 → Cell := twoBank p6127 ray6127
theorem signs6127 : ∀ j, Signs p6127 (bank6127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6128 := params 15
abbrev ray6128 := rays 15
def bank6128 : Fin 2 → Cell := twoBank p6128 ray6128
theorem signs6128 : ∀ j, Signs p6128 (bank6128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6129 := params 16
abbrev ray6129 := rays 16
def bank6129 : Fin 2 → Cell := twoBank p6129 ray6129
theorem signs6129 : ∀ j, Signs p6129 (bank6129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6130 := params 17
abbrev ray6130 := rays 17
def bank6130 : Fin 2 → Cell := twoBank p6130 ray6130
theorem signs6130 : ∀ j, Signs p6130 (bank6130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6131 := params 18
abbrev ray6131 := rays 18
def bank6131 : Fin 2 → Cell := twoBank p6131 ray6131
theorem signs6131 : ∀ j, Signs p6131 (bank6131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6132 := params 19
abbrev ray6132 := rays 19
def bank6132 : Fin 2 → Cell := twoBank p6132 ray6132
theorem signs6132 : ∀ j, Signs p6132 (bank6132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6133 := params 20
abbrev ray6133 := rays 20
def bank6133 : Fin 2 → Cell := twoBank p6133 ray6133
theorem signs6133 : ∀ j, Signs p6133 (bank6133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6134 := params 21
abbrev ray6134 := rays 21
def bank6134 : Fin 2 → Cell := twoBank p6134 ray6134
theorem signs6134 : ∀ j, Signs p6134 (bank6134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6135 := params 22
abbrev ray6135 := rays 22
def bank6135 : Fin 2 → Cell := twoBank p6135 ray6135
theorem signs6135 : ∀ j, Signs p6135 (bank6135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6136 := params 23
abbrev ray6136 := rays 23
def bank6136 : Fin 2 → Cell := twoBank p6136 ray6136
theorem signs6136 : ∀ j, Signs p6136 (bank6136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6137 := params 24
abbrev ray6137 := rays 24
def bank6137 : Fin 2 → Cell := twoBank p6137 ray6137
theorem signs6137 : ∀ j, Signs p6137 (bank6137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6138 := params 25
abbrev ray6138 := rays 25
def bank6138 : Fin 2 → Cell := twoBank p6138 ray6138
theorem signs6138 : ∀ j, Signs p6138 (bank6138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6139 := params 26
abbrev ray6139 := rays 26
def bank6139 : Fin 2 → Cell := twoBank p6139 ray6139
theorem signs6139 : ∀ j, Signs p6139 (bank6139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6140 := params 27
abbrev ray6140 := rays 27
def bank6140 : Fin 2 → Cell := twoBank p6140 ray6140
theorem signs6140 : ∀ j, Signs p6140 (bank6140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6141 := params 28
abbrev ray6141 := rays 28
def bank6141 : Fin 2 → Cell := twoBank p6141 ray6141
theorem signs6141 : ∀ j, Signs p6141 (bank6141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6142 := params 29
abbrev ray6142 := rays 29
def bank6142 : Fin 2 → Cell := twoBank p6142 ray6142
theorem signs6142 : ∀ j, Signs p6142 (bank6142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6143 := params 30
abbrev ray6143 := rays 30
def bank6143 : Fin 2 → Cell := twoBank p6143 ray6143
theorem signs6143 : ∀ j, Signs p6143 (bank6143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6144 := params 31
abbrev ray6144 := rays 31
def bank6144 : Fin 2 → Cell := twoBank p6144 ray6144
theorem signs6144 : ∀ j, Signs p6144 (bank6144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06113_06144
