/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11105_11136
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97052720771617,97052332006248,97051943221114,97051554416215,97051165591553,97050776747127,97050387882938,97049998998987,97049610095274,97049221171800,97048832228565,97048443265569,97048054282813,97047665280298,97047276258024,97046887215991,97046498154200,97046109072651,97045719971345,97045330850283,97044941709465,97044552548891,97044163368562,97043774168478,97043384948640,97042995709048,97042606449703,97042217170605,97041827871755,97041438553153,97041049214800,97040659856696,97040270478842]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11104+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11105 := params 0
abbrev ray11105 := rays 0
def bank11105 : Fin 2 → Cell := twoBank p11105 ray11105
theorem signs11105 : ∀ j, Signs p11105 (bank11105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11106 := params 1
abbrev ray11106 := rays 1
def bank11106 : Fin 2 → Cell := twoBank p11106 ray11106
theorem signs11106 : ∀ j, Signs p11106 (bank11106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11107 := params 2
abbrev ray11107 := rays 2
def bank11107 : Fin 2 → Cell := twoBank p11107 ray11107
theorem signs11107 : ∀ j, Signs p11107 (bank11107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11108 := params 3
abbrev ray11108 := rays 3
def bank11108 : Fin 2 → Cell := twoBank p11108 ray11108
theorem signs11108 : ∀ j, Signs p11108 (bank11108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11109 := params 4
abbrev ray11109 := rays 4
def bank11109 : Fin 2 → Cell := twoBank p11109 ray11109
theorem signs11109 : ∀ j, Signs p11109 (bank11109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11110 := params 5
abbrev ray11110 := rays 5
def bank11110 : Fin 2 → Cell := twoBank p11110 ray11110
theorem signs11110 : ∀ j, Signs p11110 (bank11110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11111 := params 6
abbrev ray11111 := rays 6
def bank11111 : Fin 2 → Cell := twoBank p11111 ray11111
theorem signs11111 : ∀ j, Signs p11111 (bank11111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11112 := params 7
abbrev ray11112 := rays 7
def bank11112 : Fin 2 → Cell := twoBank p11112 ray11112
theorem signs11112 : ∀ j, Signs p11112 (bank11112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11113 := params 8
abbrev ray11113 := rays 8
def bank11113 : Fin 2 → Cell := twoBank p11113 ray11113
theorem signs11113 : ∀ j, Signs p11113 (bank11113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11114 := params 9
abbrev ray11114 := rays 9
def bank11114 : Fin 2 → Cell := twoBank p11114 ray11114
theorem signs11114 : ∀ j, Signs p11114 (bank11114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11115 := params 10
abbrev ray11115 := rays 10
def bank11115 : Fin 2 → Cell := twoBank p11115 ray11115
theorem signs11115 : ∀ j, Signs p11115 (bank11115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11116 := params 11
abbrev ray11116 := rays 11
def bank11116 : Fin 2 → Cell := twoBank p11116 ray11116
theorem signs11116 : ∀ j, Signs p11116 (bank11116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11117 := params 12
abbrev ray11117 := rays 12
def bank11117 : Fin 2 → Cell := twoBank p11117 ray11117
theorem signs11117 : ∀ j, Signs p11117 (bank11117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11118 := params 13
abbrev ray11118 := rays 13
def bank11118 : Fin 2 → Cell := twoBank p11118 ray11118
theorem signs11118 : ∀ j, Signs p11118 (bank11118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11119 := params 14
abbrev ray11119 := rays 14
def bank11119 : Fin 2 → Cell := twoBank p11119 ray11119
theorem signs11119 : ∀ j, Signs p11119 (bank11119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11120 := params 15
abbrev ray11120 := rays 15
def bank11120 : Fin 2 → Cell := twoBank p11120 ray11120
theorem signs11120 : ∀ j, Signs p11120 (bank11120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11121 := params 16
abbrev ray11121 := rays 16
def bank11121 : Fin 2 → Cell := twoBank p11121 ray11121
theorem signs11121 : ∀ j, Signs p11121 (bank11121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11122 := params 17
abbrev ray11122 := rays 17
def bank11122 : Fin 2 → Cell := twoBank p11122 ray11122
theorem signs11122 : ∀ j, Signs p11122 (bank11122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11123 := params 18
abbrev ray11123 := rays 18
def bank11123 : Fin 2 → Cell := twoBank p11123 ray11123
theorem signs11123 : ∀ j, Signs p11123 (bank11123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11124 := params 19
abbrev ray11124 := rays 19
def bank11124 : Fin 2 → Cell := twoBank p11124 ray11124
theorem signs11124 : ∀ j, Signs p11124 (bank11124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11125 := params 20
abbrev ray11125 := rays 20
def bank11125 : Fin 2 → Cell := twoBank p11125 ray11125
theorem signs11125 : ∀ j, Signs p11125 (bank11125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11126 := params 21
abbrev ray11126 := rays 21
def bank11126 : Fin 2 → Cell := twoBank p11126 ray11126
theorem signs11126 : ∀ j, Signs p11126 (bank11126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11127 := params 22
abbrev ray11127 := rays 22
def bank11127 : Fin 2 → Cell := twoBank p11127 ray11127
theorem signs11127 : ∀ j, Signs p11127 (bank11127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11128 := params 23
abbrev ray11128 := rays 23
def bank11128 : Fin 2 → Cell := twoBank p11128 ray11128
theorem signs11128 : ∀ j, Signs p11128 (bank11128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11129 := params 24
abbrev ray11129 := rays 24
def bank11129 : Fin 2 → Cell := twoBank p11129 ray11129
theorem signs11129 : ∀ j, Signs p11129 (bank11129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11130 := params 25
abbrev ray11130 := rays 25
def bank11130 : Fin 2 → Cell := twoBank p11130 ray11130
theorem signs11130 : ∀ j, Signs p11130 (bank11130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11131 := params 26
abbrev ray11131 := rays 26
def bank11131 : Fin 2 → Cell := twoBank p11131 ray11131
theorem signs11131 : ∀ j, Signs p11131 (bank11131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11132 := params 27
abbrev ray11132 := rays 27
def bank11132 : Fin 2 → Cell := twoBank p11132 ray11132
theorem signs11132 : ∀ j, Signs p11132 (bank11132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11133 := params 28
abbrev ray11133 := rays 28
def bank11133 : Fin 2 → Cell := twoBank p11133 ray11133
theorem signs11133 : ∀ j, Signs p11133 (bank11133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11134 := params 29
abbrev ray11134 := rays 29
def bank11134 : Fin 2 → Cell := twoBank p11134 ray11134
theorem signs11134 : ∀ j, Signs p11134 (bank11134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11135 := params 30
abbrev ray11135 := rays 30
def bank11135 : Fin 2 → Cell := twoBank p11135 ray11135
theorem signs11135 : ∀ j, Signs p11135 (bank11135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11136 := params 31
abbrev ray11136 := rays 31
def bank11136 : Fin 2 → Cell := twoBank p11136 ray11136
theorem signs11136 : ∀ j, Signs p11136 (bank11136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11105_11136
