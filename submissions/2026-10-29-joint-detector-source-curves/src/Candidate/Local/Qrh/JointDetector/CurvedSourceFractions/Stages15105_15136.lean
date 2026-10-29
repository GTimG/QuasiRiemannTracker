/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15105_15136
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95350676079798,95350217056009,95349758016165,95349298960266,95348839888313,95348380800306,95347921696244,95347462576128,95347003439958,95346544287734,95346085119456,95345625935125,95345166734740,95344707518301,95344248285809,95343789037264,95343329772665,95342870492013,95342411195308,95341951882550,95341492553740,95341033208877,95340573847961,95340114470993,95339655077972,95339195668899,95338736243774,95338276802597,95337817345368,95337357872087,95336898382754,95336438877369,95335979355933]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15104+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15105 := params 0
abbrev ray15105 := rays 0
def bank15105 : Fin 1 → Cell := oneBank p15105 ray15105
theorem signs15105 : ∀ j, Signs p15105 (bank15105 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15106 := params 1
abbrev ray15106 := rays 1
def bank15106 : Fin 1 → Cell := oneBank p15106 ray15106
theorem signs15106 : ∀ j, Signs p15106 (bank15106 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15107 := params 2
abbrev ray15107 := rays 2
def bank15107 : Fin 1 → Cell := oneBank p15107 ray15107
theorem signs15107 : ∀ j, Signs p15107 (bank15107 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15108 := params 3
abbrev ray15108 := rays 3
def bank15108 : Fin 1 → Cell := oneBank p15108 ray15108
theorem signs15108 : ∀ j, Signs p15108 (bank15108 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15109 := params 4
abbrev ray15109 := rays 4
def bank15109 : Fin 1 → Cell := oneBank p15109 ray15109
theorem signs15109 : ∀ j, Signs p15109 (bank15109 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15110 := params 5
abbrev ray15110 := rays 5
def bank15110 : Fin 1 → Cell := oneBank p15110 ray15110
theorem signs15110 : ∀ j, Signs p15110 (bank15110 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15111 := params 6
abbrev ray15111 := rays 6
def bank15111 : Fin 1 → Cell := oneBank p15111 ray15111
theorem signs15111 : ∀ j, Signs p15111 (bank15111 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15112 := params 7
abbrev ray15112 := rays 7
def bank15112 : Fin 1 → Cell := oneBank p15112 ray15112
theorem signs15112 : ∀ j, Signs p15112 (bank15112 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15113 := params 8
abbrev ray15113 := rays 8
def bank15113 : Fin 1 → Cell := oneBank p15113 ray15113
theorem signs15113 : ∀ j, Signs p15113 (bank15113 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15114 := params 9
abbrev ray15114 := rays 9
def bank15114 : Fin 1 → Cell := oneBank p15114 ray15114
theorem signs15114 : ∀ j, Signs p15114 (bank15114 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15115 := params 10
abbrev ray15115 := rays 10
def bank15115 : Fin 1 → Cell := oneBank p15115 ray15115
theorem signs15115 : ∀ j, Signs p15115 (bank15115 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15116 := params 11
abbrev ray15116 := rays 11
def bank15116 : Fin 1 → Cell := oneBank p15116 ray15116
theorem signs15116 : ∀ j, Signs p15116 (bank15116 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15117 := params 12
abbrev ray15117 := rays 12
def bank15117 : Fin 1 → Cell := oneBank p15117 ray15117
theorem signs15117 : ∀ j, Signs p15117 (bank15117 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15118 := params 13
abbrev ray15118 := rays 13
def bank15118 : Fin 1 → Cell := oneBank p15118 ray15118
theorem signs15118 : ∀ j, Signs p15118 (bank15118 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15119 := params 14
abbrev ray15119 := rays 14
def bank15119 : Fin 1 → Cell := oneBank p15119 ray15119
theorem signs15119 : ∀ j, Signs p15119 (bank15119 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15120 := params 15
abbrev ray15120 := rays 15
def bank15120 : Fin 1 → Cell := oneBank p15120 ray15120
theorem signs15120 : ∀ j, Signs p15120 (bank15120 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15121 := params 16
abbrev ray15121 := rays 16
def bank15121 : Fin 1 → Cell := oneBank p15121 ray15121
theorem signs15121 : ∀ j, Signs p15121 (bank15121 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15122 := params 17
abbrev ray15122 := rays 17
def bank15122 : Fin 1 → Cell := oneBank p15122 ray15122
theorem signs15122 : ∀ j, Signs p15122 (bank15122 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15123 := params 18
abbrev ray15123 := rays 18
def bank15123 : Fin 1 → Cell := oneBank p15123 ray15123
theorem signs15123 : ∀ j, Signs p15123 (bank15123 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15124 := params 19
abbrev ray15124 := rays 19
def bank15124 : Fin 1 → Cell := oneBank p15124 ray15124
theorem signs15124 : ∀ j, Signs p15124 (bank15124 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15125 := params 20
abbrev ray15125 := rays 20
def bank15125 : Fin 1 → Cell := oneBank p15125 ray15125
theorem signs15125 : ∀ j, Signs p15125 (bank15125 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15126 := params 21
abbrev ray15126 := rays 21
def bank15126 : Fin 1 → Cell := oneBank p15126 ray15126
theorem signs15126 : ∀ j, Signs p15126 (bank15126 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15127 := params 22
abbrev ray15127 := rays 22
def bank15127 : Fin 1 → Cell := oneBank p15127 ray15127
theorem signs15127 : ∀ j, Signs p15127 (bank15127 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15128 := params 23
abbrev ray15128 := rays 23
def bank15128 : Fin 1 → Cell := oneBank p15128 ray15128
theorem signs15128 : ∀ j, Signs p15128 (bank15128 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15129 := params 24
abbrev ray15129 := rays 24
def bank15129 : Fin 1 → Cell := oneBank p15129 ray15129
theorem signs15129 : ∀ j, Signs p15129 (bank15129 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15130 := params 25
abbrev ray15130 := rays 25
def bank15130 : Fin 1 → Cell := oneBank p15130 ray15130
theorem signs15130 : ∀ j, Signs p15130 (bank15130 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15131 := params 26
abbrev ray15131 := rays 26
def bank15131 : Fin 1 → Cell := oneBank p15131 ray15131
theorem signs15131 : ∀ j, Signs p15131 (bank15131 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15132 := params 27
abbrev ray15132 := rays 27
def bank15132 : Fin 1 → Cell := oneBank p15132 ray15132
theorem signs15132 : ∀ j, Signs p15132 (bank15132 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15133 := params 28
abbrev ray15133 := rays 28
def bank15133 : Fin 1 → Cell := oneBank p15133 ray15133
theorem signs15133 : ∀ j, Signs p15133 (bank15133 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15134 := params 29
abbrev ray15134 := rays 29
def bank15134 : Fin 1 → Cell := oneBank p15134 ray15134
theorem signs15134 : ∀ j, Signs p15134 (bank15134 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15135 := params 30
abbrev ray15135 := rays 30
def bank15135 : Fin 1 → Cell := oneBank p15135 ray15135
theorem signs15135 : ∀ j, Signs p15135 (bank15135 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15136 := params 31
abbrev ray15136 := rays 31
def bank15136 : Fin 1 → Cell := oneBank p15136 ray15136
theorem signs15136 : ∀ j, Signs p15136 (bank15136 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15105_15136
