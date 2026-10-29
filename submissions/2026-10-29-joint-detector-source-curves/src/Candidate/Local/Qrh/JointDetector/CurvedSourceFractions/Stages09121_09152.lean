/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09121_09152
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97784441061412,97784092543881,97783744005500,97783395446270,97783046866191,97782698265263,97782349643488,97782001000865,97781652337396,97781303653081,97780954947921,97780606221916,97780257475067,97779908707375,97779559918840,97779211109463,97778862279244,97778513428184,97778164556284,97777815663544,97777466749965,97777117815548,97776768860293,97776419884201,97776070887272,97775721869507,97775372830906,97775023771471,97774674691201,97774325590098,97773976468162,97773627325393,97773278161793]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9120+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9121 := params 0
abbrev ray9121 := rays 0
def bank9121 : Fin 2 → Cell := twoBank p9121 ray9121
theorem signs9121 : ∀ j, Signs p9121 (bank9121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9122 := params 1
abbrev ray9122 := rays 1
def bank9122 : Fin 2 → Cell := twoBank p9122 ray9122
theorem signs9122 : ∀ j, Signs p9122 (bank9122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9123 := params 2
abbrev ray9123 := rays 2
def bank9123 : Fin 2 → Cell := twoBank p9123 ray9123
theorem signs9123 : ∀ j, Signs p9123 (bank9123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9124 := params 3
abbrev ray9124 := rays 3
def bank9124 : Fin 2 → Cell := twoBank p9124 ray9124
theorem signs9124 : ∀ j, Signs p9124 (bank9124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9125 := params 4
abbrev ray9125 := rays 4
def bank9125 : Fin 2 → Cell := twoBank p9125 ray9125
theorem signs9125 : ∀ j, Signs p9125 (bank9125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9126 := params 5
abbrev ray9126 := rays 5
def bank9126 : Fin 2 → Cell := twoBank p9126 ray9126
theorem signs9126 : ∀ j, Signs p9126 (bank9126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9127 := params 6
abbrev ray9127 := rays 6
def bank9127 : Fin 2 → Cell := twoBank p9127 ray9127
theorem signs9127 : ∀ j, Signs p9127 (bank9127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9128 := params 7
abbrev ray9128 := rays 7
def bank9128 : Fin 2 → Cell := twoBank p9128 ray9128
theorem signs9128 : ∀ j, Signs p9128 (bank9128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9129 := params 8
abbrev ray9129 := rays 8
def bank9129 : Fin 2 → Cell := twoBank p9129 ray9129
theorem signs9129 : ∀ j, Signs p9129 (bank9129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9130 := params 9
abbrev ray9130 := rays 9
def bank9130 : Fin 2 → Cell := twoBank p9130 ray9130
theorem signs9130 : ∀ j, Signs p9130 (bank9130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9131 := params 10
abbrev ray9131 := rays 10
def bank9131 : Fin 2 → Cell := twoBank p9131 ray9131
theorem signs9131 : ∀ j, Signs p9131 (bank9131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9132 := params 11
abbrev ray9132 := rays 11
def bank9132 : Fin 2 → Cell := twoBank p9132 ray9132
theorem signs9132 : ∀ j, Signs p9132 (bank9132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9133 := params 12
abbrev ray9133 := rays 12
def bank9133 : Fin 2 → Cell := twoBank p9133 ray9133
theorem signs9133 : ∀ j, Signs p9133 (bank9133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9134 := params 13
abbrev ray9134 := rays 13
def bank9134 : Fin 2 → Cell := twoBank p9134 ray9134
theorem signs9134 : ∀ j, Signs p9134 (bank9134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9135 := params 14
abbrev ray9135 := rays 14
def bank9135 : Fin 2 → Cell := twoBank p9135 ray9135
theorem signs9135 : ∀ j, Signs p9135 (bank9135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9136 := params 15
abbrev ray9136 := rays 15
def bank9136 : Fin 2 → Cell := twoBank p9136 ray9136
theorem signs9136 : ∀ j, Signs p9136 (bank9136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9137 := params 16
abbrev ray9137 := rays 16
def bank9137 : Fin 2 → Cell := twoBank p9137 ray9137
theorem signs9137 : ∀ j, Signs p9137 (bank9137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9138 := params 17
abbrev ray9138 := rays 17
def bank9138 : Fin 2 → Cell := twoBank p9138 ray9138
theorem signs9138 : ∀ j, Signs p9138 (bank9138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9139 := params 18
abbrev ray9139 := rays 18
def bank9139 : Fin 2 → Cell := twoBank p9139 ray9139
theorem signs9139 : ∀ j, Signs p9139 (bank9139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9140 := params 19
abbrev ray9140 := rays 19
def bank9140 : Fin 2 → Cell := twoBank p9140 ray9140
theorem signs9140 : ∀ j, Signs p9140 (bank9140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9141 := params 20
abbrev ray9141 := rays 20
def bank9141 : Fin 2 → Cell := twoBank p9141 ray9141
theorem signs9141 : ∀ j, Signs p9141 (bank9141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9142 := params 21
abbrev ray9142 := rays 21
def bank9142 : Fin 2 → Cell := twoBank p9142 ray9142
theorem signs9142 : ∀ j, Signs p9142 (bank9142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9143 := params 22
abbrev ray9143 := rays 22
def bank9143 : Fin 2 → Cell := twoBank p9143 ray9143
theorem signs9143 : ∀ j, Signs p9143 (bank9143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9144 := params 23
abbrev ray9144 := rays 23
def bank9144 : Fin 2 → Cell := twoBank p9144 ray9144
theorem signs9144 : ∀ j, Signs p9144 (bank9144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9145 := params 24
abbrev ray9145 := rays 24
def bank9145 : Fin 2 → Cell := twoBank p9145 ray9145
theorem signs9145 : ∀ j, Signs p9145 (bank9145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9146 := params 25
abbrev ray9146 := rays 25
def bank9146 : Fin 2 → Cell := twoBank p9146 ray9146
theorem signs9146 : ∀ j, Signs p9146 (bank9146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9147 := params 26
abbrev ray9147 := rays 26
def bank9147 : Fin 2 → Cell := twoBank p9147 ray9147
theorem signs9147 : ∀ j, Signs p9147 (bank9147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9148 := params 27
abbrev ray9148 := rays 27
def bank9148 : Fin 2 → Cell := twoBank p9148 ray9148
theorem signs9148 : ∀ j, Signs p9148 (bank9148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9149 := params 28
abbrev ray9149 := rays 28
def bank9149 : Fin 2 → Cell := twoBank p9149 ray9149
theorem signs9149 : ∀ j, Signs p9149 (bank9149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9150 := params 29
abbrev ray9150 := rays 29
def bank9150 : Fin 2 → Cell := twoBank p9150 ray9150
theorem signs9150 : ∀ j, Signs p9150 (bank9150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9151 := params 30
abbrev ray9151 := rays 30
def bank9151 : Fin 2 → Cell := twoBank p9151 ray9151
theorem signs9151 : ∀ j, Signs p9151 (bank9151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9152 := params 31
abbrev ray9152 := rays 31
def bank9152 : Fin 2 → Cell := twoBank p9152 ray9152
theorem signs9152 : ∀ j, Signs p9152 (bank9152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09121_09152
