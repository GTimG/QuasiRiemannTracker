/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14113_14144
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95798100482617,95797657447910,95797214397009,95796771329915,95796328246628,95795885147148,95795442031475,95794998899610,95794555751552,95794112587302,95793669406860,95793226210226,95792782997401,95792339768384,95791896523176,95791453261777,95791009984187,95790566690406,95790123380434,95789680054272,95789236711919,95788793353376,95788349978643,95787906587721,95787463180609,95787019757308,95786576317818,95786132862139,95785689390271,95785245902214,95784802397968,95784358877534,95783915340912]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14112+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14113 := params 0
abbrev ray14113 := rays 0
def bank14113 : Fin 1 → Cell := oneBank p14113 ray14113
theorem signs14113 : ∀ j, Signs p14113 (bank14113 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14114 := params 1
abbrev ray14114 := rays 1
def bank14114 : Fin 1 → Cell := oneBank p14114 ray14114
theorem signs14114 : ∀ j, Signs p14114 (bank14114 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14115 := params 2
abbrev ray14115 := rays 2
def bank14115 : Fin 1 → Cell := oneBank p14115 ray14115
theorem signs14115 : ∀ j, Signs p14115 (bank14115 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14116 := params 3
abbrev ray14116 := rays 3
def bank14116 : Fin 1 → Cell := oneBank p14116 ray14116
theorem signs14116 : ∀ j, Signs p14116 (bank14116 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14117 := params 4
abbrev ray14117 := rays 4
def bank14117 : Fin 1 → Cell := oneBank p14117 ray14117
theorem signs14117 : ∀ j, Signs p14117 (bank14117 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14118 := params 5
abbrev ray14118 := rays 5
def bank14118 : Fin 1 → Cell := oneBank p14118 ray14118
theorem signs14118 : ∀ j, Signs p14118 (bank14118 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14119 := params 6
abbrev ray14119 := rays 6
def bank14119 : Fin 1 → Cell := oneBank p14119 ray14119
theorem signs14119 : ∀ j, Signs p14119 (bank14119 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14120 := params 7
abbrev ray14120 := rays 7
def bank14120 : Fin 1 → Cell := oneBank p14120 ray14120
theorem signs14120 : ∀ j, Signs p14120 (bank14120 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14121 := params 8
abbrev ray14121 := rays 8
def bank14121 : Fin 1 → Cell := oneBank p14121 ray14121
theorem signs14121 : ∀ j, Signs p14121 (bank14121 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14122 := params 9
abbrev ray14122 := rays 9
def bank14122 : Fin 1 → Cell := oneBank p14122 ray14122
theorem signs14122 : ∀ j, Signs p14122 (bank14122 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14123 := params 10
abbrev ray14123 := rays 10
def bank14123 : Fin 1 → Cell := oneBank p14123 ray14123
theorem signs14123 : ∀ j, Signs p14123 (bank14123 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14124 := params 11
abbrev ray14124 := rays 11
def bank14124 : Fin 1 → Cell := oneBank p14124 ray14124
theorem signs14124 : ∀ j, Signs p14124 (bank14124 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14125 := params 12
abbrev ray14125 := rays 12
def bank14125 : Fin 1 → Cell := oneBank p14125 ray14125
theorem signs14125 : ∀ j, Signs p14125 (bank14125 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14126 := params 13
abbrev ray14126 := rays 13
def bank14126 : Fin 1 → Cell := oneBank p14126 ray14126
theorem signs14126 : ∀ j, Signs p14126 (bank14126 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14127 := params 14
abbrev ray14127 := rays 14
def bank14127 : Fin 1 → Cell := oneBank p14127 ray14127
theorem signs14127 : ∀ j, Signs p14127 (bank14127 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14128 := params 15
abbrev ray14128 := rays 15
def bank14128 : Fin 1 → Cell := oneBank p14128 ray14128
theorem signs14128 : ∀ j, Signs p14128 (bank14128 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14129 := params 16
abbrev ray14129 := rays 16
def bank14129 : Fin 1 → Cell := oneBank p14129 ray14129
theorem signs14129 : ∀ j, Signs p14129 (bank14129 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14130 := params 17
abbrev ray14130 := rays 17
def bank14130 : Fin 1 → Cell := oneBank p14130 ray14130
theorem signs14130 : ∀ j, Signs p14130 (bank14130 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14131 := params 18
abbrev ray14131 := rays 18
def bank14131 : Fin 1 → Cell := oneBank p14131 ray14131
theorem signs14131 : ∀ j, Signs p14131 (bank14131 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14132 := params 19
abbrev ray14132 := rays 19
def bank14132 : Fin 1 → Cell := oneBank p14132 ray14132
theorem signs14132 : ∀ j, Signs p14132 (bank14132 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14133 := params 20
abbrev ray14133 := rays 20
def bank14133 : Fin 1 → Cell := oneBank p14133 ray14133
theorem signs14133 : ∀ j, Signs p14133 (bank14133 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14134 := params 21
abbrev ray14134 := rays 21
def bank14134 : Fin 1 → Cell := oneBank p14134 ray14134
theorem signs14134 : ∀ j, Signs p14134 (bank14134 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14135 := params 22
abbrev ray14135 := rays 22
def bank14135 : Fin 1 → Cell := oneBank p14135 ray14135
theorem signs14135 : ∀ j, Signs p14135 (bank14135 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14136 := params 23
abbrev ray14136 := rays 23
def bank14136 : Fin 1 → Cell := oneBank p14136 ray14136
theorem signs14136 : ∀ j, Signs p14136 (bank14136 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14137 := params 24
abbrev ray14137 := rays 24
def bank14137 : Fin 1 → Cell := oneBank p14137 ray14137
theorem signs14137 : ∀ j, Signs p14137 (bank14137 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14138 := params 25
abbrev ray14138 := rays 25
def bank14138 : Fin 1 → Cell := oneBank p14138 ray14138
theorem signs14138 : ∀ j, Signs p14138 (bank14138 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14139 := params 26
abbrev ray14139 := rays 26
def bank14139 : Fin 1 → Cell := oneBank p14139 ray14139
theorem signs14139 : ∀ j, Signs p14139 (bank14139 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14140 := params 27
abbrev ray14140 := rays 27
def bank14140 : Fin 1 → Cell := oneBank p14140 ray14140
theorem signs14140 : ∀ j, Signs p14140 (bank14140 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14141 := params 28
abbrev ray14141 := rays 28
def bank14141 : Fin 1 → Cell := oneBank p14141 ray14141
theorem signs14141 : ∀ j, Signs p14141 (bank14141 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14142 := params 29
abbrev ray14142 := rays 29
def bank14142 : Fin 1 → Cell := oneBank p14142 ray14142
theorem signs14142 : ∀ j, Signs p14142 (bank14142 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14143 := params 30
abbrev ray14143 := rays 30
def bank14143 : Fin 1 → Cell := oneBank p14143 ray14143
theorem signs14143 : ∀ j, Signs p14143 (bank14143 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14144 := params 31
abbrev ray14144 := rays 31
def bank14144 : Fin 1 → Cell := oneBank p14144 ray14144
theorem signs14144 : ∀ j, Signs p14144 (bank14144 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14113_14144
