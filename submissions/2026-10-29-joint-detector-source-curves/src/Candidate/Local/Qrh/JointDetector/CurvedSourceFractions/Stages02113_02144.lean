/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02113_02144
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99670911610372,99670729458988,99670547280047,99670365073550,99670182839499,99670000577895,99669818288740,99669635972035,99669453627782,99669271255981,99669088856635,99668906429745,99668723975312,99668541493337,99668358983822,99668176446769,99667993882179,99667811290053,99667628670393,99667446023200,99667263348475,99667080646220,99666897916437,99666715159127,99666532374291,99666349561931,99666166722048,99665983854643,99665800959718,99665618037275,99665435087315,99665252109839,99665069104848]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2112+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2113 := params 0
abbrev ray2113 := rays 0
def bank2113 : Fin 2 → Cell := twoBank p2113 ray2113
theorem signs2113 : ∀ j, Signs p2113 (bank2113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2114 := params 1
abbrev ray2114 := rays 1
def bank2114 : Fin 2 → Cell := twoBank p2114 ray2114
theorem signs2114 : ∀ j, Signs p2114 (bank2114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2115 := params 2
abbrev ray2115 := rays 2
def bank2115 : Fin 2 → Cell := twoBank p2115 ray2115
theorem signs2115 : ∀ j, Signs p2115 (bank2115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2116 := params 3
abbrev ray2116 := rays 3
def bank2116 : Fin 2 → Cell := twoBank p2116 ray2116
theorem signs2116 : ∀ j, Signs p2116 (bank2116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2117 := params 4
abbrev ray2117 := rays 4
def bank2117 : Fin 2 → Cell := twoBank p2117 ray2117
theorem signs2117 : ∀ j, Signs p2117 (bank2117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2118 := params 5
abbrev ray2118 := rays 5
def bank2118 : Fin 2 → Cell := twoBank p2118 ray2118
theorem signs2118 : ∀ j, Signs p2118 (bank2118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2119 := params 6
abbrev ray2119 := rays 6
def bank2119 : Fin 2 → Cell := twoBank p2119 ray2119
theorem signs2119 : ∀ j, Signs p2119 (bank2119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2120 := params 7
abbrev ray2120 := rays 7
def bank2120 : Fin 2 → Cell := twoBank p2120 ray2120
theorem signs2120 : ∀ j, Signs p2120 (bank2120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2121 := params 8
abbrev ray2121 := rays 8
def bank2121 : Fin 2 → Cell := twoBank p2121 ray2121
theorem signs2121 : ∀ j, Signs p2121 (bank2121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2122 := params 9
abbrev ray2122 := rays 9
def bank2122 : Fin 2 → Cell := twoBank p2122 ray2122
theorem signs2122 : ∀ j, Signs p2122 (bank2122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2123 := params 10
abbrev ray2123 := rays 10
def bank2123 : Fin 2 → Cell := twoBank p2123 ray2123
theorem signs2123 : ∀ j, Signs p2123 (bank2123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2124 := params 11
abbrev ray2124 := rays 11
def bank2124 : Fin 2 → Cell := twoBank p2124 ray2124
theorem signs2124 : ∀ j, Signs p2124 (bank2124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2125 := params 12
abbrev ray2125 := rays 12
def bank2125 : Fin 2 → Cell := twoBank p2125 ray2125
theorem signs2125 : ∀ j, Signs p2125 (bank2125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2126 := params 13
abbrev ray2126 := rays 13
def bank2126 : Fin 2 → Cell := twoBank p2126 ray2126
theorem signs2126 : ∀ j, Signs p2126 (bank2126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2127 := params 14
abbrev ray2127 := rays 14
def bank2127 : Fin 2 → Cell := twoBank p2127 ray2127
theorem signs2127 : ∀ j, Signs p2127 (bank2127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2128 := params 15
abbrev ray2128 := rays 15
def bank2128 : Fin 2 → Cell := twoBank p2128 ray2128
theorem signs2128 : ∀ j, Signs p2128 (bank2128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2129 := params 16
abbrev ray2129 := rays 16
def bank2129 : Fin 2 → Cell := twoBank p2129 ray2129
theorem signs2129 : ∀ j, Signs p2129 (bank2129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2130 := params 17
abbrev ray2130 := rays 17
def bank2130 : Fin 2 → Cell := twoBank p2130 ray2130
theorem signs2130 : ∀ j, Signs p2130 (bank2130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2131 := params 18
abbrev ray2131 := rays 18
def bank2131 : Fin 2 → Cell := twoBank p2131 ray2131
theorem signs2131 : ∀ j, Signs p2131 (bank2131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2132 := params 19
abbrev ray2132 := rays 19
def bank2132 : Fin 2 → Cell := twoBank p2132 ray2132
theorem signs2132 : ∀ j, Signs p2132 (bank2132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2133 := params 20
abbrev ray2133 := rays 20
def bank2133 : Fin 2 → Cell := twoBank p2133 ray2133
theorem signs2133 : ∀ j, Signs p2133 (bank2133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2134 := params 21
abbrev ray2134 := rays 21
def bank2134 : Fin 2 → Cell := twoBank p2134 ray2134
theorem signs2134 : ∀ j, Signs p2134 (bank2134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2135 := params 22
abbrev ray2135 := rays 22
def bank2135 : Fin 2 → Cell := twoBank p2135 ray2135
theorem signs2135 : ∀ j, Signs p2135 (bank2135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2136 := params 23
abbrev ray2136 := rays 23
def bank2136 : Fin 2 → Cell := twoBank p2136 ray2136
theorem signs2136 : ∀ j, Signs p2136 (bank2136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2137 := params 24
abbrev ray2137 := rays 24
def bank2137 : Fin 2 → Cell := twoBank p2137 ray2137
theorem signs2137 : ∀ j, Signs p2137 (bank2137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2138 := params 25
abbrev ray2138 := rays 25
def bank2138 : Fin 2 → Cell := twoBank p2138 ray2138
theorem signs2138 : ∀ j, Signs p2138 (bank2138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2139 := params 26
abbrev ray2139 := rays 26
def bank2139 : Fin 2 → Cell := twoBank p2139 ray2139
theorem signs2139 : ∀ j, Signs p2139 (bank2139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2140 := params 27
abbrev ray2140 := rays 27
def bank2140 : Fin 2 → Cell := twoBank p2140 ray2140
theorem signs2140 : ∀ j, Signs p2140 (bank2140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2141 := params 28
abbrev ray2141 := rays 28
def bank2141 : Fin 2 → Cell := twoBank p2141 ray2141
theorem signs2141 : ∀ j, Signs p2141 (bank2141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2142 := params 29
abbrev ray2142 := rays 29
def bank2142 : Fin 2 → Cell := twoBank p2142 ray2142
theorem signs2142 : ∀ j, Signs p2142 (bank2142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2143 := params 30
abbrev ray2143 := rays 30
def bank2143 : Fin 2 → Cell := twoBank p2143 ray2143
theorem signs2143 : ∀ j, Signs p2143 (bank2143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2144 := params 31
abbrev ray2144 := rays 31
def bank2144 : Fin 2 → Cell := twoBank p2144 ray2144
theorem signs2144 : ∀ j, Signs p2144 (bank2144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02113_02144
