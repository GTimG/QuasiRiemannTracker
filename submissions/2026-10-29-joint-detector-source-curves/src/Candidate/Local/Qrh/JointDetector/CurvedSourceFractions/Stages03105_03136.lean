/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03105_03136
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99476896478742,99476687663469,99476478821968,99476269954241,99476061060289,99475852140113,99475643193715,99475434221096,99475225222257,99475016197199,99474807145924,99474598068432,99474388964725,99474179834805,99473970678672,99473761496328,99473552287774,99473343053011,99473133792041,99472924504865,99472715191484,99472505851899,99472296486112,99472087094124,99471877675936,99471668231549,99471458760965,99471249264185,99471039741210,99470830192041,99470620616680,99470411015128,99470201387386]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3104+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3105 := params 0
abbrev ray3105 := rays 0
def bank3105 : Fin 2 → Cell := twoBank p3105 ray3105
theorem signs3105 : ∀ j, Signs p3105 (bank3105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3106 := params 1
abbrev ray3106 := rays 1
def bank3106 : Fin 2 → Cell := twoBank p3106 ray3106
theorem signs3106 : ∀ j, Signs p3106 (bank3106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3107 := params 2
abbrev ray3107 := rays 2
def bank3107 : Fin 2 → Cell := twoBank p3107 ray3107
theorem signs3107 : ∀ j, Signs p3107 (bank3107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3108 := params 3
abbrev ray3108 := rays 3
def bank3108 : Fin 2 → Cell := twoBank p3108 ray3108
theorem signs3108 : ∀ j, Signs p3108 (bank3108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3109 := params 4
abbrev ray3109 := rays 4
def bank3109 : Fin 2 → Cell := twoBank p3109 ray3109
theorem signs3109 : ∀ j, Signs p3109 (bank3109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3110 := params 5
abbrev ray3110 := rays 5
def bank3110 : Fin 2 → Cell := twoBank p3110 ray3110
theorem signs3110 : ∀ j, Signs p3110 (bank3110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3111 := params 6
abbrev ray3111 := rays 6
def bank3111 : Fin 2 → Cell := twoBank p3111 ray3111
theorem signs3111 : ∀ j, Signs p3111 (bank3111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3112 := params 7
abbrev ray3112 := rays 7
def bank3112 : Fin 2 → Cell := twoBank p3112 ray3112
theorem signs3112 : ∀ j, Signs p3112 (bank3112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3113 := params 8
abbrev ray3113 := rays 8
def bank3113 : Fin 2 → Cell := twoBank p3113 ray3113
theorem signs3113 : ∀ j, Signs p3113 (bank3113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3114 := params 9
abbrev ray3114 := rays 9
def bank3114 : Fin 2 → Cell := twoBank p3114 ray3114
theorem signs3114 : ∀ j, Signs p3114 (bank3114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3115 := params 10
abbrev ray3115 := rays 10
def bank3115 : Fin 2 → Cell := twoBank p3115 ray3115
theorem signs3115 : ∀ j, Signs p3115 (bank3115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3116 := params 11
abbrev ray3116 := rays 11
def bank3116 : Fin 2 → Cell := twoBank p3116 ray3116
theorem signs3116 : ∀ j, Signs p3116 (bank3116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3117 := params 12
abbrev ray3117 := rays 12
def bank3117 : Fin 2 → Cell := twoBank p3117 ray3117
theorem signs3117 : ∀ j, Signs p3117 (bank3117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3118 := params 13
abbrev ray3118 := rays 13
def bank3118 : Fin 2 → Cell := twoBank p3118 ray3118
theorem signs3118 : ∀ j, Signs p3118 (bank3118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3119 := params 14
abbrev ray3119 := rays 14
def bank3119 : Fin 2 → Cell := twoBank p3119 ray3119
theorem signs3119 : ∀ j, Signs p3119 (bank3119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3120 := params 15
abbrev ray3120 := rays 15
def bank3120 : Fin 2 → Cell := twoBank p3120 ray3120
theorem signs3120 : ∀ j, Signs p3120 (bank3120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3121 := params 16
abbrev ray3121 := rays 16
def bank3121 : Fin 2 → Cell := twoBank p3121 ray3121
theorem signs3121 : ∀ j, Signs p3121 (bank3121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3122 := params 17
abbrev ray3122 := rays 17
def bank3122 : Fin 2 → Cell := twoBank p3122 ray3122
theorem signs3122 : ∀ j, Signs p3122 (bank3122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3123 := params 18
abbrev ray3123 := rays 18
def bank3123 : Fin 2 → Cell := twoBank p3123 ray3123
theorem signs3123 : ∀ j, Signs p3123 (bank3123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3124 := params 19
abbrev ray3124 := rays 19
def bank3124 : Fin 2 → Cell := twoBank p3124 ray3124
theorem signs3124 : ∀ j, Signs p3124 (bank3124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3125 := params 20
abbrev ray3125 := rays 20
def bank3125 : Fin 2 → Cell := twoBank p3125 ray3125
theorem signs3125 : ∀ j, Signs p3125 (bank3125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3126 := params 21
abbrev ray3126 := rays 21
def bank3126 : Fin 2 → Cell := twoBank p3126 ray3126
theorem signs3126 : ∀ j, Signs p3126 (bank3126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3127 := params 22
abbrev ray3127 := rays 22
def bank3127 : Fin 2 → Cell := twoBank p3127 ray3127
theorem signs3127 : ∀ j, Signs p3127 (bank3127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3128 := params 23
abbrev ray3128 := rays 23
def bank3128 : Fin 2 → Cell := twoBank p3128 ray3128
theorem signs3128 : ∀ j, Signs p3128 (bank3128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3129 := params 24
abbrev ray3129 := rays 24
def bank3129 : Fin 2 → Cell := twoBank p3129 ray3129
theorem signs3129 : ∀ j, Signs p3129 (bank3129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3130 := params 25
abbrev ray3130 := rays 25
def bank3130 : Fin 2 → Cell := twoBank p3130 ray3130
theorem signs3130 : ∀ j, Signs p3130 (bank3130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3131 := params 26
abbrev ray3131 := rays 26
def bank3131 : Fin 2 → Cell := twoBank p3131 ray3131
theorem signs3131 : ∀ j, Signs p3131 (bank3131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3132 := params 27
abbrev ray3132 := rays 27
def bank3132 : Fin 2 → Cell := twoBank p3132 ray3132
theorem signs3132 : ∀ j, Signs p3132 (bank3132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3133 := params 28
abbrev ray3133 := rays 28
def bank3133 : Fin 2 → Cell := twoBank p3133 ray3133
theorem signs3133 : ∀ j, Signs p3133 (bank3133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3134 := params 29
abbrev ray3134 := rays 29
def bank3134 : Fin 2 → Cell := twoBank p3134 ray3134
theorem signs3134 : ∀ j, Signs p3134 (bank3134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3135 := params 30
abbrev ray3135 := rays 30
def bank3135 : Fin 2 → Cell := twoBank p3135 ray3135
theorem signs3135 : ∀ j, Signs p3135 (bank3135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3136 := params 31
abbrev ray3136 := rays 31
def bank3136 : Fin 2 → Cell := twoBank p3136 ray3136
theorem signs3136 : ∀ j, Signs p3136 (bank3136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03105_03136
