/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03137_03168
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99470201387386,99469991733455,99469782053337,99469572347033,99469362614544,99469152855871,99468943071016,99468733259980,99468523422764,99468313559369,99468103669797,99467893754049,99467683812126,99467473844030,99467263849761,99467053829321,99466843782711,99466633709933,99466423610987,99466213485875,99466003334598,99465793157158,99465582953555,99465372723791,99465162467867,99464952185785,99464741877546,99464531543150,99464321182600,99464110795896,99463900383040,99463689944033,99463479478876]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3136+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3137 := params 0
abbrev ray3137 := rays 0
def bank3137 : Fin 2 → Cell := twoBank p3137 ray3137
theorem signs3137 : ∀ j, Signs p3137 (bank3137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3138 := params 1
abbrev ray3138 := rays 1
def bank3138 : Fin 2 → Cell := twoBank p3138 ray3138
theorem signs3138 : ∀ j, Signs p3138 (bank3138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3139 := params 2
abbrev ray3139 := rays 2
def bank3139 : Fin 2 → Cell := twoBank p3139 ray3139
theorem signs3139 : ∀ j, Signs p3139 (bank3139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3140 := params 3
abbrev ray3140 := rays 3
def bank3140 : Fin 2 → Cell := twoBank p3140 ray3140
theorem signs3140 : ∀ j, Signs p3140 (bank3140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3141 := params 4
abbrev ray3141 := rays 4
def bank3141 : Fin 2 → Cell := twoBank p3141 ray3141
theorem signs3141 : ∀ j, Signs p3141 (bank3141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3142 := params 5
abbrev ray3142 := rays 5
def bank3142 : Fin 2 → Cell := twoBank p3142 ray3142
theorem signs3142 : ∀ j, Signs p3142 (bank3142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3143 := params 6
abbrev ray3143 := rays 6
def bank3143 : Fin 2 → Cell := twoBank p3143 ray3143
theorem signs3143 : ∀ j, Signs p3143 (bank3143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3144 := params 7
abbrev ray3144 := rays 7
def bank3144 : Fin 2 → Cell := twoBank p3144 ray3144
theorem signs3144 : ∀ j, Signs p3144 (bank3144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3145 := params 8
abbrev ray3145 := rays 8
def bank3145 : Fin 2 → Cell := twoBank p3145 ray3145
theorem signs3145 : ∀ j, Signs p3145 (bank3145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3146 := params 9
abbrev ray3146 := rays 9
def bank3146 : Fin 2 → Cell := twoBank p3146 ray3146
theorem signs3146 : ∀ j, Signs p3146 (bank3146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3147 := params 10
abbrev ray3147 := rays 10
def bank3147 : Fin 2 → Cell := twoBank p3147 ray3147
theorem signs3147 : ∀ j, Signs p3147 (bank3147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3148 := params 11
abbrev ray3148 := rays 11
def bank3148 : Fin 2 → Cell := twoBank p3148 ray3148
theorem signs3148 : ∀ j, Signs p3148 (bank3148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3149 := params 12
abbrev ray3149 := rays 12
def bank3149 : Fin 2 → Cell := twoBank p3149 ray3149
theorem signs3149 : ∀ j, Signs p3149 (bank3149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3150 := params 13
abbrev ray3150 := rays 13
def bank3150 : Fin 2 → Cell := twoBank p3150 ray3150
theorem signs3150 : ∀ j, Signs p3150 (bank3150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3151 := params 14
abbrev ray3151 := rays 14
def bank3151 : Fin 2 → Cell := twoBank p3151 ray3151
theorem signs3151 : ∀ j, Signs p3151 (bank3151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3152 := params 15
abbrev ray3152 := rays 15
def bank3152 : Fin 2 → Cell := twoBank p3152 ray3152
theorem signs3152 : ∀ j, Signs p3152 (bank3152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3153 := params 16
abbrev ray3153 := rays 16
def bank3153 : Fin 2 → Cell := twoBank p3153 ray3153
theorem signs3153 : ∀ j, Signs p3153 (bank3153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3154 := params 17
abbrev ray3154 := rays 17
def bank3154 : Fin 2 → Cell := twoBank p3154 ray3154
theorem signs3154 : ∀ j, Signs p3154 (bank3154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3155 := params 18
abbrev ray3155 := rays 18
def bank3155 : Fin 2 → Cell := twoBank p3155 ray3155
theorem signs3155 : ∀ j, Signs p3155 (bank3155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3156 := params 19
abbrev ray3156 := rays 19
def bank3156 : Fin 2 → Cell := twoBank p3156 ray3156
theorem signs3156 : ∀ j, Signs p3156 (bank3156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3157 := params 20
abbrev ray3157 := rays 20
def bank3157 : Fin 2 → Cell := twoBank p3157 ray3157
theorem signs3157 : ∀ j, Signs p3157 (bank3157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3158 := params 21
abbrev ray3158 := rays 21
def bank3158 : Fin 2 → Cell := twoBank p3158 ray3158
theorem signs3158 : ∀ j, Signs p3158 (bank3158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3159 := params 22
abbrev ray3159 := rays 22
def bank3159 : Fin 2 → Cell := twoBank p3159 ray3159
theorem signs3159 : ∀ j, Signs p3159 (bank3159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3160 := params 23
abbrev ray3160 := rays 23
def bank3160 : Fin 2 → Cell := twoBank p3160 ray3160
theorem signs3160 : ∀ j, Signs p3160 (bank3160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3161 := params 24
abbrev ray3161 := rays 24
def bank3161 : Fin 2 → Cell := twoBank p3161 ray3161
theorem signs3161 : ∀ j, Signs p3161 (bank3161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3162 := params 25
abbrev ray3162 := rays 25
def bank3162 : Fin 2 → Cell := twoBank p3162 ray3162
theorem signs3162 : ∀ j, Signs p3162 (bank3162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3163 := params 26
abbrev ray3163 := rays 26
def bank3163 : Fin 2 → Cell := twoBank p3163 ray3163
theorem signs3163 : ∀ j, Signs p3163 (bank3163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3164 := params 27
abbrev ray3164 := rays 27
def bank3164 : Fin 2 → Cell := twoBank p3164 ray3164
theorem signs3164 : ∀ j, Signs p3164 (bank3164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3165 := params 28
abbrev ray3165 := rays 28
def bank3165 : Fin 2 → Cell := twoBank p3165 ray3165
theorem signs3165 : ∀ j, Signs p3165 (bank3165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3166 := params 29
abbrev ray3166 := rays 29
def bank3166 : Fin 2 → Cell := twoBank p3166 ray3166
theorem signs3166 : ∀ j, Signs p3166 (bank3166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3167 := params 30
abbrev ray3167 := rays 30
def bank3167 : Fin 2 → Cell := twoBank p3167 ray3167
theorem signs3167 : ∀ j, Signs p3167 (bank3167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3168 := params 31
abbrev ray3168 := rays 31
def bank3168 : Fin 2 → Cell := twoBank p3168 ray3168
theorem signs3168 : ∀ j, Signs p3168 (bank3168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03137_03168
