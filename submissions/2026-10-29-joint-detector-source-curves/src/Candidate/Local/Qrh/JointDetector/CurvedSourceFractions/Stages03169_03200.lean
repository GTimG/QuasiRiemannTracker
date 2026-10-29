/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03169_03200
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99463479478876,99463268987570,99463058470117,99462847926518,99462637356774,99462426760886,99462216138856,99462005490685,99461794816374,99461584115924,99461373389337,99461162636614,99460951857756,99460741052764,99460530221640,99460319364384,99460108480999,99459897571485,99459686635843,99459475674075,99459264686182,99459053672166,99458842632027,99458631565767,99458420473387,99458209354888,99457998210272,99457787039540,99457575842693,99457364619732,99457153370658,99456942095473,99456730794178]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3168+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3169 := params 0
abbrev ray3169 := rays 0
def bank3169 : Fin 2 → Cell := twoBank p3169 ray3169
theorem signs3169 : ∀ j, Signs p3169 (bank3169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3170 := params 1
abbrev ray3170 := rays 1
def bank3170 : Fin 2 → Cell := twoBank p3170 ray3170
theorem signs3170 : ∀ j, Signs p3170 (bank3170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3171 := params 2
abbrev ray3171 := rays 2
def bank3171 : Fin 2 → Cell := twoBank p3171 ray3171
theorem signs3171 : ∀ j, Signs p3171 (bank3171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3172 := params 3
abbrev ray3172 := rays 3
def bank3172 : Fin 2 → Cell := twoBank p3172 ray3172
theorem signs3172 : ∀ j, Signs p3172 (bank3172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3173 := params 4
abbrev ray3173 := rays 4
def bank3173 : Fin 2 → Cell := twoBank p3173 ray3173
theorem signs3173 : ∀ j, Signs p3173 (bank3173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3174 := params 5
abbrev ray3174 := rays 5
def bank3174 : Fin 2 → Cell := twoBank p3174 ray3174
theorem signs3174 : ∀ j, Signs p3174 (bank3174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3175 := params 6
abbrev ray3175 := rays 6
def bank3175 : Fin 2 → Cell := twoBank p3175 ray3175
theorem signs3175 : ∀ j, Signs p3175 (bank3175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3176 := params 7
abbrev ray3176 := rays 7
def bank3176 : Fin 2 → Cell := twoBank p3176 ray3176
theorem signs3176 : ∀ j, Signs p3176 (bank3176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3177 := params 8
abbrev ray3177 := rays 8
def bank3177 : Fin 2 → Cell := twoBank p3177 ray3177
theorem signs3177 : ∀ j, Signs p3177 (bank3177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3178 := params 9
abbrev ray3178 := rays 9
def bank3178 : Fin 2 → Cell := twoBank p3178 ray3178
theorem signs3178 : ∀ j, Signs p3178 (bank3178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3179 := params 10
abbrev ray3179 := rays 10
def bank3179 : Fin 2 → Cell := twoBank p3179 ray3179
theorem signs3179 : ∀ j, Signs p3179 (bank3179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3180 := params 11
abbrev ray3180 := rays 11
def bank3180 : Fin 2 → Cell := twoBank p3180 ray3180
theorem signs3180 : ∀ j, Signs p3180 (bank3180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3181 := params 12
abbrev ray3181 := rays 12
def bank3181 : Fin 2 → Cell := twoBank p3181 ray3181
theorem signs3181 : ∀ j, Signs p3181 (bank3181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3182 := params 13
abbrev ray3182 := rays 13
def bank3182 : Fin 2 → Cell := twoBank p3182 ray3182
theorem signs3182 : ∀ j, Signs p3182 (bank3182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3183 := params 14
abbrev ray3183 := rays 14
def bank3183 : Fin 2 → Cell := twoBank p3183 ray3183
theorem signs3183 : ∀ j, Signs p3183 (bank3183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3184 := params 15
abbrev ray3184 := rays 15
def bank3184 : Fin 2 → Cell := twoBank p3184 ray3184
theorem signs3184 : ∀ j, Signs p3184 (bank3184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3185 := params 16
abbrev ray3185 := rays 16
def bank3185 : Fin 2 → Cell := twoBank p3185 ray3185
theorem signs3185 : ∀ j, Signs p3185 (bank3185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3186 := params 17
abbrev ray3186 := rays 17
def bank3186 : Fin 2 → Cell := twoBank p3186 ray3186
theorem signs3186 : ∀ j, Signs p3186 (bank3186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3187 := params 18
abbrev ray3187 := rays 18
def bank3187 : Fin 2 → Cell := twoBank p3187 ray3187
theorem signs3187 : ∀ j, Signs p3187 (bank3187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3188 := params 19
abbrev ray3188 := rays 19
def bank3188 : Fin 2 → Cell := twoBank p3188 ray3188
theorem signs3188 : ∀ j, Signs p3188 (bank3188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3189 := params 20
abbrev ray3189 := rays 20
def bank3189 : Fin 2 → Cell := twoBank p3189 ray3189
theorem signs3189 : ∀ j, Signs p3189 (bank3189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3190 := params 21
abbrev ray3190 := rays 21
def bank3190 : Fin 2 → Cell := twoBank p3190 ray3190
theorem signs3190 : ∀ j, Signs p3190 (bank3190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3191 := params 22
abbrev ray3191 := rays 22
def bank3191 : Fin 2 → Cell := twoBank p3191 ray3191
theorem signs3191 : ∀ j, Signs p3191 (bank3191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3192 := params 23
abbrev ray3192 := rays 23
def bank3192 : Fin 2 → Cell := twoBank p3192 ray3192
theorem signs3192 : ∀ j, Signs p3192 (bank3192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3193 := params 24
abbrev ray3193 := rays 24
def bank3193 : Fin 2 → Cell := twoBank p3193 ray3193
theorem signs3193 : ∀ j, Signs p3193 (bank3193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3194 := params 25
abbrev ray3194 := rays 25
def bank3194 : Fin 2 → Cell := twoBank p3194 ray3194
theorem signs3194 : ∀ j, Signs p3194 (bank3194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3195 := params 26
abbrev ray3195 := rays 26
def bank3195 : Fin 2 → Cell := twoBank p3195 ray3195
theorem signs3195 : ∀ j, Signs p3195 (bank3195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3196 := params 27
abbrev ray3196 := rays 27
def bank3196 : Fin 2 → Cell := twoBank p3196 ray3196
theorem signs3196 : ∀ j, Signs p3196 (bank3196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3197 := params 28
abbrev ray3197 := rays 28
def bank3197 : Fin 2 → Cell := twoBank p3197 ray3197
theorem signs3197 : ∀ j, Signs p3197 (bank3197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3198 := params 29
abbrev ray3198 := rays 29
def bank3198 : Fin 2 → Cell := twoBank p3198 ray3198
theorem signs3198 : ∀ j, Signs p3198 (bank3198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3199 := params 30
abbrev ray3199 := rays 30
def bank3199 : Fin 2 → Cell := twoBank p3199 ray3199
theorem signs3199 : ∀ j, Signs p3199 (bank3199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3200 := params 31
abbrev ray3200 := rays 31
def bank3200 : Fin 2 → Cell := twoBank p3200 ray3200
theorem signs3200 : ∀ j, Signs p3200 (bank3200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03169_03200
