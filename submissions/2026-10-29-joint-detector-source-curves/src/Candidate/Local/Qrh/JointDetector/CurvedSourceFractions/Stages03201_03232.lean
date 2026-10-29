/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03201_03232
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99456730794178,99456519466774,99456308113263,99456096733646,99455885327924,99455673896098,99455462438169,99455250954139,99455039444009,99454827907780,99454616345453,99454404757030,99454193142512,99453981501900,99453769835195,99453558142399,99453346423513,99453134678538,99452922907475,99452711110326,99452499287092,99452287437774,99452075562373,99451863660891,99451651733328,99451439779686,99451227799967,99451015794171,99450803762300,99450591704355,99450379620337,99450167510247,99449955374087]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3200+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3201 := params 0
abbrev ray3201 := rays 0
def bank3201 : Fin 2 → Cell := twoBank p3201 ray3201
theorem signs3201 : ∀ j, Signs p3201 (bank3201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3202 := params 1
abbrev ray3202 := rays 1
def bank3202 : Fin 2 → Cell := twoBank p3202 ray3202
theorem signs3202 : ∀ j, Signs p3202 (bank3202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3203 := params 2
abbrev ray3203 := rays 2
def bank3203 : Fin 2 → Cell := twoBank p3203 ray3203
theorem signs3203 : ∀ j, Signs p3203 (bank3203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3204 := params 3
abbrev ray3204 := rays 3
def bank3204 : Fin 2 → Cell := twoBank p3204 ray3204
theorem signs3204 : ∀ j, Signs p3204 (bank3204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3205 := params 4
abbrev ray3205 := rays 4
def bank3205 : Fin 2 → Cell := twoBank p3205 ray3205
theorem signs3205 : ∀ j, Signs p3205 (bank3205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3206 := params 5
abbrev ray3206 := rays 5
def bank3206 : Fin 2 → Cell := twoBank p3206 ray3206
theorem signs3206 : ∀ j, Signs p3206 (bank3206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3207 := params 6
abbrev ray3207 := rays 6
def bank3207 : Fin 2 → Cell := twoBank p3207 ray3207
theorem signs3207 : ∀ j, Signs p3207 (bank3207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3208 := params 7
abbrev ray3208 := rays 7
def bank3208 : Fin 2 → Cell := twoBank p3208 ray3208
theorem signs3208 : ∀ j, Signs p3208 (bank3208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3209 := params 8
abbrev ray3209 := rays 8
def bank3209 : Fin 2 → Cell := twoBank p3209 ray3209
theorem signs3209 : ∀ j, Signs p3209 (bank3209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3210 := params 9
abbrev ray3210 := rays 9
def bank3210 : Fin 2 → Cell := twoBank p3210 ray3210
theorem signs3210 : ∀ j, Signs p3210 (bank3210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3211 := params 10
abbrev ray3211 := rays 10
def bank3211 : Fin 2 → Cell := twoBank p3211 ray3211
theorem signs3211 : ∀ j, Signs p3211 (bank3211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3212 := params 11
abbrev ray3212 := rays 11
def bank3212 : Fin 2 → Cell := twoBank p3212 ray3212
theorem signs3212 : ∀ j, Signs p3212 (bank3212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3213 := params 12
abbrev ray3213 := rays 12
def bank3213 : Fin 2 → Cell := twoBank p3213 ray3213
theorem signs3213 : ∀ j, Signs p3213 (bank3213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3214 := params 13
abbrev ray3214 := rays 13
def bank3214 : Fin 2 → Cell := twoBank p3214 ray3214
theorem signs3214 : ∀ j, Signs p3214 (bank3214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3215 := params 14
abbrev ray3215 := rays 14
def bank3215 : Fin 2 → Cell := twoBank p3215 ray3215
theorem signs3215 : ∀ j, Signs p3215 (bank3215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3216 := params 15
abbrev ray3216 := rays 15
def bank3216 : Fin 2 → Cell := twoBank p3216 ray3216
theorem signs3216 : ∀ j, Signs p3216 (bank3216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3217 := params 16
abbrev ray3217 := rays 16
def bank3217 : Fin 2 → Cell := twoBank p3217 ray3217
theorem signs3217 : ∀ j, Signs p3217 (bank3217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3218 := params 17
abbrev ray3218 := rays 17
def bank3218 : Fin 2 → Cell := twoBank p3218 ray3218
theorem signs3218 : ∀ j, Signs p3218 (bank3218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3219 := params 18
abbrev ray3219 := rays 18
def bank3219 : Fin 2 → Cell := twoBank p3219 ray3219
theorem signs3219 : ∀ j, Signs p3219 (bank3219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3220 := params 19
abbrev ray3220 := rays 19
def bank3220 : Fin 2 → Cell := twoBank p3220 ray3220
theorem signs3220 : ∀ j, Signs p3220 (bank3220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3221 := params 20
abbrev ray3221 := rays 20
def bank3221 : Fin 2 → Cell := twoBank p3221 ray3221
theorem signs3221 : ∀ j, Signs p3221 (bank3221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3222 := params 21
abbrev ray3222 := rays 21
def bank3222 : Fin 2 → Cell := twoBank p3222 ray3222
theorem signs3222 : ∀ j, Signs p3222 (bank3222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3223 := params 22
abbrev ray3223 := rays 22
def bank3223 : Fin 2 → Cell := twoBank p3223 ray3223
theorem signs3223 : ∀ j, Signs p3223 (bank3223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3224 := params 23
abbrev ray3224 := rays 23
def bank3224 : Fin 2 → Cell := twoBank p3224 ray3224
theorem signs3224 : ∀ j, Signs p3224 (bank3224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3225 := params 24
abbrev ray3225 := rays 24
def bank3225 : Fin 2 → Cell := twoBank p3225 ray3225
theorem signs3225 : ∀ j, Signs p3225 (bank3225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3226 := params 25
abbrev ray3226 := rays 25
def bank3226 : Fin 2 → Cell := twoBank p3226 ray3226
theorem signs3226 : ∀ j, Signs p3226 (bank3226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3227 := params 26
abbrev ray3227 := rays 26
def bank3227 : Fin 2 → Cell := twoBank p3227 ray3227
theorem signs3227 : ∀ j, Signs p3227 (bank3227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3228 := params 27
abbrev ray3228 := rays 27
def bank3228 : Fin 2 → Cell := twoBank p3228 ray3228
theorem signs3228 : ∀ j, Signs p3228 (bank3228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3229 := params 28
abbrev ray3229 := rays 28
def bank3229 : Fin 2 → Cell := twoBank p3229 ray3229
theorem signs3229 : ∀ j, Signs p3229 (bank3229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3230 := params 29
abbrev ray3230 := rays 29
def bank3230 : Fin 2 → Cell := twoBank p3230 ray3230
theorem signs3230 : ∀ j, Signs p3230 (bank3230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3231 := params 30
abbrev ray3231 := rays 30
def bank3231 : Fin 2 → Cell := twoBank p3231 ray3231
theorem signs3231 : ∀ j, Signs p3231 (bank3231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3232 := params 31
abbrev ray3232 := rays 31
def bank3232 : Fin 2 → Cell := twoBank p3232 ray3232
theorem signs3232 : ∀ j, Signs p3232 (bank3232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03201_03232
