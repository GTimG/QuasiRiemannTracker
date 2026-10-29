/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03233_03264
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99449955374087,99449743211858,99449531023561,99449318809198,99449106568769,99448894302276,99448682009720,99448469691103,99448257346425,99448044975688,99447832578893,99447620156041,99447407707134,99447195232173,99446982731158,99446770204092,99446557650975,99446345071809,99446132466595,99445919835334,99445707178027,99445494494676,99445281785282,99445069049846,99444856288369,99444643500853,99444430687299,99444217847708,99444004982081,99443792090420,99443579172725,99443366228998,99443153259240]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3232+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3233 := params 0
abbrev ray3233 := rays 0
def bank3233 : Fin 2 → Cell := twoBank p3233 ray3233
theorem signs3233 : ∀ j, Signs p3233 (bank3233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3234 := params 1
abbrev ray3234 := rays 1
def bank3234 : Fin 2 → Cell := twoBank p3234 ray3234
theorem signs3234 : ∀ j, Signs p3234 (bank3234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3235 := params 2
abbrev ray3235 := rays 2
def bank3235 : Fin 2 → Cell := twoBank p3235 ray3235
theorem signs3235 : ∀ j, Signs p3235 (bank3235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3236 := params 3
abbrev ray3236 := rays 3
def bank3236 : Fin 2 → Cell := twoBank p3236 ray3236
theorem signs3236 : ∀ j, Signs p3236 (bank3236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3237 := params 4
abbrev ray3237 := rays 4
def bank3237 : Fin 2 → Cell := twoBank p3237 ray3237
theorem signs3237 : ∀ j, Signs p3237 (bank3237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3238 := params 5
abbrev ray3238 := rays 5
def bank3238 : Fin 2 → Cell := twoBank p3238 ray3238
theorem signs3238 : ∀ j, Signs p3238 (bank3238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3239 := params 6
abbrev ray3239 := rays 6
def bank3239 : Fin 2 → Cell := twoBank p3239 ray3239
theorem signs3239 : ∀ j, Signs p3239 (bank3239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3240 := params 7
abbrev ray3240 := rays 7
def bank3240 : Fin 2 → Cell := twoBank p3240 ray3240
theorem signs3240 : ∀ j, Signs p3240 (bank3240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3241 := params 8
abbrev ray3241 := rays 8
def bank3241 : Fin 2 → Cell := twoBank p3241 ray3241
theorem signs3241 : ∀ j, Signs p3241 (bank3241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3242 := params 9
abbrev ray3242 := rays 9
def bank3242 : Fin 2 → Cell := twoBank p3242 ray3242
theorem signs3242 : ∀ j, Signs p3242 (bank3242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3243 := params 10
abbrev ray3243 := rays 10
def bank3243 : Fin 2 → Cell := twoBank p3243 ray3243
theorem signs3243 : ∀ j, Signs p3243 (bank3243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3244 := params 11
abbrev ray3244 := rays 11
def bank3244 : Fin 2 → Cell := twoBank p3244 ray3244
theorem signs3244 : ∀ j, Signs p3244 (bank3244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3245 := params 12
abbrev ray3245 := rays 12
def bank3245 : Fin 2 → Cell := twoBank p3245 ray3245
theorem signs3245 : ∀ j, Signs p3245 (bank3245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3246 := params 13
abbrev ray3246 := rays 13
def bank3246 : Fin 2 → Cell := twoBank p3246 ray3246
theorem signs3246 : ∀ j, Signs p3246 (bank3246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3247 := params 14
abbrev ray3247 := rays 14
def bank3247 : Fin 2 → Cell := twoBank p3247 ray3247
theorem signs3247 : ∀ j, Signs p3247 (bank3247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3248 := params 15
abbrev ray3248 := rays 15
def bank3248 : Fin 2 → Cell := twoBank p3248 ray3248
theorem signs3248 : ∀ j, Signs p3248 (bank3248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3249 := params 16
abbrev ray3249 := rays 16
def bank3249 : Fin 2 → Cell := twoBank p3249 ray3249
theorem signs3249 : ∀ j, Signs p3249 (bank3249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3250 := params 17
abbrev ray3250 := rays 17
def bank3250 : Fin 2 → Cell := twoBank p3250 ray3250
theorem signs3250 : ∀ j, Signs p3250 (bank3250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3251 := params 18
abbrev ray3251 := rays 18
def bank3251 : Fin 2 → Cell := twoBank p3251 ray3251
theorem signs3251 : ∀ j, Signs p3251 (bank3251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3252 := params 19
abbrev ray3252 := rays 19
def bank3252 : Fin 2 → Cell := twoBank p3252 ray3252
theorem signs3252 : ∀ j, Signs p3252 (bank3252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3253 := params 20
abbrev ray3253 := rays 20
def bank3253 : Fin 2 → Cell := twoBank p3253 ray3253
theorem signs3253 : ∀ j, Signs p3253 (bank3253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3254 := params 21
abbrev ray3254 := rays 21
def bank3254 : Fin 2 → Cell := twoBank p3254 ray3254
theorem signs3254 : ∀ j, Signs p3254 (bank3254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3255 := params 22
abbrev ray3255 := rays 22
def bank3255 : Fin 2 → Cell := twoBank p3255 ray3255
theorem signs3255 : ∀ j, Signs p3255 (bank3255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3256 := params 23
abbrev ray3256 := rays 23
def bank3256 : Fin 2 → Cell := twoBank p3256 ray3256
theorem signs3256 : ∀ j, Signs p3256 (bank3256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3257 := params 24
abbrev ray3257 := rays 24
def bank3257 : Fin 2 → Cell := twoBank p3257 ray3257
theorem signs3257 : ∀ j, Signs p3257 (bank3257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3258 := params 25
abbrev ray3258 := rays 25
def bank3258 : Fin 2 → Cell := twoBank p3258 ray3258
theorem signs3258 : ∀ j, Signs p3258 (bank3258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3259 := params 26
abbrev ray3259 := rays 26
def bank3259 : Fin 2 → Cell := twoBank p3259 ray3259
theorem signs3259 : ∀ j, Signs p3259 (bank3259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3260 := params 27
abbrev ray3260 := rays 27
def bank3260 : Fin 2 → Cell := twoBank p3260 ray3260
theorem signs3260 : ∀ j, Signs p3260 (bank3260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3261 := params 28
abbrev ray3261 := rays 28
def bank3261 : Fin 2 → Cell := twoBank p3261 ray3261
theorem signs3261 : ∀ j, Signs p3261 (bank3261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3262 := params 29
abbrev ray3262 := rays 29
def bank3262 : Fin 2 → Cell := twoBank p3262 ray3262
theorem signs3262 : ∀ j, Signs p3262 (bank3262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3263 := params 30
abbrev ray3263 := rays 30
def bank3263 : Fin 2 → Cell := twoBank p3263 ray3263
theorem signs3263 : ∀ j, Signs p3263 (bank3263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3264 := params 31
abbrev ray3264 := rays 31
def bank3264 : Fin 2 → Cell := twoBank p3264 ray3264
theorem signs3264 : ∀ j, Signs p3264 (bank3264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03233_03264
