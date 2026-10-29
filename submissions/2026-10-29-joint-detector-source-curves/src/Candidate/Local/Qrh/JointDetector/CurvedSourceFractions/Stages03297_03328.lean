/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03297_03328
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99436324490107,99436110662024,99435896807952,99435682927892,99435469021846,99435255089814,99435041131798,99434827147800,99434613137820,99434399101860,99434185039920,99433970952002,99433756838108,99433542698238,99433328532394,99433114340577,99432900122788,99432685879029,99432471609300,99432257313603,99432042991939,99431828644310,99431614270716,99431399871159,99431185445640,99430970994160,99430756516721,99430542013323,99430327483968,99430112928657,99429898347392,99429683740173,99429469107002]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3296+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3297 := params 0
abbrev ray3297 := rays 0
def bank3297 : Fin 2 → Cell := twoBank p3297 ray3297
theorem signs3297 : ∀ j, Signs p3297 (bank3297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3298 := params 1
abbrev ray3298 := rays 1
def bank3298 : Fin 2 → Cell := twoBank p3298 ray3298
theorem signs3298 : ∀ j, Signs p3298 (bank3298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3299 := params 2
abbrev ray3299 := rays 2
def bank3299 : Fin 2 → Cell := twoBank p3299 ray3299
theorem signs3299 : ∀ j, Signs p3299 (bank3299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3300 := params 3
abbrev ray3300 := rays 3
def bank3300 : Fin 2 → Cell := twoBank p3300 ray3300
theorem signs3300 : ∀ j, Signs p3300 (bank3300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3301 := params 4
abbrev ray3301 := rays 4
def bank3301 : Fin 2 → Cell := twoBank p3301 ray3301
theorem signs3301 : ∀ j, Signs p3301 (bank3301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3302 := params 5
abbrev ray3302 := rays 5
def bank3302 : Fin 2 → Cell := twoBank p3302 ray3302
theorem signs3302 : ∀ j, Signs p3302 (bank3302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3303 := params 6
abbrev ray3303 := rays 6
def bank3303 : Fin 2 → Cell := twoBank p3303 ray3303
theorem signs3303 : ∀ j, Signs p3303 (bank3303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3304 := params 7
abbrev ray3304 := rays 7
def bank3304 : Fin 2 → Cell := twoBank p3304 ray3304
theorem signs3304 : ∀ j, Signs p3304 (bank3304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3305 := params 8
abbrev ray3305 := rays 8
def bank3305 : Fin 2 → Cell := twoBank p3305 ray3305
theorem signs3305 : ∀ j, Signs p3305 (bank3305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3306 := params 9
abbrev ray3306 := rays 9
def bank3306 : Fin 2 → Cell := twoBank p3306 ray3306
theorem signs3306 : ∀ j, Signs p3306 (bank3306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3307 := params 10
abbrev ray3307 := rays 10
def bank3307 : Fin 2 → Cell := twoBank p3307 ray3307
theorem signs3307 : ∀ j, Signs p3307 (bank3307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3308 := params 11
abbrev ray3308 := rays 11
def bank3308 : Fin 2 → Cell := twoBank p3308 ray3308
theorem signs3308 : ∀ j, Signs p3308 (bank3308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3309 := params 12
abbrev ray3309 := rays 12
def bank3309 : Fin 2 → Cell := twoBank p3309 ray3309
theorem signs3309 : ∀ j, Signs p3309 (bank3309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3310 := params 13
abbrev ray3310 := rays 13
def bank3310 : Fin 2 → Cell := twoBank p3310 ray3310
theorem signs3310 : ∀ j, Signs p3310 (bank3310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3311 := params 14
abbrev ray3311 := rays 14
def bank3311 : Fin 2 → Cell := twoBank p3311 ray3311
theorem signs3311 : ∀ j, Signs p3311 (bank3311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3312 := params 15
abbrev ray3312 := rays 15
def bank3312 : Fin 2 → Cell := twoBank p3312 ray3312
theorem signs3312 : ∀ j, Signs p3312 (bank3312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3313 := params 16
abbrev ray3313 := rays 16
def bank3313 : Fin 2 → Cell := twoBank p3313 ray3313
theorem signs3313 : ∀ j, Signs p3313 (bank3313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3314 := params 17
abbrev ray3314 := rays 17
def bank3314 : Fin 2 → Cell := twoBank p3314 ray3314
theorem signs3314 : ∀ j, Signs p3314 (bank3314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3315 := params 18
abbrev ray3315 := rays 18
def bank3315 : Fin 2 → Cell := twoBank p3315 ray3315
theorem signs3315 : ∀ j, Signs p3315 (bank3315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3316 := params 19
abbrev ray3316 := rays 19
def bank3316 : Fin 2 → Cell := twoBank p3316 ray3316
theorem signs3316 : ∀ j, Signs p3316 (bank3316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3317 := params 20
abbrev ray3317 := rays 20
def bank3317 : Fin 2 → Cell := twoBank p3317 ray3317
theorem signs3317 : ∀ j, Signs p3317 (bank3317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3318 := params 21
abbrev ray3318 := rays 21
def bank3318 : Fin 2 → Cell := twoBank p3318 ray3318
theorem signs3318 : ∀ j, Signs p3318 (bank3318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3319 := params 22
abbrev ray3319 := rays 22
def bank3319 : Fin 2 → Cell := twoBank p3319 ray3319
theorem signs3319 : ∀ j, Signs p3319 (bank3319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3320 := params 23
abbrev ray3320 := rays 23
def bank3320 : Fin 2 → Cell := twoBank p3320 ray3320
theorem signs3320 : ∀ j, Signs p3320 (bank3320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3321 := params 24
abbrev ray3321 := rays 24
def bank3321 : Fin 2 → Cell := twoBank p3321 ray3321
theorem signs3321 : ∀ j, Signs p3321 (bank3321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3322 := params 25
abbrev ray3322 := rays 25
def bank3322 : Fin 2 → Cell := twoBank p3322 ray3322
theorem signs3322 : ∀ j, Signs p3322 (bank3322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3323 := params 26
abbrev ray3323 := rays 26
def bank3323 : Fin 2 → Cell := twoBank p3323 ray3323
theorem signs3323 : ∀ j, Signs p3323 (bank3323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3324 := params 27
abbrev ray3324 := rays 27
def bank3324 : Fin 2 → Cell := twoBank p3324 ray3324
theorem signs3324 : ∀ j, Signs p3324 (bank3324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3325 := params 28
abbrev ray3325 := rays 28
def bank3325 : Fin 2 → Cell := twoBank p3325 ray3325
theorem signs3325 : ∀ j, Signs p3325 (bank3325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3326 := params 29
abbrev ray3326 := rays 29
def bank3326 : Fin 2 → Cell := twoBank p3326 ray3326
theorem signs3326 : ∀ j, Signs p3326 (bank3326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3327 := params 30
abbrev ray3327 := rays 30
def bank3327 : Fin 2 → Cell := twoBank p3327 ray3327
theorem signs3327 : ∀ j, Signs p3327 (bank3327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3328 := params 31
abbrev ray3328 := rays 31
def bank3328 : Fin 2 → Cell := twoBank p3328 ray3328
theorem signs3328 : ∀ j, Signs p3328 (bank3328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03297_03328
