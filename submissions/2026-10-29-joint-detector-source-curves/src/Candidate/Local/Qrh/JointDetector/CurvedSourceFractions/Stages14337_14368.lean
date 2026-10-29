/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14337_14368
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95698456579933,95698009922172,95697563248256,95697116558184,95696669851957,95696223129575,95695776391037,95695329636345,95694882865498,95694436078496,95693989275340,95693542456030,95693095620565,95692648768947,95692201901175,95691755017249,95691308117170,95690861200937,95690414268551,95689967320012,95689520355320,95689073374476,95688626377479,95688179364330,95687732335029,95687285289576,95686838227971,95686391150214,95685944056305,95685496946245,95685049820034,95684602677672,95684155519159]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14336+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14337 := params 0
abbrev ray14337 := rays 0
def bank14337 : Fin 1 → Cell := oneBank p14337 ray14337
theorem signs14337 : ∀ j, Signs p14337 (bank14337 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14338 := params 1
abbrev ray14338 := rays 1
def bank14338 : Fin 1 → Cell := oneBank p14338 ray14338
theorem signs14338 : ∀ j, Signs p14338 (bank14338 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14339 := params 2
abbrev ray14339 := rays 2
def bank14339 : Fin 1 → Cell := oneBank p14339 ray14339
theorem signs14339 : ∀ j, Signs p14339 (bank14339 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14340 := params 3
abbrev ray14340 := rays 3
def bank14340 : Fin 1 → Cell := oneBank p14340 ray14340
theorem signs14340 : ∀ j, Signs p14340 (bank14340 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14341 := params 4
abbrev ray14341 := rays 4
def bank14341 : Fin 1 → Cell := oneBank p14341 ray14341
theorem signs14341 : ∀ j, Signs p14341 (bank14341 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14342 := params 5
abbrev ray14342 := rays 5
def bank14342 : Fin 1 → Cell := oneBank p14342 ray14342
theorem signs14342 : ∀ j, Signs p14342 (bank14342 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14343 := params 6
abbrev ray14343 := rays 6
def bank14343 : Fin 1 → Cell := oneBank p14343 ray14343
theorem signs14343 : ∀ j, Signs p14343 (bank14343 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14344 := params 7
abbrev ray14344 := rays 7
def bank14344 : Fin 1 → Cell := oneBank p14344 ray14344
theorem signs14344 : ∀ j, Signs p14344 (bank14344 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14345 := params 8
abbrev ray14345 := rays 8
def bank14345 : Fin 1 → Cell := oneBank p14345 ray14345
theorem signs14345 : ∀ j, Signs p14345 (bank14345 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14346 := params 9
abbrev ray14346 := rays 9
def bank14346 : Fin 1 → Cell := oneBank p14346 ray14346
theorem signs14346 : ∀ j, Signs p14346 (bank14346 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14347 := params 10
abbrev ray14347 := rays 10
def bank14347 : Fin 1 → Cell := oneBank p14347 ray14347
theorem signs14347 : ∀ j, Signs p14347 (bank14347 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14348 := params 11
abbrev ray14348 := rays 11
def bank14348 : Fin 1 → Cell := oneBank p14348 ray14348
theorem signs14348 : ∀ j, Signs p14348 (bank14348 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14349 := params 12
abbrev ray14349 := rays 12
def bank14349 : Fin 1 → Cell := oneBank p14349 ray14349
theorem signs14349 : ∀ j, Signs p14349 (bank14349 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14350 := params 13
abbrev ray14350 := rays 13
def bank14350 : Fin 1 → Cell := oneBank p14350 ray14350
theorem signs14350 : ∀ j, Signs p14350 (bank14350 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14351 := params 14
abbrev ray14351 := rays 14
def bank14351 : Fin 1 → Cell := oneBank p14351 ray14351
theorem signs14351 : ∀ j, Signs p14351 (bank14351 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14352 := params 15
abbrev ray14352 := rays 15
def bank14352 : Fin 1 → Cell := oneBank p14352 ray14352
theorem signs14352 : ∀ j, Signs p14352 (bank14352 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14353 := params 16
abbrev ray14353 := rays 16
def bank14353 : Fin 1 → Cell := oneBank p14353 ray14353
theorem signs14353 : ∀ j, Signs p14353 (bank14353 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14354 := params 17
abbrev ray14354 := rays 17
def bank14354 : Fin 1 → Cell := oneBank p14354 ray14354
theorem signs14354 : ∀ j, Signs p14354 (bank14354 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14355 := params 18
abbrev ray14355 := rays 18
def bank14355 : Fin 1 → Cell := oneBank p14355 ray14355
theorem signs14355 : ∀ j, Signs p14355 (bank14355 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14356 := params 19
abbrev ray14356 := rays 19
def bank14356 : Fin 1 → Cell := oneBank p14356 ray14356
theorem signs14356 : ∀ j, Signs p14356 (bank14356 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14357 := params 20
abbrev ray14357 := rays 20
def bank14357 : Fin 1 → Cell := oneBank p14357 ray14357
theorem signs14357 : ∀ j, Signs p14357 (bank14357 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14358 := params 21
abbrev ray14358 := rays 21
def bank14358 : Fin 1 → Cell := oneBank p14358 ray14358
theorem signs14358 : ∀ j, Signs p14358 (bank14358 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14359 := params 22
abbrev ray14359 := rays 22
def bank14359 : Fin 1 → Cell := oneBank p14359 ray14359
theorem signs14359 : ∀ j, Signs p14359 (bank14359 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14360 := params 23
abbrev ray14360 := rays 23
def bank14360 : Fin 1 → Cell := oneBank p14360 ray14360
theorem signs14360 : ∀ j, Signs p14360 (bank14360 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14361 := params 24
abbrev ray14361 := rays 24
def bank14361 : Fin 1 → Cell := oneBank p14361 ray14361
theorem signs14361 : ∀ j, Signs p14361 (bank14361 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14362 := params 25
abbrev ray14362 := rays 25
def bank14362 : Fin 1 → Cell := oneBank p14362 ray14362
theorem signs14362 : ∀ j, Signs p14362 (bank14362 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14363 := params 26
abbrev ray14363 := rays 26
def bank14363 : Fin 1 → Cell := oneBank p14363 ray14363
theorem signs14363 : ∀ j, Signs p14363 (bank14363 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14364 := params 27
abbrev ray14364 := rays 27
def bank14364 : Fin 1 → Cell := oneBank p14364 ray14364
theorem signs14364 : ∀ j, Signs p14364 (bank14364 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14365 := params 28
abbrev ray14365 := rays 28
def bank14365 : Fin 1 → Cell := oneBank p14365 ray14365
theorem signs14365 : ∀ j, Signs p14365 (bank14365 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14366 := params 29
abbrev ray14366 := rays 29
def bank14366 : Fin 1 → Cell := oneBank p14366 ray14366
theorem signs14366 : ∀ j, Signs p14366 (bank14366 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14367 := params 30
abbrev ray14367 := rays 30
def bank14367 : Fin 1 → Cell := oneBank p14367 ray14367
theorem signs14367 : ∀ j, Signs p14367 (bank14367 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14368 := params 31
abbrev ray14368 := rays 31
def bank14368 : Fin 1 → Cell := oneBank p14368 ray14368
theorem signs14368 : ∀ j, Signs p14368 (bank14368 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14337_14368
