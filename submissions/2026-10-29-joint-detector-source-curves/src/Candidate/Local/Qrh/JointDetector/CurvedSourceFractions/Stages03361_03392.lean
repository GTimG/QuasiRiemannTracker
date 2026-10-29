/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03361_03392
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99422587150072,99422371661163,99422156146344,99421940605615,99421725038978,99421509446434,99421293827984,99421078183629,99420862513371,99420646817211,99420431095150,99420215347189,99419999573329,99419783773572,99419567947919,99419352096371,99419136218929,99418920315595,99418704386370,99418488431255,99418272450251,99418056443359,99417840410581,99417624351918,99417408267371,99417192156941,99416976020629,99416759858437,99416543670366,99416327456417,99416111216591,99415894950890,99415678659315]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3360+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3361 := params 0
abbrev ray3361 := rays 0
def bank3361 : Fin 2 → Cell := twoBank p3361 ray3361
theorem signs3361 : ∀ j, Signs p3361 (bank3361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3362 := params 1
abbrev ray3362 := rays 1
def bank3362 : Fin 2 → Cell := twoBank p3362 ray3362
theorem signs3362 : ∀ j, Signs p3362 (bank3362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3363 := params 2
abbrev ray3363 := rays 2
def bank3363 : Fin 2 → Cell := twoBank p3363 ray3363
theorem signs3363 : ∀ j, Signs p3363 (bank3363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3364 := params 3
abbrev ray3364 := rays 3
def bank3364 : Fin 2 → Cell := twoBank p3364 ray3364
theorem signs3364 : ∀ j, Signs p3364 (bank3364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3365 := params 4
abbrev ray3365 := rays 4
def bank3365 : Fin 2 → Cell := twoBank p3365 ray3365
theorem signs3365 : ∀ j, Signs p3365 (bank3365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3366 := params 5
abbrev ray3366 := rays 5
def bank3366 : Fin 2 → Cell := twoBank p3366 ray3366
theorem signs3366 : ∀ j, Signs p3366 (bank3366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3367 := params 6
abbrev ray3367 := rays 6
def bank3367 : Fin 2 → Cell := twoBank p3367 ray3367
theorem signs3367 : ∀ j, Signs p3367 (bank3367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3368 := params 7
abbrev ray3368 := rays 7
def bank3368 : Fin 2 → Cell := twoBank p3368 ray3368
theorem signs3368 : ∀ j, Signs p3368 (bank3368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3369 := params 8
abbrev ray3369 := rays 8
def bank3369 : Fin 2 → Cell := twoBank p3369 ray3369
theorem signs3369 : ∀ j, Signs p3369 (bank3369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3370 := params 9
abbrev ray3370 := rays 9
def bank3370 : Fin 2 → Cell := twoBank p3370 ray3370
theorem signs3370 : ∀ j, Signs p3370 (bank3370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3371 := params 10
abbrev ray3371 := rays 10
def bank3371 : Fin 2 → Cell := twoBank p3371 ray3371
theorem signs3371 : ∀ j, Signs p3371 (bank3371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3372 := params 11
abbrev ray3372 := rays 11
def bank3372 : Fin 2 → Cell := twoBank p3372 ray3372
theorem signs3372 : ∀ j, Signs p3372 (bank3372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3373 := params 12
abbrev ray3373 := rays 12
def bank3373 : Fin 2 → Cell := twoBank p3373 ray3373
theorem signs3373 : ∀ j, Signs p3373 (bank3373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3374 := params 13
abbrev ray3374 := rays 13
def bank3374 : Fin 2 → Cell := twoBank p3374 ray3374
theorem signs3374 : ∀ j, Signs p3374 (bank3374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3375 := params 14
abbrev ray3375 := rays 14
def bank3375 : Fin 2 → Cell := twoBank p3375 ray3375
theorem signs3375 : ∀ j, Signs p3375 (bank3375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3376 := params 15
abbrev ray3376 := rays 15
def bank3376 : Fin 2 → Cell := twoBank p3376 ray3376
theorem signs3376 : ∀ j, Signs p3376 (bank3376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3377 := params 16
abbrev ray3377 := rays 16
def bank3377 : Fin 2 → Cell := twoBank p3377 ray3377
theorem signs3377 : ∀ j, Signs p3377 (bank3377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3378 := params 17
abbrev ray3378 := rays 17
def bank3378 : Fin 2 → Cell := twoBank p3378 ray3378
theorem signs3378 : ∀ j, Signs p3378 (bank3378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3379 := params 18
abbrev ray3379 := rays 18
def bank3379 : Fin 2 → Cell := twoBank p3379 ray3379
theorem signs3379 : ∀ j, Signs p3379 (bank3379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3380 := params 19
abbrev ray3380 := rays 19
def bank3380 : Fin 2 → Cell := twoBank p3380 ray3380
theorem signs3380 : ∀ j, Signs p3380 (bank3380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3381 := params 20
abbrev ray3381 := rays 20
def bank3381 : Fin 2 → Cell := twoBank p3381 ray3381
theorem signs3381 : ∀ j, Signs p3381 (bank3381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3382 := params 21
abbrev ray3382 := rays 21
def bank3382 : Fin 2 → Cell := twoBank p3382 ray3382
theorem signs3382 : ∀ j, Signs p3382 (bank3382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3383 := params 22
abbrev ray3383 := rays 22
def bank3383 : Fin 2 → Cell := twoBank p3383 ray3383
theorem signs3383 : ∀ j, Signs p3383 (bank3383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3384 := params 23
abbrev ray3384 := rays 23
def bank3384 : Fin 2 → Cell := twoBank p3384 ray3384
theorem signs3384 : ∀ j, Signs p3384 (bank3384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3385 := params 24
abbrev ray3385 := rays 24
def bank3385 : Fin 2 → Cell := twoBank p3385 ray3385
theorem signs3385 : ∀ j, Signs p3385 (bank3385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3386 := params 25
abbrev ray3386 := rays 25
def bank3386 : Fin 2 → Cell := twoBank p3386 ray3386
theorem signs3386 : ∀ j, Signs p3386 (bank3386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3387 := params 26
abbrev ray3387 := rays 26
def bank3387 : Fin 2 → Cell := twoBank p3387 ray3387
theorem signs3387 : ∀ j, Signs p3387 (bank3387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3388 := params 27
abbrev ray3388 := rays 27
def bank3388 : Fin 2 → Cell := twoBank p3388 ray3388
theorem signs3388 : ∀ j, Signs p3388 (bank3388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3389 := params 28
abbrev ray3389 := rays 28
def bank3389 : Fin 2 → Cell := twoBank p3389 ray3389
theorem signs3389 : ∀ j, Signs p3389 (bank3389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3390 := params 29
abbrev ray3390 := rays 29
def bank3390 : Fin 2 → Cell := twoBank p3390 ray3390
theorem signs3390 : ∀ j, Signs p3390 (bank3390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3391 := params 30
abbrev ray3391 := rays 30
def bank3391 : Fin 2 → Cell := twoBank p3391 ray3391
theorem signs3391 : ∀ j, Signs p3391 (bank3391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3392 := params 31
abbrev ray3392 := rays 31
def bank3392 : Fin 2 → Cell := twoBank p3392 ray3392
theorem signs3392 : ∀ j, Signs p3392 (bank3392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03361_03392
