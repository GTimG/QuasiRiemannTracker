/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03425_03456
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99408743674549,99408526529803,99408309359224,99408092162813,99407874940571,99407657692500,99407440418601,99407223118875,99407005793323,99406788441946,99406571064746,99406353661723,99406136232879,99405918778216,99405701297734,99405483791435,99405266259319,99405048701388,99404831117644,99404613508087,99404395872719,99404178211541,99403960524554,99403742811759,99403525073157,99403307308750,99403089518539,99402871702525,99402653860709,99402435993093,99402218099677,99402000180463,99401782235452]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3424+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3425 := params 0
abbrev ray3425 := rays 0
def bank3425 : Fin 2 → Cell := twoBank p3425 ray3425
theorem signs3425 : ∀ j, Signs p3425 (bank3425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3426 := params 1
abbrev ray3426 := rays 1
def bank3426 : Fin 2 → Cell := twoBank p3426 ray3426
theorem signs3426 : ∀ j, Signs p3426 (bank3426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3427 := params 2
abbrev ray3427 := rays 2
def bank3427 : Fin 2 → Cell := twoBank p3427 ray3427
theorem signs3427 : ∀ j, Signs p3427 (bank3427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3428 := params 3
abbrev ray3428 := rays 3
def bank3428 : Fin 2 → Cell := twoBank p3428 ray3428
theorem signs3428 : ∀ j, Signs p3428 (bank3428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3429 := params 4
abbrev ray3429 := rays 4
def bank3429 : Fin 2 → Cell := twoBank p3429 ray3429
theorem signs3429 : ∀ j, Signs p3429 (bank3429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3430 := params 5
abbrev ray3430 := rays 5
def bank3430 : Fin 2 → Cell := twoBank p3430 ray3430
theorem signs3430 : ∀ j, Signs p3430 (bank3430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3431 := params 6
abbrev ray3431 := rays 6
def bank3431 : Fin 2 → Cell := twoBank p3431 ray3431
theorem signs3431 : ∀ j, Signs p3431 (bank3431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3432 := params 7
abbrev ray3432 := rays 7
def bank3432 : Fin 2 → Cell := twoBank p3432 ray3432
theorem signs3432 : ∀ j, Signs p3432 (bank3432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3433 := params 8
abbrev ray3433 := rays 8
def bank3433 : Fin 2 → Cell := twoBank p3433 ray3433
theorem signs3433 : ∀ j, Signs p3433 (bank3433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3434 := params 9
abbrev ray3434 := rays 9
def bank3434 : Fin 2 → Cell := twoBank p3434 ray3434
theorem signs3434 : ∀ j, Signs p3434 (bank3434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3435 := params 10
abbrev ray3435 := rays 10
def bank3435 : Fin 2 → Cell := twoBank p3435 ray3435
theorem signs3435 : ∀ j, Signs p3435 (bank3435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3436 := params 11
abbrev ray3436 := rays 11
def bank3436 : Fin 2 → Cell := twoBank p3436 ray3436
theorem signs3436 : ∀ j, Signs p3436 (bank3436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3437 := params 12
abbrev ray3437 := rays 12
def bank3437 : Fin 2 → Cell := twoBank p3437 ray3437
theorem signs3437 : ∀ j, Signs p3437 (bank3437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3438 := params 13
abbrev ray3438 := rays 13
def bank3438 : Fin 2 → Cell := twoBank p3438 ray3438
theorem signs3438 : ∀ j, Signs p3438 (bank3438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3439 := params 14
abbrev ray3439 := rays 14
def bank3439 : Fin 2 → Cell := twoBank p3439 ray3439
theorem signs3439 : ∀ j, Signs p3439 (bank3439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3440 := params 15
abbrev ray3440 := rays 15
def bank3440 : Fin 2 → Cell := twoBank p3440 ray3440
theorem signs3440 : ∀ j, Signs p3440 (bank3440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3441 := params 16
abbrev ray3441 := rays 16
def bank3441 : Fin 2 → Cell := twoBank p3441 ray3441
theorem signs3441 : ∀ j, Signs p3441 (bank3441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3442 := params 17
abbrev ray3442 := rays 17
def bank3442 : Fin 2 → Cell := twoBank p3442 ray3442
theorem signs3442 : ∀ j, Signs p3442 (bank3442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3443 := params 18
abbrev ray3443 := rays 18
def bank3443 : Fin 2 → Cell := twoBank p3443 ray3443
theorem signs3443 : ∀ j, Signs p3443 (bank3443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3444 := params 19
abbrev ray3444 := rays 19
def bank3444 : Fin 2 → Cell := twoBank p3444 ray3444
theorem signs3444 : ∀ j, Signs p3444 (bank3444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3445 := params 20
abbrev ray3445 := rays 20
def bank3445 : Fin 2 → Cell := twoBank p3445 ray3445
theorem signs3445 : ∀ j, Signs p3445 (bank3445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3446 := params 21
abbrev ray3446 := rays 21
def bank3446 : Fin 2 → Cell := twoBank p3446 ray3446
theorem signs3446 : ∀ j, Signs p3446 (bank3446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3447 := params 22
abbrev ray3447 := rays 22
def bank3447 : Fin 2 → Cell := twoBank p3447 ray3447
theorem signs3447 : ∀ j, Signs p3447 (bank3447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3448 := params 23
abbrev ray3448 := rays 23
def bank3448 : Fin 2 → Cell := twoBank p3448 ray3448
theorem signs3448 : ∀ j, Signs p3448 (bank3448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3449 := params 24
abbrev ray3449 := rays 24
def bank3449 : Fin 2 → Cell := twoBank p3449 ray3449
theorem signs3449 : ∀ j, Signs p3449 (bank3449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3450 := params 25
abbrev ray3450 := rays 25
def bank3450 : Fin 2 → Cell := twoBank p3450 ray3450
theorem signs3450 : ∀ j, Signs p3450 (bank3450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3451 := params 26
abbrev ray3451 := rays 26
def bank3451 : Fin 2 → Cell := twoBank p3451 ray3451
theorem signs3451 : ∀ j, Signs p3451 (bank3451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3452 := params 27
abbrev ray3452 := rays 27
def bank3452 : Fin 2 → Cell := twoBank p3452 ray3452
theorem signs3452 : ∀ j, Signs p3452 (bank3452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3453 := params 28
abbrev ray3453 := rays 28
def bank3453 : Fin 2 → Cell := twoBank p3453 ray3453
theorem signs3453 : ∀ j, Signs p3453 (bank3453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3454 := params 29
abbrev ray3454 := rays 29
def bank3454 : Fin 2 → Cell := twoBank p3454 ray3454
theorem signs3454 : ∀ j, Signs p3454 (bank3454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3455 := params 30
abbrev ray3455 := rays 30
def bank3455 : Fin 2 → Cell := twoBank p3455 ray3455
theorem signs3455 : ∀ j, Signs p3455 (bank3455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3456 := params 31
abbrev ray3456 := rays 31
def bank3456 : Fin 2 → Cell := twoBank p3456 ray3456
theorem signs3456 : ∀ j, Signs p3456 (bank3456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03425_03456
