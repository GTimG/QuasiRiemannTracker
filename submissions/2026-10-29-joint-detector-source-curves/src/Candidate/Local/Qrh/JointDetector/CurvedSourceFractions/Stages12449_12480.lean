/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12449_12480
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96512569737432,96512154820974,96511739885349,96511324930557,96510909956598,96510494963473,96510079951182,96509664919726,96509249869105,96508834799320,96508419710371,96508004602258,96507589474982,96507174328543,96506759162941,96506343978177,96505928774252,96505513551166,96505098308919,96504683047511,96504267766943,96503852467216,96503437148329,96503021810284,96502606453080,96502191076718,96501775681199,96501360266522,96500944832689,96500529379699,96500113907553,96499698416252,96499282905796]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12448+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12449 := params 0
abbrev ray12449 := rays 0
def bank12449 : Fin 2 → Cell := twoBank p12449 ray12449
theorem signs12449 : ∀ j, Signs p12449 (bank12449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12450 := params 1
abbrev ray12450 := rays 1
def bank12450 : Fin 2 → Cell := twoBank p12450 ray12450
theorem signs12450 : ∀ j, Signs p12450 (bank12450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12451 := params 2
abbrev ray12451 := rays 2
def bank12451 : Fin 2 → Cell := twoBank p12451 ray12451
theorem signs12451 : ∀ j, Signs p12451 (bank12451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12452 := params 3
abbrev ray12452 := rays 3
def bank12452 : Fin 2 → Cell := twoBank p12452 ray12452
theorem signs12452 : ∀ j, Signs p12452 (bank12452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12453 := params 4
abbrev ray12453 := rays 4
def bank12453 : Fin 2 → Cell := twoBank p12453 ray12453
theorem signs12453 : ∀ j, Signs p12453 (bank12453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12454 := params 5
abbrev ray12454 := rays 5
def bank12454 : Fin 2 → Cell := twoBank p12454 ray12454
theorem signs12454 : ∀ j, Signs p12454 (bank12454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12455 := params 6
abbrev ray12455 := rays 6
def bank12455 : Fin 2 → Cell := twoBank p12455 ray12455
theorem signs12455 : ∀ j, Signs p12455 (bank12455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12456 := params 7
abbrev ray12456 := rays 7
def bank12456 : Fin 2 → Cell := twoBank p12456 ray12456
theorem signs12456 : ∀ j, Signs p12456 (bank12456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12457 := params 8
abbrev ray12457 := rays 8
def bank12457 : Fin 2 → Cell := twoBank p12457 ray12457
theorem signs12457 : ∀ j, Signs p12457 (bank12457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12458 := params 9
abbrev ray12458 := rays 9
def bank12458 : Fin 2 → Cell := twoBank p12458 ray12458
theorem signs12458 : ∀ j, Signs p12458 (bank12458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12459 := params 10
abbrev ray12459 := rays 10
def bank12459 : Fin 2 → Cell := twoBank p12459 ray12459
theorem signs12459 : ∀ j, Signs p12459 (bank12459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12460 := params 11
abbrev ray12460 := rays 11
def bank12460 : Fin 2 → Cell := twoBank p12460 ray12460
theorem signs12460 : ∀ j, Signs p12460 (bank12460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12461 := params 12
abbrev ray12461 := rays 12
def bank12461 : Fin 2 → Cell := twoBank p12461 ray12461
theorem signs12461 : ∀ j, Signs p12461 (bank12461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12462 := params 13
abbrev ray12462 := rays 13
def bank12462 : Fin 2 → Cell := twoBank p12462 ray12462
theorem signs12462 : ∀ j, Signs p12462 (bank12462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12463 := params 14
abbrev ray12463 := rays 14
def bank12463 : Fin 2 → Cell := twoBank p12463 ray12463
theorem signs12463 : ∀ j, Signs p12463 (bank12463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12464 := params 15
abbrev ray12464 := rays 15
def bank12464 : Fin 2 → Cell := twoBank p12464 ray12464
theorem signs12464 : ∀ j, Signs p12464 (bank12464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12465 := params 16
abbrev ray12465 := rays 16
def bank12465 : Fin 2 → Cell := twoBank p12465 ray12465
theorem signs12465 : ∀ j, Signs p12465 (bank12465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12466 := params 17
abbrev ray12466 := rays 17
def bank12466 : Fin 2 → Cell := twoBank p12466 ray12466
theorem signs12466 : ∀ j, Signs p12466 (bank12466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12467 := params 18
abbrev ray12467 := rays 18
def bank12467 : Fin 2 → Cell := twoBank p12467 ray12467
theorem signs12467 : ∀ j, Signs p12467 (bank12467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12468 := params 19
abbrev ray12468 := rays 19
def bank12468 : Fin 2 → Cell := twoBank p12468 ray12468
theorem signs12468 : ∀ j, Signs p12468 (bank12468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12469 := params 20
abbrev ray12469 := rays 20
def bank12469 : Fin 2 → Cell := twoBank p12469 ray12469
theorem signs12469 : ∀ j, Signs p12469 (bank12469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12470 := params 21
abbrev ray12470 := rays 21
def bank12470 : Fin 2 → Cell := twoBank p12470 ray12470
theorem signs12470 : ∀ j, Signs p12470 (bank12470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12471 := params 22
abbrev ray12471 := rays 22
def bank12471 : Fin 2 → Cell := twoBank p12471 ray12471
theorem signs12471 : ∀ j, Signs p12471 (bank12471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12472 := params 23
abbrev ray12472 := rays 23
def bank12472 : Fin 2 → Cell := twoBank p12472 ray12472
theorem signs12472 : ∀ j, Signs p12472 (bank12472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12473 := params 24
abbrev ray12473 := rays 24
def bank12473 : Fin 2 → Cell := twoBank p12473 ray12473
theorem signs12473 : ∀ j, Signs p12473 (bank12473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12474 := params 25
abbrev ray12474 := rays 25
def bank12474 : Fin 2 → Cell := twoBank p12474 ray12474
theorem signs12474 : ∀ j, Signs p12474 (bank12474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12475 := params 26
abbrev ray12475 := rays 26
def bank12475 : Fin 2 → Cell := twoBank p12475 ray12475
theorem signs12475 : ∀ j, Signs p12475 (bank12475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12476 := params 27
abbrev ray12476 := rays 27
def bank12476 : Fin 2 → Cell := twoBank p12476 ray12476
theorem signs12476 : ∀ j, Signs p12476 (bank12476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12477 := params 28
abbrev ray12477 := rays 28
def bank12477 : Fin 2 → Cell := twoBank p12477 ray12477
theorem signs12477 : ∀ j, Signs p12477 (bank12477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12478 := params 29
abbrev ray12478 := rays 29
def bank12478 : Fin 2 → Cell := twoBank p12478 ray12478
theorem signs12478 : ∀ j, Signs p12478 (bank12478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12479 := params 30
abbrev ray12479 := rays 30
def bank12479 : Fin 2 → Cell := twoBank p12479 ray12479
theorem signs12479 : ∀ j, Signs p12479 (bank12479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12480 := params 31
abbrev ray12480 := rays 31
def bank12480 : Fin 2 → Cell := twoBank p12480 ray12480
theorem signs12480 : ∀ j, Signs p12480 (bank12480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12449_12480
