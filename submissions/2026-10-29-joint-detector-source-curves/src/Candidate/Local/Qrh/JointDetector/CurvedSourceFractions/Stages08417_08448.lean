/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08417_08448
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98024586597489,98024252915205,98023919211620,98023585486734,98023251740549,98022917973065,98022584184282,98022250374202,98021916542825,98021582690151,98021248816182,98020914920918,98020581004359,98020247066507,98019913107362,98019579126925,98019245125196,98018911102176,98018577057866,98018242992266,98017908905377,98017574797200,98017240667735,98016906516983,98016572344945,98016238151621,98015903937012,98015569701119,98015235443942,98014901165482,98014566865740,98014232544716,98013898202411]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8416+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8417 := params 0
abbrev ray8417 := rays 0
def bank8417 : Fin 2 → Cell := twoBank p8417 ray8417
theorem signs8417 : ∀ j, Signs p8417 (bank8417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8418 := params 1
abbrev ray8418 := rays 1
def bank8418 : Fin 2 → Cell := twoBank p8418 ray8418
theorem signs8418 : ∀ j, Signs p8418 (bank8418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8419 := params 2
abbrev ray8419 := rays 2
def bank8419 : Fin 2 → Cell := twoBank p8419 ray8419
theorem signs8419 : ∀ j, Signs p8419 (bank8419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8420 := params 3
abbrev ray8420 := rays 3
def bank8420 : Fin 2 → Cell := twoBank p8420 ray8420
theorem signs8420 : ∀ j, Signs p8420 (bank8420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8421 := params 4
abbrev ray8421 := rays 4
def bank8421 : Fin 2 → Cell := twoBank p8421 ray8421
theorem signs8421 : ∀ j, Signs p8421 (bank8421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8422 := params 5
abbrev ray8422 := rays 5
def bank8422 : Fin 2 → Cell := twoBank p8422 ray8422
theorem signs8422 : ∀ j, Signs p8422 (bank8422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8423 := params 6
abbrev ray8423 := rays 6
def bank8423 : Fin 2 → Cell := twoBank p8423 ray8423
theorem signs8423 : ∀ j, Signs p8423 (bank8423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8424 := params 7
abbrev ray8424 := rays 7
def bank8424 : Fin 2 → Cell := twoBank p8424 ray8424
theorem signs8424 : ∀ j, Signs p8424 (bank8424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8425 := params 8
abbrev ray8425 := rays 8
def bank8425 : Fin 2 → Cell := twoBank p8425 ray8425
theorem signs8425 : ∀ j, Signs p8425 (bank8425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8426 := params 9
abbrev ray8426 := rays 9
def bank8426 : Fin 2 → Cell := twoBank p8426 ray8426
theorem signs8426 : ∀ j, Signs p8426 (bank8426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8427 := params 10
abbrev ray8427 := rays 10
def bank8427 : Fin 2 → Cell := twoBank p8427 ray8427
theorem signs8427 : ∀ j, Signs p8427 (bank8427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8428 := params 11
abbrev ray8428 := rays 11
def bank8428 : Fin 2 → Cell := twoBank p8428 ray8428
theorem signs8428 : ∀ j, Signs p8428 (bank8428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8429 := params 12
abbrev ray8429 := rays 12
def bank8429 : Fin 2 → Cell := twoBank p8429 ray8429
theorem signs8429 : ∀ j, Signs p8429 (bank8429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8430 := params 13
abbrev ray8430 := rays 13
def bank8430 : Fin 2 → Cell := twoBank p8430 ray8430
theorem signs8430 : ∀ j, Signs p8430 (bank8430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8431 := params 14
abbrev ray8431 := rays 14
def bank8431 : Fin 2 → Cell := twoBank p8431 ray8431
theorem signs8431 : ∀ j, Signs p8431 (bank8431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8432 := params 15
abbrev ray8432 := rays 15
def bank8432 : Fin 2 → Cell := twoBank p8432 ray8432
theorem signs8432 : ∀ j, Signs p8432 (bank8432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8433 := params 16
abbrev ray8433 := rays 16
def bank8433 : Fin 2 → Cell := twoBank p8433 ray8433
theorem signs8433 : ∀ j, Signs p8433 (bank8433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8434 := params 17
abbrev ray8434 := rays 17
def bank8434 : Fin 2 → Cell := twoBank p8434 ray8434
theorem signs8434 : ∀ j, Signs p8434 (bank8434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8435 := params 18
abbrev ray8435 := rays 18
def bank8435 : Fin 2 → Cell := twoBank p8435 ray8435
theorem signs8435 : ∀ j, Signs p8435 (bank8435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8436 := params 19
abbrev ray8436 := rays 19
def bank8436 : Fin 2 → Cell := twoBank p8436 ray8436
theorem signs8436 : ∀ j, Signs p8436 (bank8436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8437 := params 20
abbrev ray8437 := rays 20
def bank8437 : Fin 2 → Cell := twoBank p8437 ray8437
theorem signs8437 : ∀ j, Signs p8437 (bank8437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8438 := params 21
abbrev ray8438 := rays 21
def bank8438 : Fin 2 → Cell := twoBank p8438 ray8438
theorem signs8438 : ∀ j, Signs p8438 (bank8438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8439 := params 22
abbrev ray8439 := rays 22
def bank8439 : Fin 2 → Cell := twoBank p8439 ray8439
theorem signs8439 : ∀ j, Signs p8439 (bank8439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8440 := params 23
abbrev ray8440 := rays 23
def bank8440 : Fin 2 → Cell := twoBank p8440 ray8440
theorem signs8440 : ∀ j, Signs p8440 (bank8440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8441 := params 24
abbrev ray8441 := rays 24
def bank8441 : Fin 2 → Cell := twoBank p8441 ray8441
theorem signs8441 : ∀ j, Signs p8441 (bank8441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8442 := params 25
abbrev ray8442 := rays 25
def bank8442 : Fin 2 → Cell := twoBank p8442 ray8442
theorem signs8442 : ∀ j, Signs p8442 (bank8442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8443 := params 26
abbrev ray8443 := rays 26
def bank8443 : Fin 2 → Cell := twoBank p8443 ray8443
theorem signs8443 : ∀ j, Signs p8443 (bank8443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8444 := params 27
abbrev ray8444 := rays 27
def bank8444 : Fin 2 → Cell := twoBank p8444 ray8444
theorem signs8444 : ∀ j, Signs p8444 (bank8444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8445 := params 28
abbrev ray8445 := rays 28
def bank8445 : Fin 2 → Cell := twoBank p8445 ray8445
theorem signs8445 : ∀ j, Signs p8445 (bank8445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8446 := params 29
abbrev ray8446 := rays 29
def bank8446 : Fin 2 → Cell := twoBank p8446 ray8446
theorem signs8446 : ∀ j, Signs p8446 (bank8446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8447 := params 30
abbrev ray8447 := rays 30
def bank8447 : Fin 2 → Cell := twoBank p8447 ray8447
theorem signs8447 : ∀ j, Signs p8447 (bank8447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8448 := params 31
abbrev ray8448 := rays 31
def bank8448 : Fin 2 → Cell := twoBank p8448 ray8448
theorem signs8448 : ∀ j, Signs p8448 (bank8448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08417_08448
