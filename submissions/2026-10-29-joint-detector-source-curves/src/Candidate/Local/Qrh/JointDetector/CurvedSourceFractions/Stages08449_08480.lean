/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08449_08480
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98013898202411,98013563838826,98013229453961,98012895047817,98012560620395,98012226171695,98011891701718,98011557210465,98011222697936,98010888164132,98010553609054,98010219032702,98009884435077,98009549816179,98009215176010,98008880514570,98008545831859,98008211127879,98007876402630,98007541656112,98007206888326,98006872099273,98006537288954,98006202457369,98005867604519,98005532730405,98005197835027,98004862918386,98004527980482,98004193021317,98003858040891,98003523039204,98003188016257]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8448+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8449 := params 0
abbrev ray8449 := rays 0
def bank8449 : Fin 2 → Cell := twoBank p8449 ray8449
theorem signs8449 : ∀ j, Signs p8449 (bank8449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8450 := params 1
abbrev ray8450 := rays 1
def bank8450 : Fin 2 → Cell := twoBank p8450 ray8450
theorem signs8450 : ∀ j, Signs p8450 (bank8450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8451 := params 2
abbrev ray8451 := rays 2
def bank8451 : Fin 2 → Cell := twoBank p8451 ray8451
theorem signs8451 : ∀ j, Signs p8451 (bank8451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8452 := params 3
abbrev ray8452 := rays 3
def bank8452 : Fin 2 → Cell := twoBank p8452 ray8452
theorem signs8452 : ∀ j, Signs p8452 (bank8452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8453 := params 4
abbrev ray8453 := rays 4
def bank8453 : Fin 2 → Cell := twoBank p8453 ray8453
theorem signs8453 : ∀ j, Signs p8453 (bank8453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8454 := params 5
abbrev ray8454 := rays 5
def bank8454 : Fin 2 → Cell := twoBank p8454 ray8454
theorem signs8454 : ∀ j, Signs p8454 (bank8454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8455 := params 6
abbrev ray8455 := rays 6
def bank8455 : Fin 2 → Cell := twoBank p8455 ray8455
theorem signs8455 : ∀ j, Signs p8455 (bank8455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8456 := params 7
abbrev ray8456 := rays 7
def bank8456 : Fin 2 → Cell := twoBank p8456 ray8456
theorem signs8456 : ∀ j, Signs p8456 (bank8456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8457 := params 8
abbrev ray8457 := rays 8
def bank8457 : Fin 2 → Cell := twoBank p8457 ray8457
theorem signs8457 : ∀ j, Signs p8457 (bank8457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8458 := params 9
abbrev ray8458 := rays 9
def bank8458 : Fin 2 → Cell := twoBank p8458 ray8458
theorem signs8458 : ∀ j, Signs p8458 (bank8458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8459 := params 10
abbrev ray8459 := rays 10
def bank8459 : Fin 2 → Cell := twoBank p8459 ray8459
theorem signs8459 : ∀ j, Signs p8459 (bank8459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8460 := params 11
abbrev ray8460 := rays 11
def bank8460 : Fin 2 → Cell := twoBank p8460 ray8460
theorem signs8460 : ∀ j, Signs p8460 (bank8460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8461 := params 12
abbrev ray8461 := rays 12
def bank8461 : Fin 2 → Cell := twoBank p8461 ray8461
theorem signs8461 : ∀ j, Signs p8461 (bank8461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8462 := params 13
abbrev ray8462 := rays 13
def bank8462 : Fin 2 → Cell := twoBank p8462 ray8462
theorem signs8462 : ∀ j, Signs p8462 (bank8462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8463 := params 14
abbrev ray8463 := rays 14
def bank8463 : Fin 2 → Cell := twoBank p8463 ray8463
theorem signs8463 : ∀ j, Signs p8463 (bank8463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8464 := params 15
abbrev ray8464 := rays 15
def bank8464 : Fin 2 → Cell := twoBank p8464 ray8464
theorem signs8464 : ∀ j, Signs p8464 (bank8464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8465 := params 16
abbrev ray8465 := rays 16
def bank8465 : Fin 2 → Cell := twoBank p8465 ray8465
theorem signs8465 : ∀ j, Signs p8465 (bank8465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8466 := params 17
abbrev ray8466 := rays 17
def bank8466 : Fin 2 → Cell := twoBank p8466 ray8466
theorem signs8466 : ∀ j, Signs p8466 (bank8466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8467 := params 18
abbrev ray8467 := rays 18
def bank8467 : Fin 2 → Cell := twoBank p8467 ray8467
theorem signs8467 : ∀ j, Signs p8467 (bank8467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8468 := params 19
abbrev ray8468 := rays 19
def bank8468 : Fin 2 → Cell := twoBank p8468 ray8468
theorem signs8468 : ∀ j, Signs p8468 (bank8468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8469 := params 20
abbrev ray8469 := rays 20
def bank8469 : Fin 2 → Cell := twoBank p8469 ray8469
theorem signs8469 : ∀ j, Signs p8469 (bank8469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8470 := params 21
abbrev ray8470 := rays 21
def bank8470 : Fin 2 → Cell := twoBank p8470 ray8470
theorem signs8470 : ∀ j, Signs p8470 (bank8470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8471 := params 22
abbrev ray8471 := rays 22
def bank8471 : Fin 2 → Cell := twoBank p8471 ray8471
theorem signs8471 : ∀ j, Signs p8471 (bank8471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8472 := params 23
abbrev ray8472 := rays 23
def bank8472 : Fin 2 → Cell := twoBank p8472 ray8472
theorem signs8472 : ∀ j, Signs p8472 (bank8472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8473 := params 24
abbrev ray8473 := rays 24
def bank8473 : Fin 2 → Cell := twoBank p8473 ray8473
theorem signs8473 : ∀ j, Signs p8473 (bank8473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8474 := params 25
abbrev ray8474 := rays 25
def bank8474 : Fin 2 → Cell := twoBank p8474 ray8474
theorem signs8474 : ∀ j, Signs p8474 (bank8474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8475 := params 26
abbrev ray8475 := rays 26
def bank8475 : Fin 2 → Cell := twoBank p8475 ray8475
theorem signs8475 : ∀ j, Signs p8475 (bank8475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8476 := params 27
abbrev ray8476 := rays 27
def bank8476 : Fin 2 → Cell := twoBank p8476 ray8476
theorem signs8476 : ∀ j, Signs p8476 (bank8476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8477 := params 28
abbrev ray8477 := rays 28
def bank8477 : Fin 2 → Cell := twoBank p8477 ray8477
theorem signs8477 : ∀ j, Signs p8477 (bank8477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8478 := params 29
abbrev ray8478 := rays 29
def bank8478 : Fin 2 → Cell := twoBank p8478 ray8478
theorem signs8478 : ∀ j, Signs p8478 (bank8478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8479 := params 30
abbrev ray8479 := rays 30
def bank8479 : Fin 2 → Cell := twoBank p8479 ray8479
theorem signs8479 : ∀ j, Signs p8479 (bank8479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8480 := params 31
abbrev ray8480 := rays 31
def bank8480 : Fin 2 → Cell := twoBank p8480 ray8480
theorem signs8480 : ∀ j, Signs p8480 (bank8480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08449_08480
