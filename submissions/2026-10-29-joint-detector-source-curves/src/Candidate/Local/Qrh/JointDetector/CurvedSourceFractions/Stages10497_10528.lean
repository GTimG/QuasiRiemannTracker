/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10497_10528
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97285412376892,97285035720385,97284659043807,97284282347160,97283905630444,97283528893659,97283152136806,97282775359885,97282398562897,97282021745842,97281644908721,97281268051535,97280891174283,97280514276967,97280137359587,97279760422143,97279383464636,97279006487067,97278629489436,97278252471744,97277875433991,97277498376177,97277121298304,97276744200371,97276367082379,97275989944329,97275612786221,97275235608056,97274858409834,97274481191556,97274103953222,97273726694833,97273349416390]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10496+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10497 := params 0
abbrev ray10497 := rays 0
def bank10497 : Fin 2 → Cell := twoBank p10497 ray10497
theorem signs10497 : ∀ j, Signs p10497 (bank10497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10498 := params 1
abbrev ray10498 := rays 1
def bank10498 : Fin 2 → Cell := twoBank p10498 ray10498
theorem signs10498 : ∀ j, Signs p10498 (bank10498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10499 := params 2
abbrev ray10499 := rays 2
def bank10499 : Fin 2 → Cell := twoBank p10499 ray10499
theorem signs10499 : ∀ j, Signs p10499 (bank10499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10500 := params 3
abbrev ray10500 := rays 3
def bank10500 : Fin 2 → Cell := twoBank p10500 ray10500
theorem signs10500 : ∀ j, Signs p10500 (bank10500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10501 := params 4
abbrev ray10501 := rays 4
def bank10501 : Fin 2 → Cell := twoBank p10501 ray10501
theorem signs10501 : ∀ j, Signs p10501 (bank10501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10502 := params 5
abbrev ray10502 := rays 5
def bank10502 : Fin 2 → Cell := twoBank p10502 ray10502
theorem signs10502 : ∀ j, Signs p10502 (bank10502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10503 := params 6
abbrev ray10503 := rays 6
def bank10503 : Fin 2 → Cell := twoBank p10503 ray10503
theorem signs10503 : ∀ j, Signs p10503 (bank10503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10504 := params 7
abbrev ray10504 := rays 7
def bank10504 : Fin 2 → Cell := twoBank p10504 ray10504
theorem signs10504 : ∀ j, Signs p10504 (bank10504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10505 := params 8
abbrev ray10505 := rays 8
def bank10505 : Fin 2 → Cell := twoBank p10505 ray10505
theorem signs10505 : ∀ j, Signs p10505 (bank10505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10506 := params 9
abbrev ray10506 := rays 9
def bank10506 : Fin 2 → Cell := twoBank p10506 ray10506
theorem signs10506 : ∀ j, Signs p10506 (bank10506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10507 := params 10
abbrev ray10507 := rays 10
def bank10507 : Fin 2 → Cell := twoBank p10507 ray10507
theorem signs10507 : ∀ j, Signs p10507 (bank10507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10508 := params 11
abbrev ray10508 := rays 11
def bank10508 : Fin 2 → Cell := twoBank p10508 ray10508
theorem signs10508 : ∀ j, Signs p10508 (bank10508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10509 := params 12
abbrev ray10509 := rays 12
def bank10509 : Fin 2 → Cell := twoBank p10509 ray10509
theorem signs10509 : ∀ j, Signs p10509 (bank10509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10510 := params 13
abbrev ray10510 := rays 13
def bank10510 : Fin 2 → Cell := twoBank p10510 ray10510
theorem signs10510 : ∀ j, Signs p10510 (bank10510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10511 := params 14
abbrev ray10511 := rays 14
def bank10511 : Fin 2 → Cell := twoBank p10511 ray10511
theorem signs10511 : ∀ j, Signs p10511 (bank10511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10512 := params 15
abbrev ray10512 := rays 15
def bank10512 : Fin 2 → Cell := twoBank p10512 ray10512
theorem signs10512 : ∀ j, Signs p10512 (bank10512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10513 := params 16
abbrev ray10513 := rays 16
def bank10513 : Fin 2 → Cell := twoBank p10513 ray10513
theorem signs10513 : ∀ j, Signs p10513 (bank10513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10514 := params 17
abbrev ray10514 := rays 17
def bank10514 : Fin 2 → Cell := twoBank p10514 ray10514
theorem signs10514 : ∀ j, Signs p10514 (bank10514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10515 := params 18
abbrev ray10515 := rays 18
def bank10515 : Fin 2 → Cell := twoBank p10515 ray10515
theorem signs10515 : ∀ j, Signs p10515 (bank10515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10516 := params 19
abbrev ray10516 := rays 19
def bank10516 : Fin 2 → Cell := twoBank p10516 ray10516
theorem signs10516 : ∀ j, Signs p10516 (bank10516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10517 := params 20
abbrev ray10517 := rays 20
def bank10517 : Fin 2 → Cell := twoBank p10517 ray10517
theorem signs10517 : ∀ j, Signs p10517 (bank10517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10518 := params 21
abbrev ray10518 := rays 21
def bank10518 : Fin 2 → Cell := twoBank p10518 ray10518
theorem signs10518 : ∀ j, Signs p10518 (bank10518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10519 := params 22
abbrev ray10519 := rays 22
def bank10519 : Fin 2 → Cell := twoBank p10519 ray10519
theorem signs10519 : ∀ j, Signs p10519 (bank10519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10520 := params 23
abbrev ray10520 := rays 23
def bank10520 : Fin 2 → Cell := twoBank p10520 ray10520
theorem signs10520 : ∀ j, Signs p10520 (bank10520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10521 := params 24
abbrev ray10521 := rays 24
def bank10521 : Fin 2 → Cell := twoBank p10521 ray10521
theorem signs10521 : ∀ j, Signs p10521 (bank10521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10522 := params 25
abbrev ray10522 := rays 25
def bank10522 : Fin 2 → Cell := twoBank p10522 ray10522
theorem signs10522 : ∀ j, Signs p10522 (bank10522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10523 := params 26
abbrev ray10523 := rays 26
def bank10523 : Fin 2 → Cell := twoBank p10523 ray10523
theorem signs10523 : ∀ j, Signs p10523 (bank10523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10524 := params 27
abbrev ray10524 := rays 27
def bank10524 : Fin 2 → Cell := twoBank p10524 ray10524
theorem signs10524 : ∀ j, Signs p10524 (bank10524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10525 := params 28
abbrev ray10525 := rays 28
def bank10525 : Fin 2 → Cell := twoBank p10525 ray10525
theorem signs10525 : ∀ j, Signs p10525 (bank10525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10526 := params 29
abbrev ray10526 := rays 29
def bank10526 : Fin 2 → Cell := twoBank p10526 ray10526
theorem signs10526 : ∀ j, Signs p10526 (bank10526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10527 := params 30
abbrev ray10527 := rays 30
def bank10527 : Fin 2 → Cell := twoBank p10527 ray10527
theorem signs10527 : ∀ j, Signs p10527 (bank10527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10528 := params 31
abbrev ray10528 := rays 31
def bank10528 : Fin 2 → Cell := twoBank p10528 ray10528
theorem signs10528 : ∀ j, Signs p10528 (bank10528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10497_10528
