/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09505_09536
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97649082780143,97648726300652,97648369800542,97648013279813,97647656738465,97647300176500,97646943593917,97646586990718,97646230366903,97645873722472,97645517057427,97645160371767,97644803665494,97644446938608,97644090191109,97643733422998,97643376634276,97643019824943,97642662995000,97642306144447,97641949273286,97641592381516,97641235469138,97640878536153,97640521582562,97640164608364,97639807613561,97639450598153,97639093562141,97638736505525,97638379428306,97638022330485,97637665212062]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9504+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9505 := params 0
abbrev ray9505 := rays 0
def bank9505 : Fin 2 → Cell := twoBank p9505 ray9505
theorem signs9505 : ∀ j, Signs p9505 (bank9505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9506 := params 1
abbrev ray9506 := rays 1
def bank9506 : Fin 2 → Cell := twoBank p9506 ray9506
theorem signs9506 : ∀ j, Signs p9506 (bank9506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9507 := params 2
abbrev ray9507 := rays 2
def bank9507 : Fin 2 → Cell := twoBank p9507 ray9507
theorem signs9507 : ∀ j, Signs p9507 (bank9507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9508 := params 3
abbrev ray9508 := rays 3
def bank9508 : Fin 2 → Cell := twoBank p9508 ray9508
theorem signs9508 : ∀ j, Signs p9508 (bank9508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9509 := params 4
abbrev ray9509 := rays 4
def bank9509 : Fin 2 → Cell := twoBank p9509 ray9509
theorem signs9509 : ∀ j, Signs p9509 (bank9509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9510 := params 5
abbrev ray9510 := rays 5
def bank9510 : Fin 2 → Cell := twoBank p9510 ray9510
theorem signs9510 : ∀ j, Signs p9510 (bank9510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9511 := params 6
abbrev ray9511 := rays 6
def bank9511 : Fin 2 → Cell := twoBank p9511 ray9511
theorem signs9511 : ∀ j, Signs p9511 (bank9511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9512 := params 7
abbrev ray9512 := rays 7
def bank9512 : Fin 2 → Cell := twoBank p9512 ray9512
theorem signs9512 : ∀ j, Signs p9512 (bank9512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9513 := params 8
abbrev ray9513 := rays 8
def bank9513 : Fin 2 → Cell := twoBank p9513 ray9513
theorem signs9513 : ∀ j, Signs p9513 (bank9513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9514 := params 9
abbrev ray9514 := rays 9
def bank9514 : Fin 2 → Cell := twoBank p9514 ray9514
theorem signs9514 : ∀ j, Signs p9514 (bank9514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9515 := params 10
abbrev ray9515 := rays 10
def bank9515 : Fin 2 → Cell := twoBank p9515 ray9515
theorem signs9515 : ∀ j, Signs p9515 (bank9515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9516 := params 11
abbrev ray9516 := rays 11
def bank9516 : Fin 2 → Cell := twoBank p9516 ray9516
theorem signs9516 : ∀ j, Signs p9516 (bank9516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9517 := params 12
abbrev ray9517 := rays 12
def bank9517 : Fin 2 → Cell := twoBank p9517 ray9517
theorem signs9517 : ∀ j, Signs p9517 (bank9517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9518 := params 13
abbrev ray9518 := rays 13
def bank9518 : Fin 2 → Cell := twoBank p9518 ray9518
theorem signs9518 : ∀ j, Signs p9518 (bank9518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9519 := params 14
abbrev ray9519 := rays 14
def bank9519 : Fin 2 → Cell := twoBank p9519 ray9519
theorem signs9519 : ∀ j, Signs p9519 (bank9519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9520 := params 15
abbrev ray9520 := rays 15
def bank9520 : Fin 2 → Cell := twoBank p9520 ray9520
theorem signs9520 : ∀ j, Signs p9520 (bank9520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9521 := params 16
abbrev ray9521 := rays 16
def bank9521 : Fin 2 → Cell := twoBank p9521 ray9521
theorem signs9521 : ∀ j, Signs p9521 (bank9521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9522 := params 17
abbrev ray9522 := rays 17
def bank9522 : Fin 2 → Cell := twoBank p9522 ray9522
theorem signs9522 : ∀ j, Signs p9522 (bank9522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9523 := params 18
abbrev ray9523 := rays 18
def bank9523 : Fin 2 → Cell := twoBank p9523 ray9523
theorem signs9523 : ∀ j, Signs p9523 (bank9523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9524 := params 19
abbrev ray9524 := rays 19
def bank9524 : Fin 2 → Cell := twoBank p9524 ray9524
theorem signs9524 : ∀ j, Signs p9524 (bank9524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9525 := params 20
abbrev ray9525 := rays 20
def bank9525 : Fin 2 → Cell := twoBank p9525 ray9525
theorem signs9525 : ∀ j, Signs p9525 (bank9525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9526 := params 21
abbrev ray9526 := rays 21
def bank9526 : Fin 2 → Cell := twoBank p9526 ray9526
theorem signs9526 : ∀ j, Signs p9526 (bank9526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9527 := params 22
abbrev ray9527 := rays 22
def bank9527 : Fin 2 → Cell := twoBank p9527 ray9527
theorem signs9527 : ∀ j, Signs p9527 (bank9527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9528 := params 23
abbrev ray9528 := rays 23
def bank9528 : Fin 2 → Cell := twoBank p9528 ray9528
theorem signs9528 : ∀ j, Signs p9528 (bank9528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9529 := params 24
abbrev ray9529 := rays 24
def bank9529 : Fin 2 → Cell := twoBank p9529 ray9529
theorem signs9529 : ∀ j, Signs p9529 (bank9529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9530 := params 25
abbrev ray9530 := rays 25
def bank9530 : Fin 2 → Cell := twoBank p9530 ray9530
theorem signs9530 : ∀ j, Signs p9530 (bank9530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9531 := params 26
abbrev ray9531 := rays 26
def bank9531 : Fin 2 → Cell := twoBank p9531 ray9531
theorem signs9531 : ∀ j, Signs p9531 (bank9531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9532 := params 27
abbrev ray9532 := rays 27
def bank9532 : Fin 2 → Cell := twoBank p9532 ray9532
theorem signs9532 : ∀ j, Signs p9532 (bank9532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9533 := params 28
abbrev ray9533 := rays 28
def bank9533 : Fin 2 → Cell := twoBank p9533 ray9533
theorem signs9533 : ∀ j, Signs p9533 (bank9533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9534 := params 29
abbrev ray9534 := rays 29
def bank9534 : Fin 2 → Cell := twoBank p9534 ray9534
theorem signs9534 : ∀ j, Signs p9534 (bank9534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9535 := params 30
abbrev ray9535 := rays 30
def bank9535 : Fin 2 → Cell := twoBank p9535 ray9535
theorem signs9535 : ∀ j, Signs p9535 (bank9535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9536 := params 31
abbrev ray9536 := rays 31
def bank9536 : Fin 2 → Cell := twoBank p9536 ray9536
theorem signs9536 : ∀ j, Signs p9536 (bank9536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09505_09536
