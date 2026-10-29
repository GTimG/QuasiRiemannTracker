/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06529_06560
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98615801887300,98615509703224,98615217496438,98614925266943,98614633014740,98614340739830,98614048442213,98613756121890,98613463778862,98613171413130,98612879024695,98612586613558,98612294179719,98612001723179,98611709243939,98611416742000,98611124217363,98610831670028,98610539099997,98610246507270,98609953891848,98609661253732,98609368592923,98609075909421,98608783203228,98608490474344,98608197722770,98607904948507,98607612151555,98607319331916,98607026489590,98606733624578,98606440736881]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6528+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6529 := params 0
abbrev ray6529 := rays 0
def bank6529 : Fin 2 → Cell := twoBank p6529 ray6529
theorem signs6529 : ∀ j, Signs p6529 (bank6529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6530 := params 1
abbrev ray6530 := rays 1
def bank6530 : Fin 2 → Cell := twoBank p6530 ray6530
theorem signs6530 : ∀ j, Signs p6530 (bank6530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6531 := params 2
abbrev ray6531 := rays 2
def bank6531 : Fin 2 → Cell := twoBank p6531 ray6531
theorem signs6531 : ∀ j, Signs p6531 (bank6531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6532 := params 3
abbrev ray6532 := rays 3
def bank6532 : Fin 2 → Cell := twoBank p6532 ray6532
theorem signs6532 : ∀ j, Signs p6532 (bank6532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6533 := params 4
abbrev ray6533 := rays 4
def bank6533 : Fin 2 → Cell := twoBank p6533 ray6533
theorem signs6533 : ∀ j, Signs p6533 (bank6533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6534 := params 5
abbrev ray6534 := rays 5
def bank6534 : Fin 2 → Cell := twoBank p6534 ray6534
theorem signs6534 : ∀ j, Signs p6534 (bank6534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6535 := params 6
abbrev ray6535 := rays 6
def bank6535 : Fin 2 → Cell := twoBank p6535 ray6535
theorem signs6535 : ∀ j, Signs p6535 (bank6535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6536 := params 7
abbrev ray6536 := rays 7
def bank6536 : Fin 2 → Cell := twoBank p6536 ray6536
theorem signs6536 : ∀ j, Signs p6536 (bank6536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6537 := params 8
abbrev ray6537 := rays 8
def bank6537 : Fin 2 → Cell := twoBank p6537 ray6537
theorem signs6537 : ∀ j, Signs p6537 (bank6537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6538 := params 9
abbrev ray6538 := rays 9
def bank6538 : Fin 2 → Cell := twoBank p6538 ray6538
theorem signs6538 : ∀ j, Signs p6538 (bank6538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6539 := params 10
abbrev ray6539 := rays 10
def bank6539 : Fin 2 → Cell := twoBank p6539 ray6539
theorem signs6539 : ∀ j, Signs p6539 (bank6539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6540 := params 11
abbrev ray6540 := rays 11
def bank6540 : Fin 2 → Cell := twoBank p6540 ray6540
theorem signs6540 : ∀ j, Signs p6540 (bank6540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6541 := params 12
abbrev ray6541 := rays 12
def bank6541 : Fin 2 → Cell := twoBank p6541 ray6541
theorem signs6541 : ∀ j, Signs p6541 (bank6541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6542 := params 13
abbrev ray6542 := rays 13
def bank6542 : Fin 2 → Cell := twoBank p6542 ray6542
theorem signs6542 : ∀ j, Signs p6542 (bank6542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6543 := params 14
abbrev ray6543 := rays 14
def bank6543 : Fin 2 → Cell := twoBank p6543 ray6543
theorem signs6543 : ∀ j, Signs p6543 (bank6543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6544 := params 15
abbrev ray6544 := rays 15
def bank6544 : Fin 2 → Cell := twoBank p6544 ray6544
theorem signs6544 : ∀ j, Signs p6544 (bank6544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6545 := params 16
abbrev ray6545 := rays 16
def bank6545 : Fin 2 → Cell := twoBank p6545 ray6545
theorem signs6545 : ∀ j, Signs p6545 (bank6545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6546 := params 17
abbrev ray6546 := rays 17
def bank6546 : Fin 2 → Cell := twoBank p6546 ray6546
theorem signs6546 : ∀ j, Signs p6546 (bank6546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6547 := params 18
abbrev ray6547 := rays 18
def bank6547 : Fin 2 → Cell := twoBank p6547 ray6547
theorem signs6547 : ∀ j, Signs p6547 (bank6547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6548 := params 19
abbrev ray6548 := rays 19
def bank6548 : Fin 2 → Cell := twoBank p6548 ray6548
theorem signs6548 : ∀ j, Signs p6548 (bank6548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6549 := params 20
abbrev ray6549 := rays 20
def bank6549 : Fin 2 → Cell := twoBank p6549 ray6549
theorem signs6549 : ∀ j, Signs p6549 (bank6549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6550 := params 21
abbrev ray6550 := rays 21
def bank6550 : Fin 2 → Cell := twoBank p6550 ray6550
theorem signs6550 : ∀ j, Signs p6550 (bank6550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6551 := params 22
abbrev ray6551 := rays 22
def bank6551 : Fin 2 → Cell := twoBank p6551 ray6551
theorem signs6551 : ∀ j, Signs p6551 (bank6551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6552 := params 23
abbrev ray6552 := rays 23
def bank6552 : Fin 2 → Cell := twoBank p6552 ray6552
theorem signs6552 : ∀ j, Signs p6552 (bank6552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6553 := params 24
abbrev ray6553 := rays 24
def bank6553 : Fin 2 → Cell := twoBank p6553 ray6553
theorem signs6553 : ∀ j, Signs p6553 (bank6553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6554 := params 25
abbrev ray6554 := rays 25
def bank6554 : Fin 2 → Cell := twoBank p6554 ray6554
theorem signs6554 : ∀ j, Signs p6554 (bank6554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6555 := params 26
abbrev ray6555 := rays 26
def bank6555 : Fin 2 → Cell := twoBank p6555 ray6555
theorem signs6555 : ∀ j, Signs p6555 (bank6555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6556 := params 27
abbrev ray6556 := rays 27
def bank6556 : Fin 2 → Cell := twoBank p6556 ray6556
theorem signs6556 : ∀ j, Signs p6556 (bank6556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6557 := params 28
abbrev ray6557 := rays 28
def bank6557 : Fin 2 → Cell := twoBank p6557 ray6557
theorem signs6557 : ∀ j, Signs p6557 (bank6557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6558 := params 29
abbrev ray6558 := rays 29
def bank6558 : Fin 2 → Cell := twoBank p6558 ray6558
theorem signs6558 : ∀ j, Signs p6558 (bank6558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6559 := params 30
abbrev ray6559 := rays 30
def bank6559 : Fin 2 → Cell := twoBank p6559 ray6559
theorem signs6559 : ∀ j, Signs p6559 (bank6559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6560 := params 31
abbrev ray6560 := rays 31
def bank6560 : Fin 2 → Cell := twoBank p6560 ray6560
theorem signs6560 : ∀ j, Signs p6560 (bank6560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06529_06560
