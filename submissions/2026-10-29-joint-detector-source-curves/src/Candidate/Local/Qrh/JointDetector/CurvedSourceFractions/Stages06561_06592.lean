/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06561_06592
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98606440736881,98606147826500,98605854893436,98605561937689,98605268959261,98604975958152,98604682934363,98604389887894,98604096818747,98603803726923,98603510612422,98603217475245,98602924315393,98602631132867,98602337927667,98602044699795,98601751449251,98601458176036,98601164880151,98600871561596,98600578220373,98600284856482,98599991469925,98599698060702,98599404628813,98599111174260,98598817697044,98598524197165,98598230674624,98597937129422,98597643561560,98597349971039,98597056357859]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6560+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6561 := params 0
abbrev ray6561 := rays 0
def bank6561 : Fin 2 → Cell := twoBank p6561 ray6561
theorem signs6561 : ∀ j, Signs p6561 (bank6561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6562 := params 1
abbrev ray6562 := rays 1
def bank6562 : Fin 2 → Cell := twoBank p6562 ray6562
theorem signs6562 : ∀ j, Signs p6562 (bank6562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6563 := params 2
abbrev ray6563 := rays 2
def bank6563 : Fin 2 → Cell := twoBank p6563 ray6563
theorem signs6563 : ∀ j, Signs p6563 (bank6563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6564 := params 3
abbrev ray6564 := rays 3
def bank6564 : Fin 2 → Cell := twoBank p6564 ray6564
theorem signs6564 : ∀ j, Signs p6564 (bank6564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6565 := params 4
abbrev ray6565 := rays 4
def bank6565 : Fin 2 → Cell := twoBank p6565 ray6565
theorem signs6565 : ∀ j, Signs p6565 (bank6565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6566 := params 5
abbrev ray6566 := rays 5
def bank6566 : Fin 2 → Cell := twoBank p6566 ray6566
theorem signs6566 : ∀ j, Signs p6566 (bank6566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6567 := params 6
abbrev ray6567 := rays 6
def bank6567 : Fin 2 → Cell := twoBank p6567 ray6567
theorem signs6567 : ∀ j, Signs p6567 (bank6567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6568 := params 7
abbrev ray6568 := rays 7
def bank6568 : Fin 2 → Cell := twoBank p6568 ray6568
theorem signs6568 : ∀ j, Signs p6568 (bank6568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6569 := params 8
abbrev ray6569 := rays 8
def bank6569 : Fin 2 → Cell := twoBank p6569 ray6569
theorem signs6569 : ∀ j, Signs p6569 (bank6569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6570 := params 9
abbrev ray6570 := rays 9
def bank6570 : Fin 2 → Cell := twoBank p6570 ray6570
theorem signs6570 : ∀ j, Signs p6570 (bank6570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6571 := params 10
abbrev ray6571 := rays 10
def bank6571 : Fin 2 → Cell := twoBank p6571 ray6571
theorem signs6571 : ∀ j, Signs p6571 (bank6571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6572 := params 11
abbrev ray6572 := rays 11
def bank6572 : Fin 2 → Cell := twoBank p6572 ray6572
theorem signs6572 : ∀ j, Signs p6572 (bank6572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6573 := params 12
abbrev ray6573 := rays 12
def bank6573 : Fin 2 → Cell := twoBank p6573 ray6573
theorem signs6573 : ∀ j, Signs p6573 (bank6573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6574 := params 13
abbrev ray6574 := rays 13
def bank6574 : Fin 2 → Cell := twoBank p6574 ray6574
theorem signs6574 : ∀ j, Signs p6574 (bank6574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6575 := params 14
abbrev ray6575 := rays 14
def bank6575 : Fin 2 → Cell := twoBank p6575 ray6575
theorem signs6575 : ∀ j, Signs p6575 (bank6575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6576 := params 15
abbrev ray6576 := rays 15
def bank6576 : Fin 2 → Cell := twoBank p6576 ray6576
theorem signs6576 : ∀ j, Signs p6576 (bank6576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6577 := params 16
abbrev ray6577 := rays 16
def bank6577 : Fin 2 → Cell := twoBank p6577 ray6577
theorem signs6577 : ∀ j, Signs p6577 (bank6577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6578 := params 17
abbrev ray6578 := rays 17
def bank6578 : Fin 2 → Cell := twoBank p6578 ray6578
theorem signs6578 : ∀ j, Signs p6578 (bank6578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6579 := params 18
abbrev ray6579 := rays 18
def bank6579 : Fin 2 → Cell := twoBank p6579 ray6579
theorem signs6579 : ∀ j, Signs p6579 (bank6579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6580 := params 19
abbrev ray6580 := rays 19
def bank6580 : Fin 2 → Cell := twoBank p6580 ray6580
theorem signs6580 : ∀ j, Signs p6580 (bank6580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6581 := params 20
abbrev ray6581 := rays 20
def bank6581 : Fin 2 → Cell := twoBank p6581 ray6581
theorem signs6581 : ∀ j, Signs p6581 (bank6581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6582 := params 21
abbrev ray6582 := rays 21
def bank6582 : Fin 2 → Cell := twoBank p6582 ray6582
theorem signs6582 : ∀ j, Signs p6582 (bank6582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6583 := params 22
abbrev ray6583 := rays 22
def bank6583 : Fin 2 → Cell := twoBank p6583 ray6583
theorem signs6583 : ∀ j, Signs p6583 (bank6583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6584 := params 23
abbrev ray6584 := rays 23
def bank6584 : Fin 2 → Cell := twoBank p6584 ray6584
theorem signs6584 : ∀ j, Signs p6584 (bank6584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6585 := params 24
abbrev ray6585 := rays 24
def bank6585 : Fin 2 → Cell := twoBank p6585 ray6585
theorem signs6585 : ∀ j, Signs p6585 (bank6585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6586 := params 25
abbrev ray6586 := rays 25
def bank6586 : Fin 2 → Cell := twoBank p6586 ray6586
theorem signs6586 : ∀ j, Signs p6586 (bank6586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6587 := params 26
abbrev ray6587 := rays 26
def bank6587 : Fin 2 → Cell := twoBank p6587 ray6587
theorem signs6587 : ∀ j, Signs p6587 (bank6587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6588 := params 27
abbrev ray6588 := rays 27
def bank6588 : Fin 2 → Cell := twoBank p6588 ray6588
theorem signs6588 : ∀ j, Signs p6588 (bank6588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6589 := params 28
abbrev ray6589 := rays 28
def bank6589 : Fin 2 → Cell := twoBank p6589 ray6589
theorem signs6589 : ∀ j, Signs p6589 (bank6589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6590 := params 29
abbrev ray6590 := rays 29
def bank6590 : Fin 2 → Cell := twoBank p6590 ray6590
theorem signs6590 : ∀ j, Signs p6590 (bank6590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6591 := params 30
abbrev ray6591 := rays 30
def bank6591 : Fin 2 → Cell := twoBank p6591 ray6591
theorem signs6591 : ∀ j, Signs p6591 (bank6591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6592 := params 31
abbrev ray6592 := rays 31
def bank6592 : Fin 2 → Cell := twoBank p6592 ray6592
theorem signs6592 : ∀ j, Signs p6592 (bank6592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06561_06592
