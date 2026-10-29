/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06593_06624
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98597056357859,98596762722021,98596469063526,98596175382375,98595881678569,98595587952109,98595294202995,98595000431228,98594706636809,98594412819739,98594118980019,98593825117650,98593531232632,98593237324966,98592943394653,98592649441694,98592355466090,98592061467841,98591767446948,98591473403412,98591179337234,98590885248415,98590591136956,98590297002857,98590002846119,98589708666744,98589414464731,98589120240082,98588825992798,98588531722879,98588237430326,98587943115140,98587648777322]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6592+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6593 := params 0
abbrev ray6593 := rays 0
def bank6593 : Fin 2 → Cell := twoBank p6593 ray6593
theorem signs6593 : ∀ j, Signs p6593 (bank6593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6594 := params 1
abbrev ray6594 := rays 1
def bank6594 : Fin 2 → Cell := twoBank p6594 ray6594
theorem signs6594 : ∀ j, Signs p6594 (bank6594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6595 := params 2
abbrev ray6595 := rays 2
def bank6595 : Fin 2 → Cell := twoBank p6595 ray6595
theorem signs6595 : ∀ j, Signs p6595 (bank6595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6596 := params 3
abbrev ray6596 := rays 3
def bank6596 : Fin 2 → Cell := twoBank p6596 ray6596
theorem signs6596 : ∀ j, Signs p6596 (bank6596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6597 := params 4
abbrev ray6597 := rays 4
def bank6597 : Fin 2 → Cell := twoBank p6597 ray6597
theorem signs6597 : ∀ j, Signs p6597 (bank6597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6598 := params 5
abbrev ray6598 := rays 5
def bank6598 : Fin 2 → Cell := twoBank p6598 ray6598
theorem signs6598 : ∀ j, Signs p6598 (bank6598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6599 := params 6
abbrev ray6599 := rays 6
def bank6599 : Fin 2 → Cell := twoBank p6599 ray6599
theorem signs6599 : ∀ j, Signs p6599 (bank6599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6600 := params 7
abbrev ray6600 := rays 7
def bank6600 : Fin 2 → Cell := twoBank p6600 ray6600
theorem signs6600 : ∀ j, Signs p6600 (bank6600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6601 := params 8
abbrev ray6601 := rays 8
def bank6601 : Fin 2 → Cell := twoBank p6601 ray6601
theorem signs6601 : ∀ j, Signs p6601 (bank6601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6602 := params 9
abbrev ray6602 := rays 9
def bank6602 : Fin 2 → Cell := twoBank p6602 ray6602
theorem signs6602 : ∀ j, Signs p6602 (bank6602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6603 := params 10
abbrev ray6603 := rays 10
def bank6603 : Fin 2 → Cell := twoBank p6603 ray6603
theorem signs6603 : ∀ j, Signs p6603 (bank6603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6604 := params 11
abbrev ray6604 := rays 11
def bank6604 : Fin 2 → Cell := twoBank p6604 ray6604
theorem signs6604 : ∀ j, Signs p6604 (bank6604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6605 := params 12
abbrev ray6605 := rays 12
def bank6605 : Fin 2 → Cell := twoBank p6605 ray6605
theorem signs6605 : ∀ j, Signs p6605 (bank6605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6606 := params 13
abbrev ray6606 := rays 13
def bank6606 : Fin 2 → Cell := twoBank p6606 ray6606
theorem signs6606 : ∀ j, Signs p6606 (bank6606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6607 := params 14
abbrev ray6607 := rays 14
def bank6607 : Fin 2 → Cell := twoBank p6607 ray6607
theorem signs6607 : ∀ j, Signs p6607 (bank6607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6608 := params 15
abbrev ray6608 := rays 15
def bank6608 : Fin 2 → Cell := twoBank p6608 ray6608
theorem signs6608 : ∀ j, Signs p6608 (bank6608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6609 := params 16
abbrev ray6609 := rays 16
def bank6609 : Fin 2 → Cell := twoBank p6609 ray6609
theorem signs6609 : ∀ j, Signs p6609 (bank6609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6610 := params 17
abbrev ray6610 := rays 17
def bank6610 : Fin 2 → Cell := twoBank p6610 ray6610
theorem signs6610 : ∀ j, Signs p6610 (bank6610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6611 := params 18
abbrev ray6611 := rays 18
def bank6611 : Fin 2 → Cell := twoBank p6611 ray6611
theorem signs6611 : ∀ j, Signs p6611 (bank6611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6612 := params 19
abbrev ray6612 := rays 19
def bank6612 : Fin 2 → Cell := twoBank p6612 ray6612
theorem signs6612 : ∀ j, Signs p6612 (bank6612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6613 := params 20
abbrev ray6613 := rays 20
def bank6613 : Fin 2 → Cell := twoBank p6613 ray6613
theorem signs6613 : ∀ j, Signs p6613 (bank6613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6614 := params 21
abbrev ray6614 := rays 21
def bank6614 : Fin 2 → Cell := twoBank p6614 ray6614
theorem signs6614 : ∀ j, Signs p6614 (bank6614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6615 := params 22
abbrev ray6615 := rays 22
def bank6615 : Fin 2 → Cell := twoBank p6615 ray6615
theorem signs6615 : ∀ j, Signs p6615 (bank6615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6616 := params 23
abbrev ray6616 := rays 23
def bank6616 : Fin 2 → Cell := twoBank p6616 ray6616
theorem signs6616 : ∀ j, Signs p6616 (bank6616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6617 := params 24
abbrev ray6617 := rays 24
def bank6617 : Fin 2 → Cell := twoBank p6617 ray6617
theorem signs6617 : ∀ j, Signs p6617 (bank6617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6618 := params 25
abbrev ray6618 := rays 25
def bank6618 : Fin 2 → Cell := twoBank p6618 ray6618
theorem signs6618 : ∀ j, Signs p6618 (bank6618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6619 := params 26
abbrev ray6619 := rays 26
def bank6619 : Fin 2 → Cell := twoBank p6619 ray6619
theorem signs6619 : ∀ j, Signs p6619 (bank6619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6620 := params 27
abbrev ray6620 := rays 27
def bank6620 : Fin 2 → Cell := twoBank p6620 ray6620
theorem signs6620 : ∀ j, Signs p6620 (bank6620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6621 := params 28
abbrev ray6621 := rays 28
def bank6621 : Fin 2 → Cell := twoBank p6621 ray6621
theorem signs6621 : ∀ j, Signs p6621 (bank6621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6622 := params 29
abbrev ray6622 := rays 29
def bank6622 : Fin 2 → Cell := twoBank p6622 ray6622
theorem signs6622 : ∀ j, Signs p6622 (bank6622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6623 := params 30
abbrev ray6623 := rays 30
def bank6623 : Fin 2 → Cell := twoBank p6623 ray6623
theorem signs6623 : ∀ j, Signs p6623 (bank6623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6624 := params 31
abbrev ray6624 := rays 31
def bank6624 : Fin 2 → Cell := twoBank p6624 ray6624
theorem signs6624 : ∀ j, Signs p6624 (bank6624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06593_06624
