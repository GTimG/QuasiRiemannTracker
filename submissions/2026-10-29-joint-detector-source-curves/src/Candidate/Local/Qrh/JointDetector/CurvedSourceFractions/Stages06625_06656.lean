/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06625_06656
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98587648777322,98587354416873,98587060033793,98586765628083,98586471199745,98586176748778,98585882275184,98585587778964,98585293260118,98584998718647,98584704154552,98584409567834,98584114958494,98583820326533,98583525671951,98583230994749,98582936294928,98582641572489,98582346827432,98582052059759,98581757269470,98581462456566,98581167621048,98580872762917,98580577882173,98580282978818,98579988052852,98579693104276,98579398133091,98579103139297,98578808122896,98578513083888,98578218022274]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6624+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6625 := params 0
abbrev ray6625 := rays 0
def bank6625 : Fin 2 → Cell := twoBank p6625 ray6625
theorem signs6625 : ∀ j, Signs p6625 (bank6625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6626 := params 1
abbrev ray6626 := rays 1
def bank6626 : Fin 2 → Cell := twoBank p6626 ray6626
theorem signs6626 : ∀ j, Signs p6626 (bank6626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6627 := params 2
abbrev ray6627 := rays 2
def bank6627 : Fin 2 → Cell := twoBank p6627 ray6627
theorem signs6627 : ∀ j, Signs p6627 (bank6627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6628 := params 3
abbrev ray6628 := rays 3
def bank6628 : Fin 2 → Cell := twoBank p6628 ray6628
theorem signs6628 : ∀ j, Signs p6628 (bank6628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6629 := params 4
abbrev ray6629 := rays 4
def bank6629 : Fin 2 → Cell := twoBank p6629 ray6629
theorem signs6629 : ∀ j, Signs p6629 (bank6629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6630 := params 5
abbrev ray6630 := rays 5
def bank6630 : Fin 2 → Cell := twoBank p6630 ray6630
theorem signs6630 : ∀ j, Signs p6630 (bank6630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6631 := params 6
abbrev ray6631 := rays 6
def bank6631 : Fin 2 → Cell := twoBank p6631 ray6631
theorem signs6631 : ∀ j, Signs p6631 (bank6631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6632 := params 7
abbrev ray6632 := rays 7
def bank6632 : Fin 2 → Cell := twoBank p6632 ray6632
theorem signs6632 : ∀ j, Signs p6632 (bank6632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6633 := params 8
abbrev ray6633 := rays 8
def bank6633 : Fin 2 → Cell := twoBank p6633 ray6633
theorem signs6633 : ∀ j, Signs p6633 (bank6633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6634 := params 9
abbrev ray6634 := rays 9
def bank6634 : Fin 2 → Cell := twoBank p6634 ray6634
theorem signs6634 : ∀ j, Signs p6634 (bank6634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6635 := params 10
abbrev ray6635 := rays 10
def bank6635 : Fin 2 → Cell := twoBank p6635 ray6635
theorem signs6635 : ∀ j, Signs p6635 (bank6635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6636 := params 11
abbrev ray6636 := rays 11
def bank6636 : Fin 2 → Cell := twoBank p6636 ray6636
theorem signs6636 : ∀ j, Signs p6636 (bank6636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6637 := params 12
abbrev ray6637 := rays 12
def bank6637 : Fin 2 → Cell := twoBank p6637 ray6637
theorem signs6637 : ∀ j, Signs p6637 (bank6637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6638 := params 13
abbrev ray6638 := rays 13
def bank6638 : Fin 2 → Cell := twoBank p6638 ray6638
theorem signs6638 : ∀ j, Signs p6638 (bank6638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6639 := params 14
abbrev ray6639 := rays 14
def bank6639 : Fin 2 → Cell := twoBank p6639 ray6639
theorem signs6639 : ∀ j, Signs p6639 (bank6639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6640 := params 15
abbrev ray6640 := rays 15
def bank6640 : Fin 2 → Cell := twoBank p6640 ray6640
theorem signs6640 : ∀ j, Signs p6640 (bank6640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6641 := params 16
abbrev ray6641 := rays 16
def bank6641 : Fin 2 → Cell := twoBank p6641 ray6641
theorem signs6641 : ∀ j, Signs p6641 (bank6641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6642 := params 17
abbrev ray6642 := rays 17
def bank6642 : Fin 2 → Cell := twoBank p6642 ray6642
theorem signs6642 : ∀ j, Signs p6642 (bank6642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6643 := params 18
abbrev ray6643 := rays 18
def bank6643 : Fin 2 → Cell := twoBank p6643 ray6643
theorem signs6643 : ∀ j, Signs p6643 (bank6643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6644 := params 19
abbrev ray6644 := rays 19
def bank6644 : Fin 2 → Cell := twoBank p6644 ray6644
theorem signs6644 : ∀ j, Signs p6644 (bank6644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6645 := params 20
abbrev ray6645 := rays 20
def bank6645 : Fin 2 → Cell := twoBank p6645 ray6645
theorem signs6645 : ∀ j, Signs p6645 (bank6645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6646 := params 21
abbrev ray6646 := rays 21
def bank6646 : Fin 2 → Cell := twoBank p6646 ray6646
theorem signs6646 : ∀ j, Signs p6646 (bank6646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6647 := params 22
abbrev ray6647 := rays 22
def bank6647 : Fin 2 → Cell := twoBank p6647 ray6647
theorem signs6647 : ∀ j, Signs p6647 (bank6647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6648 := params 23
abbrev ray6648 := rays 23
def bank6648 : Fin 2 → Cell := twoBank p6648 ray6648
theorem signs6648 : ∀ j, Signs p6648 (bank6648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6649 := params 24
abbrev ray6649 := rays 24
def bank6649 : Fin 2 → Cell := twoBank p6649 ray6649
theorem signs6649 : ∀ j, Signs p6649 (bank6649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6650 := params 25
abbrev ray6650 := rays 25
def bank6650 : Fin 2 → Cell := twoBank p6650 ray6650
theorem signs6650 : ∀ j, Signs p6650 (bank6650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6651 := params 26
abbrev ray6651 := rays 26
def bank6651 : Fin 2 → Cell := twoBank p6651 ray6651
theorem signs6651 : ∀ j, Signs p6651 (bank6651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6652 := params 27
abbrev ray6652 := rays 27
def bank6652 : Fin 2 → Cell := twoBank p6652 ray6652
theorem signs6652 : ∀ j, Signs p6652 (bank6652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6653 := params 28
abbrev ray6653 := rays 28
def bank6653 : Fin 2 → Cell := twoBank p6653 ray6653
theorem signs6653 : ∀ j, Signs p6653 (bank6653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6654 := params 29
abbrev ray6654 := rays 29
def bank6654 : Fin 2 → Cell := twoBank p6654 ray6654
theorem signs6654 : ∀ j, Signs p6654 (bank6654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6655 := params 30
abbrev ray6655 := rays 30
def bank6655 : Fin 2 → Cell := twoBank p6655 ray6655
theorem signs6655 : ∀ j, Signs p6655 (bank6655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6656 := params 31
abbrev ray6656 := rays 31
def bank6656 : Fin 2 → Cell := twoBank p6656 ray6656
theorem signs6656 : ∀ j, Signs p6656 (bank6656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06625_06656
