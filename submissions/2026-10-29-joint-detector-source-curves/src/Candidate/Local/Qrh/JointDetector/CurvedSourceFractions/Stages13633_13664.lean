/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13633_13664
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96008884324788,96008449084730,96008013828385,96007578555754,96007143266836,96006707961632,96006272640142,96005837302366,96005401948304,96004966577957,96004531191324,96004095788406,96003660369203,96003224933716,96002789481944,96002354013888,96001918529548,96001483028924,96001047512017,96000611978826,96000176429352,95999740863595,95999305281556,95998869683234,95998434068630,95997998437744,95997562790576,95997127127126,95996691447395,95996255751383,95995820039090,95995384310516,95994948565661]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13632+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13633 := params 0
abbrev ray13633 := rays 0
def bank13633 : Fin 1 → Cell := oneBank p13633 ray13633
theorem signs13633 : ∀ j, Signs p13633 (bank13633 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13634 := params 1
abbrev ray13634 := rays 1
def bank13634 : Fin 1 → Cell := oneBank p13634 ray13634
theorem signs13634 : ∀ j, Signs p13634 (bank13634 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13635 := params 2
abbrev ray13635 := rays 2
def bank13635 : Fin 1 → Cell := oneBank p13635 ray13635
theorem signs13635 : ∀ j, Signs p13635 (bank13635 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13636 := params 3
abbrev ray13636 := rays 3
def bank13636 : Fin 1 → Cell := oneBank p13636 ray13636
theorem signs13636 : ∀ j, Signs p13636 (bank13636 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13637 := params 4
abbrev ray13637 := rays 4
def bank13637 : Fin 1 → Cell := oneBank p13637 ray13637
theorem signs13637 : ∀ j, Signs p13637 (bank13637 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13638 := params 5
abbrev ray13638 := rays 5
def bank13638 : Fin 1 → Cell := oneBank p13638 ray13638
theorem signs13638 : ∀ j, Signs p13638 (bank13638 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13639 := params 6
abbrev ray13639 := rays 6
def bank13639 : Fin 1 → Cell := oneBank p13639 ray13639
theorem signs13639 : ∀ j, Signs p13639 (bank13639 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13640 := params 7
abbrev ray13640 := rays 7
def bank13640 : Fin 1 → Cell := oneBank p13640 ray13640
theorem signs13640 : ∀ j, Signs p13640 (bank13640 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13641 := params 8
abbrev ray13641 := rays 8
def bank13641 : Fin 1 → Cell := oneBank p13641 ray13641
theorem signs13641 : ∀ j, Signs p13641 (bank13641 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13642 := params 9
abbrev ray13642 := rays 9
def bank13642 : Fin 1 → Cell := oneBank p13642 ray13642
theorem signs13642 : ∀ j, Signs p13642 (bank13642 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13643 := params 10
abbrev ray13643 := rays 10
def bank13643 : Fin 1 → Cell := oneBank p13643 ray13643
theorem signs13643 : ∀ j, Signs p13643 (bank13643 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13644 := params 11
abbrev ray13644 := rays 11
def bank13644 : Fin 1 → Cell := oneBank p13644 ray13644
theorem signs13644 : ∀ j, Signs p13644 (bank13644 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13645 := params 12
abbrev ray13645 := rays 12
def bank13645 : Fin 1 → Cell := oneBank p13645 ray13645
theorem signs13645 : ∀ j, Signs p13645 (bank13645 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13646 := params 13
abbrev ray13646 := rays 13
def bank13646 : Fin 1 → Cell := oneBank p13646 ray13646
theorem signs13646 : ∀ j, Signs p13646 (bank13646 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13647 := params 14
abbrev ray13647 := rays 14
def bank13647 : Fin 1 → Cell := oneBank p13647 ray13647
theorem signs13647 : ∀ j, Signs p13647 (bank13647 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13648 := params 15
abbrev ray13648 := rays 15
def bank13648 : Fin 1 → Cell := oneBank p13648 ray13648
theorem signs13648 : ∀ j, Signs p13648 (bank13648 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13649 := params 16
abbrev ray13649 := rays 16
def bank13649 : Fin 1 → Cell := oneBank p13649 ray13649
theorem signs13649 : ∀ j, Signs p13649 (bank13649 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13650 := params 17
abbrev ray13650 := rays 17
def bank13650 : Fin 1 → Cell := oneBank p13650 ray13650
theorem signs13650 : ∀ j, Signs p13650 (bank13650 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13651 := params 18
abbrev ray13651 := rays 18
def bank13651 : Fin 1 → Cell := oneBank p13651 ray13651
theorem signs13651 : ∀ j, Signs p13651 (bank13651 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13652 := params 19
abbrev ray13652 := rays 19
def bank13652 : Fin 1 → Cell := oneBank p13652 ray13652
theorem signs13652 : ∀ j, Signs p13652 (bank13652 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13653 := params 20
abbrev ray13653 := rays 20
def bank13653 : Fin 1 → Cell := oneBank p13653 ray13653
theorem signs13653 : ∀ j, Signs p13653 (bank13653 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13654 := params 21
abbrev ray13654 := rays 21
def bank13654 : Fin 1 → Cell := oneBank p13654 ray13654
theorem signs13654 : ∀ j, Signs p13654 (bank13654 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13655 := params 22
abbrev ray13655 := rays 22
def bank13655 : Fin 1 → Cell := oneBank p13655 ray13655
theorem signs13655 : ∀ j, Signs p13655 (bank13655 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13656 := params 23
abbrev ray13656 := rays 23
def bank13656 : Fin 1 → Cell := oneBank p13656 ray13656
theorem signs13656 : ∀ j, Signs p13656 (bank13656 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13657 := params 24
abbrev ray13657 := rays 24
def bank13657 : Fin 1 → Cell := oneBank p13657 ray13657
theorem signs13657 : ∀ j, Signs p13657 (bank13657 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13658 := params 25
abbrev ray13658 := rays 25
def bank13658 : Fin 1 → Cell := oneBank p13658 ray13658
theorem signs13658 : ∀ j, Signs p13658 (bank13658 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13659 := params 26
abbrev ray13659 := rays 26
def bank13659 : Fin 1 → Cell := oneBank p13659 ray13659
theorem signs13659 : ∀ j, Signs p13659 (bank13659 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13660 := params 27
abbrev ray13660 := rays 27
def bank13660 : Fin 1 → Cell := oneBank p13660 ray13660
theorem signs13660 : ∀ j, Signs p13660 (bank13660 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13661 := params 28
abbrev ray13661 := rays 28
def bank13661 : Fin 1 → Cell := oneBank p13661 ray13661
theorem signs13661 : ∀ j, Signs p13661 (bank13661 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13662 := params 29
abbrev ray13662 := rays 29
def bank13662 : Fin 1 → Cell := oneBank p13662 ray13662
theorem signs13662 : ∀ j, Signs p13662 (bank13662 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13663 := params 30
abbrev ray13663 := rays 30
def bank13663 : Fin 1 → Cell := oneBank p13663 ray13663
theorem signs13663 : ∀ j, Signs p13663 (bank13663 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13664 := params 31
abbrev ray13664 := rays 31
def bank13664 : Fin 1 → Cell := oneBank p13664 ray13664
theorem signs13664 : ∀ j, Signs p13664 (bank13664 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13633_13664
