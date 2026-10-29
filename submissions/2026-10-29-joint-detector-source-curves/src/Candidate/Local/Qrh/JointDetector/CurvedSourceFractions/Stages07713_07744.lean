/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07713_07744
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98254173099790,98253854583578,98253536045575,98253217485783,98252898904202,98252580300832,98252261675675,98251943028731,98251624360001,98251305669485,98250986957185,98250668223101,98250349467234,98250030689584,98249711890152,98249393068939,98249074225946,98248755361173,98248436474622,98248117566292,98247798636185,98247479684301,98247160710641,98246841715206,98246522697997,98246203659014,98245884598258,98245565515729,98245246411429,98244927285358,98244608137516,98244288967905,98243969776525]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7712+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7713 := params 0
abbrev ray7713 := rays 0
def bank7713 : Fin 2 → Cell := twoBank p7713 ray7713
theorem signs7713 : ∀ j, Signs p7713 (bank7713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7714 := params 1
abbrev ray7714 := rays 1
def bank7714 : Fin 2 → Cell := twoBank p7714 ray7714
theorem signs7714 : ∀ j, Signs p7714 (bank7714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7715 := params 2
abbrev ray7715 := rays 2
def bank7715 : Fin 2 → Cell := twoBank p7715 ray7715
theorem signs7715 : ∀ j, Signs p7715 (bank7715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7716 := params 3
abbrev ray7716 := rays 3
def bank7716 : Fin 2 → Cell := twoBank p7716 ray7716
theorem signs7716 : ∀ j, Signs p7716 (bank7716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7717 := params 4
abbrev ray7717 := rays 4
def bank7717 : Fin 2 → Cell := twoBank p7717 ray7717
theorem signs7717 : ∀ j, Signs p7717 (bank7717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7718 := params 5
abbrev ray7718 := rays 5
def bank7718 : Fin 2 → Cell := twoBank p7718 ray7718
theorem signs7718 : ∀ j, Signs p7718 (bank7718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7719 := params 6
abbrev ray7719 := rays 6
def bank7719 : Fin 2 → Cell := twoBank p7719 ray7719
theorem signs7719 : ∀ j, Signs p7719 (bank7719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7720 := params 7
abbrev ray7720 := rays 7
def bank7720 : Fin 2 → Cell := twoBank p7720 ray7720
theorem signs7720 : ∀ j, Signs p7720 (bank7720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7721 := params 8
abbrev ray7721 := rays 8
def bank7721 : Fin 2 → Cell := twoBank p7721 ray7721
theorem signs7721 : ∀ j, Signs p7721 (bank7721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7722 := params 9
abbrev ray7722 := rays 9
def bank7722 : Fin 2 → Cell := twoBank p7722 ray7722
theorem signs7722 : ∀ j, Signs p7722 (bank7722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7723 := params 10
abbrev ray7723 := rays 10
def bank7723 : Fin 2 → Cell := twoBank p7723 ray7723
theorem signs7723 : ∀ j, Signs p7723 (bank7723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7724 := params 11
abbrev ray7724 := rays 11
def bank7724 : Fin 2 → Cell := twoBank p7724 ray7724
theorem signs7724 : ∀ j, Signs p7724 (bank7724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7725 := params 12
abbrev ray7725 := rays 12
def bank7725 : Fin 2 → Cell := twoBank p7725 ray7725
theorem signs7725 : ∀ j, Signs p7725 (bank7725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7726 := params 13
abbrev ray7726 := rays 13
def bank7726 : Fin 2 → Cell := twoBank p7726 ray7726
theorem signs7726 : ∀ j, Signs p7726 (bank7726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7727 := params 14
abbrev ray7727 := rays 14
def bank7727 : Fin 2 → Cell := twoBank p7727 ray7727
theorem signs7727 : ∀ j, Signs p7727 (bank7727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7728 := params 15
abbrev ray7728 := rays 15
def bank7728 : Fin 2 → Cell := twoBank p7728 ray7728
theorem signs7728 : ∀ j, Signs p7728 (bank7728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7729 := params 16
abbrev ray7729 := rays 16
def bank7729 : Fin 2 → Cell := twoBank p7729 ray7729
theorem signs7729 : ∀ j, Signs p7729 (bank7729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7730 := params 17
abbrev ray7730 := rays 17
def bank7730 : Fin 2 → Cell := twoBank p7730 ray7730
theorem signs7730 : ∀ j, Signs p7730 (bank7730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7731 := params 18
abbrev ray7731 := rays 18
def bank7731 : Fin 2 → Cell := twoBank p7731 ray7731
theorem signs7731 : ∀ j, Signs p7731 (bank7731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7732 := params 19
abbrev ray7732 := rays 19
def bank7732 : Fin 2 → Cell := twoBank p7732 ray7732
theorem signs7732 : ∀ j, Signs p7732 (bank7732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7733 := params 20
abbrev ray7733 := rays 20
def bank7733 : Fin 2 → Cell := twoBank p7733 ray7733
theorem signs7733 : ∀ j, Signs p7733 (bank7733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7734 := params 21
abbrev ray7734 := rays 21
def bank7734 : Fin 2 → Cell := twoBank p7734 ray7734
theorem signs7734 : ∀ j, Signs p7734 (bank7734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7735 := params 22
abbrev ray7735 := rays 22
def bank7735 : Fin 2 → Cell := twoBank p7735 ray7735
theorem signs7735 : ∀ j, Signs p7735 (bank7735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7736 := params 23
abbrev ray7736 := rays 23
def bank7736 : Fin 2 → Cell := twoBank p7736 ray7736
theorem signs7736 : ∀ j, Signs p7736 (bank7736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7737 := params 24
abbrev ray7737 := rays 24
def bank7737 : Fin 2 → Cell := twoBank p7737 ray7737
theorem signs7737 : ∀ j, Signs p7737 (bank7737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7738 := params 25
abbrev ray7738 := rays 25
def bank7738 : Fin 2 → Cell := twoBank p7738 ray7738
theorem signs7738 : ∀ j, Signs p7738 (bank7738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7739 := params 26
abbrev ray7739 := rays 26
def bank7739 : Fin 2 → Cell := twoBank p7739 ray7739
theorem signs7739 : ∀ j, Signs p7739 (bank7739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7740 := params 27
abbrev ray7740 := rays 27
def bank7740 : Fin 2 → Cell := twoBank p7740 ray7740
theorem signs7740 : ∀ j, Signs p7740 (bank7740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7741 := params 28
abbrev ray7741 := rays 28
def bank7741 : Fin 2 → Cell := twoBank p7741 ray7741
theorem signs7741 : ∀ j, Signs p7741 (bank7741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7742 := params 29
abbrev ray7742 := rays 29
def bank7742 : Fin 2 → Cell := twoBank p7742 ray7742
theorem signs7742 : ∀ j, Signs p7742 (bank7742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7743 := params 30
abbrev ray7743 := rays 30
def bank7743 : Fin 2 → Cell := twoBank p7743 ray7743
theorem signs7743 : ∀ j, Signs p7743 (bank7743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7744 := params 31
abbrev ray7744 := rays 31
def bank7744 : Fin 2 → Cell := twoBank p7744 ray7744
theorem signs7744 : ∀ j, Signs p7744 (bank7744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07713_07744
