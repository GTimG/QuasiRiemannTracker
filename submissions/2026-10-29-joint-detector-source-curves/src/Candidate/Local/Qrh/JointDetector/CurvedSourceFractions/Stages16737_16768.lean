/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16737_16768
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94580234787888,94579749646181,94579264488488,94578779314809,94578294125144,94577808919493,94577323697856,94576838460233,94576353206624,94575867937029,94575382651448,94574897349881,94574412032328,94573926698789,94573441349264,94572955983753,94572470602256,94571985204772,94571499791302,94571014361846,94570528916404,94570043454975,94569557977560,94569072484159,94568586974772,94568101449398,94567615908038,94567130350691,94566644777358,94566159188039,94565673582733,94565187961441,94564702324162]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16736+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16737 := params 0
abbrev ray16737 := rays 0
def bank16737 : Fin 1 → Cell := oneBank p16737 ray16737
theorem signs16737 : ∀ j, Signs p16737 (bank16737 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16738 := params 1
abbrev ray16738 := rays 1
def bank16738 : Fin 1 → Cell := oneBank p16738 ray16738
theorem signs16738 : ∀ j, Signs p16738 (bank16738 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16739 := params 2
abbrev ray16739 := rays 2
def bank16739 : Fin 1 → Cell := oneBank p16739 ray16739
theorem signs16739 : ∀ j, Signs p16739 (bank16739 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16740 := params 3
abbrev ray16740 := rays 3
def bank16740 : Fin 1 → Cell := oneBank p16740 ray16740
theorem signs16740 : ∀ j, Signs p16740 (bank16740 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16741 := params 4
abbrev ray16741 := rays 4
def bank16741 : Fin 1 → Cell := oneBank p16741 ray16741
theorem signs16741 : ∀ j, Signs p16741 (bank16741 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16742 := params 5
abbrev ray16742 := rays 5
def bank16742 : Fin 1 → Cell := oneBank p16742 ray16742
theorem signs16742 : ∀ j, Signs p16742 (bank16742 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16743 := params 6
abbrev ray16743 := rays 6
def bank16743 : Fin 1 → Cell := oneBank p16743 ray16743
theorem signs16743 : ∀ j, Signs p16743 (bank16743 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16744 := params 7
abbrev ray16744 := rays 7
def bank16744 : Fin 1 → Cell := oneBank p16744 ray16744
theorem signs16744 : ∀ j, Signs p16744 (bank16744 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16745 := params 8
abbrev ray16745 := rays 8
def bank16745 : Fin 1 → Cell := oneBank p16745 ray16745
theorem signs16745 : ∀ j, Signs p16745 (bank16745 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16746 := params 9
abbrev ray16746 := rays 9
def bank16746 : Fin 1 → Cell := oneBank p16746 ray16746
theorem signs16746 : ∀ j, Signs p16746 (bank16746 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16747 := params 10
abbrev ray16747 := rays 10
def bank16747 : Fin 1 → Cell := oneBank p16747 ray16747
theorem signs16747 : ∀ j, Signs p16747 (bank16747 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16748 := params 11
abbrev ray16748 := rays 11
def bank16748 : Fin 1 → Cell := oneBank p16748 ray16748
theorem signs16748 : ∀ j, Signs p16748 (bank16748 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16749 := params 12
abbrev ray16749 := rays 12
def bank16749 : Fin 1 → Cell := oneBank p16749 ray16749
theorem signs16749 : ∀ j, Signs p16749 (bank16749 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16750 := params 13
abbrev ray16750 := rays 13
def bank16750 : Fin 1 → Cell := oneBank p16750 ray16750
theorem signs16750 : ∀ j, Signs p16750 (bank16750 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16751 := params 14
abbrev ray16751 := rays 14
def bank16751 : Fin 1 → Cell := oneBank p16751 ray16751
theorem signs16751 : ∀ j, Signs p16751 (bank16751 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16752 := params 15
abbrev ray16752 := rays 15
def bank16752 : Fin 1 → Cell := oneBank p16752 ray16752
theorem signs16752 : ∀ j, Signs p16752 (bank16752 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16753 := params 16
abbrev ray16753 := rays 16
def bank16753 : Fin 1 → Cell := oneBank p16753 ray16753
theorem signs16753 : ∀ j, Signs p16753 (bank16753 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16754 := params 17
abbrev ray16754 := rays 17
def bank16754 : Fin 1 → Cell := oneBank p16754 ray16754
theorem signs16754 : ∀ j, Signs p16754 (bank16754 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16755 := params 18
abbrev ray16755 := rays 18
def bank16755 : Fin 1 → Cell := oneBank p16755 ray16755
theorem signs16755 : ∀ j, Signs p16755 (bank16755 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16756 := params 19
abbrev ray16756 := rays 19
def bank16756 : Fin 1 → Cell := oneBank p16756 ray16756
theorem signs16756 : ∀ j, Signs p16756 (bank16756 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16757 := params 20
abbrev ray16757 := rays 20
def bank16757 : Fin 1 → Cell := oneBank p16757 ray16757
theorem signs16757 : ∀ j, Signs p16757 (bank16757 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16758 := params 21
abbrev ray16758 := rays 21
def bank16758 : Fin 1 → Cell := oneBank p16758 ray16758
theorem signs16758 : ∀ j, Signs p16758 (bank16758 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16759 := params 22
abbrev ray16759 := rays 22
def bank16759 : Fin 1 → Cell := oneBank p16759 ray16759
theorem signs16759 : ∀ j, Signs p16759 (bank16759 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16760 := params 23
abbrev ray16760 := rays 23
def bank16760 : Fin 1 → Cell := oneBank p16760 ray16760
theorem signs16760 : ∀ j, Signs p16760 (bank16760 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16761 := params 24
abbrev ray16761 := rays 24
def bank16761 : Fin 1 → Cell := oneBank p16761 ray16761
theorem signs16761 : ∀ j, Signs p16761 (bank16761 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16762 := params 25
abbrev ray16762 := rays 25
def bank16762 : Fin 1 → Cell := oneBank p16762 ray16762
theorem signs16762 : ∀ j, Signs p16762 (bank16762 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16763 := params 26
abbrev ray16763 := rays 26
def bank16763 : Fin 1 → Cell := oneBank p16763 ray16763
theorem signs16763 : ∀ j, Signs p16763 (bank16763 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16764 := params 27
abbrev ray16764 := rays 27
def bank16764 : Fin 1 → Cell := oneBank p16764 ray16764
theorem signs16764 : ∀ j, Signs p16764 (bank16764 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16765 := params 28
abbrev ray16765 := rays 28
def bank16765 : Fin 1 → Cell := oneBank p16765 ray16765
theorem signs16765 : ∀ j, Signs p16765 (bank16765 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16766 := params 29
abbrev ray16766 := rays 29
def bank16766 : Fin 1 → Cell := oneBank p16766 ray16766
theorem signs16766 : ∀ j, Signs p16766 (bank16766 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16767 := params 30
abbrev ray16767 := rays 30
def bank16767 : Fin 1 → Cell := oneBank p16767 ray16767
theorem signs16767 : ∀ j, Signs p16767 (bank16767 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16768 := params 31
abbrev ray16768 := rays 31
def bank16768 : Fin 1 → Cell := oneBank p16768 ray16768
theorem signs16768 : ∀ j, Signs p16768 (bank16768 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16737_16768
