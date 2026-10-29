/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14753_14784
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95511254206163,95510800840559,95510347458860,95509894061065,95509440647175,95508987217190,95508533771110,95508080308935,95507626830665,95507173336300,95506719825841,95506266299288,95505812756640,95505359197898,95504905623062,95504452032132,95503998425109,95503544801992,95503091162782,95502637507478,95502183836081,95501730148591,95501276445008,95500822725332,95500368989563,95499915237702,95499461469748,95499007685702,95498553885564,95498100069334,95497646237012,95497192388598,95496738524092]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14752+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14753 := params 0
abbrev ray14753 := rays 0
def bank14753 : Fin 1 → Cell := oneBank p14753 ray14753
theorem signs14753 : ∀ j, Signs p14753 (bank14753 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14754 := params 1
abbrev ray14754 := rays 1
def bank14754 : Fin 1 → Cell := oneBank p14754 ray14754
theorem signs14754 : ∀ j, Signs p14754 (bank14754 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14755 := params 2
abbrev ray14755 := rays 2
def bank14755 : Fin 1 → Cell := oneBank p14755 ray14755
theorem signs14755 : ∀ j, Signs p14755 (bank14755 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14756 := params 3
abbrev ray14756 := rays 3
def bank14756 : Fin 1 → Cell := oneBank p14756 ray14756
theorem signs14756 : ∀ j, Signs p14756 (bank14756 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14757 := params 4
abbrev ray14757 := rays 4
def bank14757 : Fin 1 → Cell := oneBank p14757 ray14757
theorem signs14757 : ∀ j, Signs p14757 (bank14757 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14758 := params 5
abbrev ray14758 := rays 5
def bank14758 : Fin 1 → Cell := oneBank p14758 ray14758
theorem signs14758 : ∀ j, Signs p14758 (bank14758 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14759 := params 6
abbrev ray14759 := rays 6
def bank14759 : Fin 1 → Cell := oneBank p14759 ray14759
theorem signs14759 : ∀ j, Signs p14759 (bank14759 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14760 := params 7
abbrev ray14760 := rays 7
def bank14760 : Fin 1 → Cell := oneBank p14760 ray14760
theorem signs14760 : ∀ j, Signs p14760 (bank14760 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14761 := params 8
abbrev ray14761 := rays 8
def bank14761 : Fin 1 → Cell := oneBank p14761 ray14761
theorem signs14761 : ∀ j, Signs p14761 (bank14761 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14762 := params 9
abbrev ray14762 := rays 9
def bank14762 : Fin 1 → Cell := oneBank p14762 ray14762
theorem signs14762 : ∀ j, Signs p14762 (bank14762 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14763 := params 10
abbrev ray14763 := rays 10
def bank14763 : Fin 1 → Cell := oneBank p14763 ray14763
theorem signs14763 : ∀ j, Signs p14763 (bank14763 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14764 := params 11
abbrev ray14764 := rays 11
def bank14764 : Fin 1 → Cell := oneBank p14764 ray14764
theorem signs14764 : ∀ j, Signs p14764 (bank14764 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14765 := params 12
abbrev ray14765 := rays 12
def bank14765 : Fin 1 → Cell := oneBank p14765 ray14765
theorem signs14765 : ∀ j, Signs p14765 (bank14765 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14766 := params 13
abbrev ray14766 := rays 13
def bank14766 : Fin 1 → Cell := oneBank p14766 ray14766
theorem signs14766 : ∀ j, Signs p14766 (bank14766 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14767 := params 14
abbrev ray14767 := rays 14
def bank14767 : Fin 1 → Cell := oneBank p14767 ray14767
theorem signs14767 : ∀ j, Signs p14767 (bank14767 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14768 := params 15
abbrev ray14768 := rays 15
def bank14768 : Fin 1 → Cell := oneBank p14768 ray14768
theorem signs14768 : ∀ j, Signs p14768 (bank14768 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14769 := params 16
abbrev ray14769 := rays 16
def bank14769 : Fin 1 → Cell := oneBank p14769 ray14769
theorem signs14769 : ∀ j, Signs p14769 (bank14769 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14770 := params 17
abbrev ray14770 := rays 17
def bank14770 : Fin 1 → Cell := oneBank p14770 ray14770
theorem signs14770 : ∀ j, Signs p14770 (bank14770 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14771 := params 18
abbrev ray14771 := rays 18
def bank14771 : Fin 1 → Cell := oneBank p14771 ray14771
theorem signs14771 : ∀ j, Signs p14771 (bank14771 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14772 := params 19
abbrev ray14772 := rays 19
def bank14772 : Fin 1 → Cell := oneBank p14772 ray14772
theorem signs14772 : ∀ j, Signs p14772 (bank14772 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14773 := params 20
abbrev ray14773 := rays 20
def bank14773 : Fin 1 → Cell := oneBank p14773 ray14773
theorem signs14773 : ∀ j, Signs p14773 (bank14773 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14774 := params 21
abbrev ray14774 := rays 21
def bank14774 : Fin 1 → Cell := oneBank p14774 ray14774
theorem signs14774 : ∀ j, Signs p14774 (bank14774 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14775 := params 22
abbrev ray14775 := rays 22
def bank14775 : Fin 1 → Cell := oneBank p14775 ray14775
theorem signs14775 : ∀ j, Signs p14775 (bank14775 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14776 := params 23
abbrev ray14776 := rays 23
def bank14776 : Fin 1 → Cell := oneBank p14776 ray14776
theorem signs14776 : ∀ j, Signs p14776 (bank14776 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14777 := params 24
abbrev ray14777 := rays 24
def bank14777 : Fin 1 → Cell := oneBank p14777 ray14777
theorem signs14777 : ∀ j, Signs p14777 (bank14777 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14778 := params 25
abbrev ray14778 := rays 25
def bank14778 : Fin 1 → Cell := oneBank p14778 ray14778
theorem signs14778 : ∀ j, Signs p14778 (bank14778 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14779 := params 26
abbrev ray14779 := rays 26
def bank14779 : Fin 1 → Cell := oneBank p14779 ray14779
theorem signs14779 : ∀ j, Signs p14779 (bank14779 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14780 := params 27
abbrev ray14780 := rays 27
def bank14780 : Fin 1 → Cell := oneBank p14780 ray14780
theorem signs14780 : ∀ j, Signs p14780 (bank14780 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14781 := params 28
abbrev ray14781 := rays 28
def bank14781 : Fin 1 → Cell := oneBank p14781 ray14781
theorem signs14781 : ∀ j, Signs p14781 (bank14781 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14782 := params 29
abbrev ray14782 := rays 29
def bank14782 : Fin 1 → Cell := oneBank p14782 ray14782
theorem signs14782 : ∀ j, Signs p14782 (bank14782 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14783 := params 30
abbrev ray14783 := rays 30
def bank14783 : Fin 1 → Cell := oneBank p14783 ray14783
theorem signs14783 : ∀ j, Signs p14783 (bank14783 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14784 := params 31
abbrev ray14784 := rays 31
def bank14784 : Fin 1 → Cell := oneBank p14784 ray14784
theorem signs14784 : ∀ j, Signs p14784 (bank14784 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14753_14784
