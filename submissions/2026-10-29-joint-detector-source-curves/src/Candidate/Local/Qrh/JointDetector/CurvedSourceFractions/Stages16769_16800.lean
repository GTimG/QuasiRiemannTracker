/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16769_16800
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94564702324162,94564216670897,94563731001645,94563245316406,94562759615181,94562273897969,94561788164770,94561302415585,94560816650413,94560330869254,94559845072109,94559359258977,94558873429858,94558387584752,94557901723660,94557415846581,94556929953515,94556444044462,94555958119422,94555472178395,94554986221381,94554500248380,94554014259392,94553528254417,94553042233455,94552556196506,94552070143570,94551584074647,94551097989736,94550611888838,94550125771953,94549639639081,94549153490222]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16768+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16769 := params 0
abbrev ray16769 := rays 0
def bank16769 : Fin 1 → Cell := oneBank p16769 ray16769
theorem signs16769 : ∀ j, Signs p16769 (bank16769 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16770 := params 1
abbrev ray16770 := rays 1
def bank16770 : Fin 1 → Cell := oneBank p16770 ray16770
theorem signs16770 : ∀ j, Signs p16770 (bank16770 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16771 := params 2
abbrev ray16771 := rays 2
def bank16771 : Fin 1 → Cell := oneBank p16771 ray16771
theorem signs16771 : ∀ j, Signs p16771 (bank16771 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16772 := params 3
abbrev ray16772 := rays 3
def bank16772 : Fin 1 → Cell := oneBank p16772 ray16772
theorem signs16772 : ∀ j, Signs p16772 (bank16772 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16773 := params 4
abbrev ray16773 := rays 4
def bank16773 : Fin 1 → Cell := oneBank p16773 ray16773
theorem signs16773 : ∀ j, Signs p16773 (bank16773 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16774 := params 5
abbrev ray16774 := rays 5
def bank16774 : Fin 1 → Cell := oneBank p16774 ray16774
theorem signs16774 : ∀ j, Signs p16774 (bank16774 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16775 := params 6
abbrev ray16775 := rays 6
def bank16775 : Fin 1 → Cell := oneBank p16775 ray16775
theorem signs16775 : ∀ j, Signs p16775 (bank16775 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16776 := params 7
abbrev ray16776 := rays 7
def bank16776 : Fin 1 → Cell := oneBank p16776 ray16776
theorem signs16776 : ∀ j, Signs p16776 (bank16776 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16777 := params 8
abbrev ray16777 := rays 8
def bank16777 : Fin 1 → Cell := oneBank p16777 ray16777
theorem signs16777 : ∀ j, Signs p16777 (bank16777 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16778 := params 9
abbrev ray16778 := rays 9
def bank16778 : Fin 1 → Cell := oneBank p16778 ray16778
theorem signs16778 : ∀ j, Signs p16778 (bank16778 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16779 := params 10
abbrev ray16779 := rays 10
def bank16779 : Fin 1 → Cell := oneBank p16779 ray16779
theorem signs16779 : ∀ j, Signs p16779 (bank16779 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16780 := params 11
abbrev ray16780 := rays 11
def bank16780 : Fin 1 → Cell := oneBank p16780 ray16780
theorem signs16780 : ∀ j, Signs p16780 (bank16780 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16781 := params 12
abbrev ray16781 := rays 12
def bank16781 : Fin 1 → Cell := oneBank p16781 ray16781
theorem signs16781 : ∀ j, Signs p16781 (bank16781 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16782 := params 13
abbrev ray16782 := rays 13
def bank16782 : Fin 1 → Cell := oneBank p16782 ray16782
theorem signs16782 : ∀ j, Signs p16782 (bank16782 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16783 := params 14
abbrev ray16783 := rays 14
def bank16783 : Fin 1 → Cell := oneBank p16783 ray16783
theorem signs16783 : ∀ j, Signs p16783 (bank16783 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16784 := params 15
abbrev ray16784 := rays 15
def bank16784 : Fin 1 → Cell := oneBank p16784 ray16784
theorem signs16784 : ∀ j, Signs p16784 (bank16784 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16785 := params 16
abbrev ray16785 := rays 16
def bank16785 : Fin 1 → Cell := oneBank p16785 ray16785
theorem signs16785 : ∀ j, Signs p16785 (bank16785 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16786 := params 17
abbrev ray16786 := rays 17
def bank16786 : Fin 1 → Cell := oneBank p16786 ray16786
theorem signs16786 : ∀ j, Signs p16786 (bank16786 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16787 := params 18
abbrev ray16787 := rays 18
def bank16787 : Fin 1 → Cell := oneBank p16787 ray16787
theorem signs16787 : ∀ j, Signs p16787 (bank16787 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16788 := params 19
abbrev ray16788 := rays 19
def bank16788 : Fin 1 → Cell := oneBank p16788 ray16788
theorem signs16788 : ∀ j, Signs p16788 (bank16788 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16789 := params 20
abbrev ray16789 := rays 20
def bank16789 : Fin 1 → Cell := oneBank p16789 ray16789
theorem signs16789 : ∀ j, Signs p16789 (bank16789 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16790 := params 21
abbrev ray16790 := rays 21
def bank16790 : Fin 1 → Cell := oneBank p16790 ray16790
theorem signs16790 : ∀ j, Signs p16790 (bank16790 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16791 := params 22
abbrev ray16791 := rays 22
def bank16791 : Fin 1 → Cell := oneBank p16791 ray16791
theorem signs16791 : ∀ j, Signs p16791 (bank16791 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16792 := params 23
abbrev ray16792 := rays 23
def bank16792 : Fin 1 → Cell := oneBank p16792 ray16792
theorem signs16792 : ∀ j, Signs p16792 (bank16792 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16793 := params 24
abbrev ray16793 := rays 24
def bank16793 : Fin 1 → Cell := oneBank p16793 ray16793
theorem signs16793 : ∀ j, Signs p16793 (bank16793 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16794 := params 25
abbrev ray16794 := rays 25
def bank16794 : Fin 1 → Cell := oneBank p16794 ray16794
theorem signs16794 : ∀ j, Signs p16794 (bank16794 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16795 := params 26
abbrev ray16795 := rays 26
def bank16795 : Fin 1 → Cell := oneBank p16795 ray16795
theorem signs16795 : ∀ j, Signs p16795 (bank16795 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16796 := params 27
abbrev ray16796 := rays 27
def bank16796 : Fin 1 → Cell := oneBank p16796 ray16796
theorem signs16796 : ∀ j, Signs p16796 (bank16796 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16797 := params 28
abbrev ray16797 := rays 28
def bank16797 : Fin 1 → Cell := oneBank p16797 ray16797
theorem signs16797 : ∀ j, Signs p16797 (bank16797 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16798 := params 29
abbrev ray16798 := rays 29
def bank16798 : Fin 1 → Cell := oneBank p16798 ray16798
theorem signs16798 : ∀ j, Signs p16798 (bank16798 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16799 := params 30
abbrev ray16799 := rays 30
def bank16799 : Fin 1 → Cell := oneBank p16799 ray16799
theorem signs16799 : ∀ j, Signs p16799 (bank16799 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16800 := params 31
abbrev ray16800 := rays 31
def bank16800 : Fin 1 → Cell := oneBank p16800 ray16800
theorem signs16800 : ∀ j, Signs p16800 (bank16800 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16769_16800
