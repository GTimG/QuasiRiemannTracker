/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06817_06848
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98530717567208,98530418876662,98530120163641,98529821428147,98529522670180,98529223889741,98528925086831,98528626261450,98528327413600,98528028543281,98527729650494,98527430735240,98527131797519,98526832837333,98526533854682,98526234849567,98525935821989,98525636771948,98525337699446,98525038604483,98524739487060,98524440347178,98524141184838,98523842000040,98523542792785,98523243563074,98522944310908,98522645036288,98522345739214,98522046419688,98521747077710,98521447713281,98521148326401]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6816+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6817 := params 0
abbrev ray6817 := rays 0
def bank6817 : Fin 2 → Cell := twoBank p6817 ray6817
theorem signs6817 : ∀ j, Signs p6817 (bank6817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6818 := params 1
abbrev ray6818 := rays 1
def bank6818 : Fin 2 → Cell := twoBank p6818 ray6818
theorem signs6818 : ∀ j, Signs p6818 (bank6818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6819 := params 2
abbrev ray6819 := rays 2
def bank6819 : Fin 2 → Cell := twoBank p6819 ray6819
theorem signs6819 : ∀ j, Signs p6819 (bank6819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6820 := params 3
abbrev ray6820 := rays 3
def bank6820 : Fin 2 → Cell := twoBank p6820 ray6820
theorem signs6820 : ∀ j, Signs p6820 (bank6820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6821 := params 4
abbrev ray6821 := rays 4
def bank6821 : Fin 2 → Cell := twoBank p6821 ray6821
theorem signs6821 : ∀ j, Signs p6821 (bank6821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6822 := params 5
abbrev ray6822 := rays 5
def bank6822 : Fin 2 → Cell := twoBank p6822 ray6822
theorem signs6822 : ∀ j, Signs p6822 (bank6822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6823 := params 6
abbrev ray6823 := rays 6
def bank6823 : Fin 2 → Cell := twoBank p6823 ray6823
theorem signs6823 : ∀ j, Signs p6823 (bank6823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6824 := params 7
abbrev ray6824 := rays 7
def bank6824 : Fin 2 → Cell := twoBank p6824 ray6824
theorem signs6824 : ∀ j, Signs p6824 (bank6824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6825 := params 8
abbrev ray6825 := rays 8
def bank6825 : Fin 2 → Cell := twoBank p6825 ray6825
theorem signs6825 : ∀ j, Signs p6825 (bank6825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6826 := params 9
abbrev ray6826 := rays 9
def bank6826 : Fin 2 → Cell := twoBank p6826 ray6826
theorem signs6826 : ∀ j, Signs p6826 (bank6826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6827 := params 10
abbrev ray6827 := rays 10
def bank6827 : Fin 2 → Cell := twoBank p6827 ray6827
theorem signs6827 : ∀ j, Signs p6827 (bank6827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6828 := params 11
abbrev ray6828 := rays 11
def bank6828 : Fin 2 → Cell := twoBank p6828 ray6828
theorem signs6828 : ∀ j, Signs p6828 (bank6828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6829 := params 12
abbrev ray6829 := rays 12
def bank6829 : Fin 2 → Cell := twoBank p6829 ray6829
theorem signs6829 : ∀ j, Signs p6829 (bank6829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6830 := params 13
abbrev ray6830 := rays 13
def bank6830 : Fin 2 → Cell := twoBank p6830 ray6830
theorem signs6830 : ∀ j, Signs p6830 (bank6830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6831 := params 14
abbrev ray6831 := rays 14
def bank6831 : Fin 2 → Cell := twoBank p6831 ray6831
theorem signs6831 : ∀ j, Signs p6831 (bank6831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6832 := params 15
abbrev ray6832 := rays 15
def bank6832 : Fin 2 → Cell := twoBank p6832 ray6832
theorem signs6832 : ∀ j, Signs p6832 (bank6832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6833 := params 16
abbrev ray6833 := rays 16
def bank6833 : Fin 2 → Cell := twoBank p6833 ray6833
theorem signs6833 : ∀ j, Signs p6833 (bank6833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6834 := params 17
abbrev ray6834 := rays 17
def bank6834 : Fin 2 → Cell := twoBank p6834 ray6834
theorem signs6834 : ∀ j, Signs p6834 (bank6834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6835 := params 18
abbrev ray6835 := rays 18
def bank6835 : Fin 2 → Cell := twoBank p6835 ray6835
theorem signs6835 : ∀ j, Signs p6835 (bank6835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6836 := params 19
abbrev ray6836 := rays 19
def bank6836 : Fin 2 → Cell := twoBank p6836 ray6836
theorem signs6836 : ∀ j, Signs p6836 (bank6836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6837 := params 20
abbrev ray6837 := rays 20
def bank6837 : Fin 2 → Cell := twoBank p6837 ray6837
theorem signs6837 : ∀ j, Signs p6837 (bank6837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6838 := params 21
abbrev ray6838 := rays 21
def bank6838 : Fin 2 → Cell := twoBank p6838 ray6838
theorem signs6838 : ∀ j, Signs p6838 (bank6838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6839 := params 22
abbrev ray6839 := rays 22
def bank6839 : Fin 2 → Cell := twoBank p6839 ray6839
theorem signs6839 : ∀ j, Signs p6839 (bank6839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6840 := params 23
abbrev ray6840 := rays 23
def bank6840 : Fin 2 → Cell := twoBank p6840 ray6840
theorem signs6840 : ∀ j, Signs p6840 (bank6840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6841 := params 24
abbrev ray6841 := rays 24
def bank6841 : Fin 2 → Cell := twoBank p6841 ray6841
theorem signs6841 : ∀ j, Signs p6841 (bank6841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6842 := params 25
abbrev ray6842 := rays 25
def bank6842 : Fin 2 → Cell := twoBank p6842 ray6842
theorem signs6842 : ∀ j, Signs p6842 (bank6842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6843 := params 26
abbrev ray6843 := rays 26
def bank6843 : Fin 2 → Cell := twoBank p6843 ray6843
theorem signs6843 : ∀ j, Signs p6843 (bank6843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6844 := params 27
abbrev ray6844 := rays 27
def bank6844 : Fin 2 → Cell := twoBank p6844 ray6844
theorem signs6844 : ∀ j, Signs p6844 (bank6844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6845 := params 28
abbrev ray6845 := rays 28
def bank6845 : Fin 2 → Cell := twoBank p6845 ray6845
theorem signs6845 : ∀ j, Signs p6845 (bank6845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6846 := params 29
abbrev ray6846 := rays 29
def bank6846 : Fin 2 → Cell := twoBank p6846 ray6846
theorem signs6846 : ∀ j, Signs p6846 (bank6846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6847 := params 30
abbrev ray6847 := rays 30
def bank6847 : Fin 2 → Cell := twoBank p6847 ray6847
theorem signs6847 : ∀ j, Signs p6847 (bank6847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6848 := params 31
abbrev ray6848 := rays 31
def bank6848 : Fin 2 → Cell := twoBank p6848 ray6848
theorem signs6848 : ∀ j, Signs p6848 (bank6848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06817_06848
