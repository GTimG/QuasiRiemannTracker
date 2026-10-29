/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09825_09856
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97533960069067,97533597020919,97533233952335,97532870863317,97532507753865,97532144623979,97531781473660,97531418302909,97531055111726,97530691900112,97530328668067,97529965415592,97529602142688,97529238849355,97528875535593,97528512201404,97528148846787,97527785471744,97527422076274,97527058660379,97526695224059,97526331767314,97525968290146,97525604792554,97525241274539,97524877736102,97524514177244,97524150597965,97523786998265,97523423378145,97523059737606,97522696076648,97522332395272]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9824+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9825 := params 0
abbrev ray9825 := rays 0
def bank9825 : Fin 2 → Cell := twoBank p9825 ray9825
theorem signs9825 : ∀ j, Signs p9825 (bank9825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9826 := params 1
abbrev ray9826 := rays 1
def bank9826 : Fin 2 → Cell := twoBank p9826 ray9826
theorem signs9826 : ∀ j, Signs p9826 (bank9826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9827 := params 2
abbrev ray9827 := rays 2
def bank9827 : Fin 2 → Cell := twoBank p9827 ray9827
theorem signs9827 : ∀ j, Signs p9827 (bank9827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9828 := params 3
abbrev ray9828 := rays 3
def bank9828 : Fin 2 → Cell := twoBank p9828 ray9828
theorem signs9828 : ∀ j, Signs p9828 (bank9828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9829 := params 4
abbrev ray9829 := rays 4
def bank9829 : Fin 2 → Cell := twoBank p9829 ray9829
theorem signs9829 : ∀ j, Signs p9829 (bank9829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9830 := params 5
abbrev ray9830 := rays 5
def bank9830 : Fin 2 → Cell := twoBank p9830 ray9830
theorem signs9830 : ∀ j, Signs p9830 (bank9830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9831 := params 6
abbrev ray9831 := rays 6
def bank9831 : Fin 2 → Cell := twoBank p9831 ray9831
theorem signs9831 : ∀ j, Signs p9831 (bank9831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9832 := params 7
abbrev ray9832 := rays 7
def bank9832 : Fin 2 → Cell := twoBank p9832 ray9832
theorem signs9832 : ∀ j, Signs p9832 (bank9832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9833 := params 8
abbrev ray9833 := rays 8
def bank9833 : Fin 2 → Cell := twoBank p9833 ray9833
theorem signs9833 : ∀ j, Signs p9833 (bank9833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9834 := params 9
abbrev ray9834 := rays 9
def bank9834 : Fin 2 → Cell := twoBank p9834 ray9834
theorem signs9834 : ∀ j, Signs p9834 (bank9834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9835 := params 10
abbrev ray9835 := rays 10
def bank9835 : Fin 2 → Cell := twoBank p9835 ray9835
theorem signs9835 : ∀ j, Signs p9835 (bank9835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9836 := params 11
abbrev ray9836 := rays 11
def bank9836 : Fin 2 → Cell := twoBank p9836 ray9836
theorem signs9836 : ∀ j, Signs p9836 (bank9836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9837 := params 12
abbrev ray9837 := rays 12
def bank9837 : Fin 2 → Cell := twoBank p9837 ray9837
theorem signs9837 : ∀ j, Signs p9837 (bank9837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9838 := params 13
abbrev ray9838 := rays 13
def bank9838 : Fin 2 → Cell := twoBank p9838 ray9838
theorem signs9838 : ∀ j, Signs p9838 (bank9838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9839 := params 14
abbrev ray9839 := rays 14
def bank9839 : Fin 2 → Cell := twoBank p9839 ray9839
theorem signs9839 : ∀ j, Signs p9839 (bank9839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9840 := params 15
abbrev ray9840 := rays 15
def bank9840 : Fin 2 → Cell := twoBank p9840 ray9840
theorem signs9840 : ∀ j, Signs p9840 (bank9840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9841 := params 16
abbrev ray9841 := rays 16
def bank9841 : Fin 2 → Cell := twoBank p9841 ray9841
theorem signs9841 : ∀ j, Signs p9841 (bank9841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9842 := params 17
abbrev ray9842 := rays 17
def bank9842 : Fin 2 → Cell := twoBank p9842 ray9842
theorem signs9842 : ∀ j, Signs p9842 (bank9842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9843 := params 18
abbrev ray9843 := rays 18
def bank9843 : Fin 2 → Cell := twoBank p9843 ray9843
theorem signs9843 : ∀ j, Signs p9843 (bank9843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9844 := params 19
abbrev ray9844 := rays 19
def bank9844 : Fin 2 → Cell := twoBank p9844 ray9844
theorem signs9844 : ∀ j, Signs p9844 (bank9844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9845 := params 20
abbrev ray9845 := rays 20
def bank9845 : Fin 2 → Cell := twoBank p9845 ray9845
theorem signs9845 : ∀ j, Signs p9845 (bank9845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9846 := params 21
abbrev ray9846 := rays 21
def bank9846 : Fin 2 → Cell := twoBank p9846 ray9846
theorem signs9846 : ∀ j, Signs p9846 (bank9846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9847 := params 22
abbrev ray9847 := rays 22
def bank9847 : Fin 2 → Cell := twoBank p9847 ray9847
theorem signs9847 : ∀ j, Signs p9847 (bank9847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9848 := params 23
abbrev ray9848 := rays 23
def bank9848 : Fin 2 → Cell := twoBank p9848 ray9848
theorem signs9848 : ∀ j, Signs p9848 (bank9848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9849 := params 24
abbrev ray9849 := rays 24
def bank9849 : Fin 2 → Cell := twoBank p9849 ray9849
theorem signs9849 : ∀ j, Signs p9849 (bank9849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9850 := params 25
abbrev ray9850 := rays 25
def bank9850 : Fin 2 → Cell := twoBank p9850 ray9850
theorem signs9850 : ∀ j, Signs p9850 (bank9850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9851 := params 26
abbrev ray9851 := rays 26
def bank9851 : Fin 2 → Cell := twoBank p9851 ray9851
theorem signs9851 : ∀ j, Signs p9851 (bank9851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9852 := params 27
abbrev ray9852 := rays 27
def bank9852 : Fin 2 → Cell := twoBank p9852 ray9852
theorem signs9852 : ∀ j, Signs p9852 (bank9852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9853 := params 28
abbrev ray9853 := rays 28
def bank9853 : Fin 2 → Cell := twoBank p9853 ray9853
theorem signs9853 : ∀ j, Signs p9853 (bank9853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9854 := params 29
abbrev ray9854 := rays 29
def bank9854 : Fin 2 → Cell := twoBank p9854 ray9854
theorem signs9854 : ∀ j, Signs p9854 (bank9854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9855 := params 30
abbrev ray9855 := rays 30
def bank9855 : Fin 2 → Cell := twoBank p9855 ray9855
theorem signs9855 : ∀ j, Signs p9855 (bank9855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9856 := params 31
abbrev ray9856 := rays 31
def bank9856 : Fin 2 → Cell := twoBank p9856 ray9856
theorem signs9856 : ∀ j, Signs p9856 (bank9856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09825_09856
