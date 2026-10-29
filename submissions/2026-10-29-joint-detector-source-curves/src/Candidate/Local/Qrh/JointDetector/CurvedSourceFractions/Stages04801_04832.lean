/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04801_04832
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99086016300536,99085764690244,99085513055648,99085261396749,99085009713548,99084758006046,99084506274244,99084254518144,99084002737746,99083750933051,99083499104060,99083247250774,99082995373194,99082743471322,99082491545158,99082239594703,99081987619958,99081735620925,99081483597604,99081231549996,99080979478103,99080727381925,99080475261464,99080223116720,99079970947694,99079718754388,99079466536802,99079214294938,99078962028796,99078709738378,99078457423684,99078205084716,99077952721475]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4800+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4801 := params 0
abbrev ray4801 := rays 0
def bank4801 : Fin 2 → Cell := twoBank p4801 ray4801
theorem signs4801 : ∀ j, Signs p4801 (bank4801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4802 := params 1
abbrev ray4802 := rays 1
def bank4802 : Fin 2 → Cell := twoBank p4802 ray4802
theorem signs4802 : ∀ j, Signs p4802 (bank4802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4803 := params 2
abbrev ray4803 := rays 2
def bank4803 : Fin 2 → Cell := twoBank p4803 ray4803
theorem signs4803 : ∀ j, Signs p4803 (bank4803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4804 := params 3
abbrev ray4804 := rays 3
def bank4804 : Fin 2 → Cell := twoBank p4804 ray4804
theorem signs4804 : ∀ j, Signs p4804 (bank4804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4805 := params 4
abbrev ray4805 := rays 4
def bank4805 : Fin 2 → Cell := twoBank p4805 ray4805
theorem signs4805 : ∀ j, Signs p4805 (bank4805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4806 := params 5
abbrev ray4806 := rays 5
def bank4806 : Fin 2 → Cell := twoBank p4806 ray4806
theorem signs4806 : ∀ j, Signs p4806 (bank4806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4807 := params 6
abbrev ray4807 := rays 6
def bank4807 : Fin 2 → Cell := twoBank p4807 ray4807
theorem signs4807 : ∀ j, Signs p4807 (bank4807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4808 := params 7
abbrev ray4808 := rays 7
def bank4808 : Fin 2 → Cell := twoBank p4808 ray4808
theorem signs4808 : ∀ j, Signs p4808 (bank4808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4809 := params 8
abbrev ray4809 := rays 8
def bank4809 : Fin 2 → Cell := twoBank p4809 ray4809
theorem signs4809 : ∀ j, Signs p4809 (bank4809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4810 := params 9
abbrev ray4810 := rays 9
def bank4810 : Fin 2 → Cell := twoBank p4810 ray4810
theorem signs4810 : ∀ j, Signs p4810 (bank4810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4811 := params 10
abbrev ray4811 := rays 10
def bank4811 : Fin 2 → Cell := twoBank p4811 ray4811
theorem signs4811 : ∀ j, Signs p4811 (bank4811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4812 := params 11
abbrev ray4812 := rays 11
def bank4812 : Fin 2 → Cell := twoBank p4812 ray4812
theorem signs4812 : ∀ j, Signs p4812 (bank4812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4813 := params 12
abbrev ray4813 := rays 12
def bank4813 : Fin 2 → Cell := twoBank p4813 ray4813
theorem signs4813 : ∀ j, Signs p4813 (bank4813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4814 := params 13
abbrev ray4814 := rays 13
def bank4814 : Fin 2 → Cell := twoBank p4814 ray4814
theorem signs4814 : ∀ j, Signs p4814 (bank4814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4815 := params 14
abbrev ray4815 := rays 14
def bank4815 : Fin 2 → Cell := twoBank p4815 ray4815
theorem signs4815 : ∀ j, Signs p4815 (bank4815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4816 := params 15
abbrev ray4816 := rays 15
def bank4816 : Fin 2 → Cell := twoBank p4816 ray4816
theorem signs4816 : ∀ j, Signs p4816 (bank4816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4817 := params 16
abbrev ray4817 := rays 16
def bank4817 : Fin 2 → Cell := twoBank p4817 ray4817
theorem signs4817 : ∀ j, Signs p4817 (bank4817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4818 := params 17
abbrev ray4818 := rays 17
def bank4818 : Fin 2 → Cell := twoBank p4818 ray4818
theorem signs4818 : ∀ j, Signs p4818 (bank4818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4819 := params 18
abbrev ray4819 := rays 18
def bank4819 : Fin 2 → Cell := twoBank p4819 ray4819
theorem signs4819 : ∀ j, Signs p4819 (bank4819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4820 := params 19
abbrev ray4820 := rays 19
def bank4820 : Fin 2 → Cell := twoBank p4820 ray4820
theorem signs4820 : ∀ j, Signs p4820 (bank4820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4821 := params 20
abbrev ray4821 := rays 20
def bank4821 : Fin 2 → Cell := twoBank p4821 ray4821
theorem signs4821 : ∀ j, Signs p4821 (bank4821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4822 := params 21
abbrev ray4822 := rays 21
def bank4822 : Fin 2 → Cell := twoBank p4822 ray4822
theorem signs4822 : ∀ j, Signs p4822 (bank4822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4823 := params 22
abbrev ray4823 := rays 22
def bank4823 : Fin 2 → Cell := twoBank p4823 ray4823
theorem signs4823 : ∀ j, Signs p4823 (bank4823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4824 := params 23
abbrev ray4824 := rays 23
def bank4824 : Fin 2 → Cell := twoBank p4824 ray4824
theorem signs4824 : ∀ j, Signs p4824 (bank4824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4825 := params 24
abbrev ray4825 := rays 24
def bank4825 : Fin 2 → Cell := twoBank p4825 ray4825
theorem signs4825 : ∀ j, Signs p4825 (bank4825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4826 := params 25
abbrev ray4826 := rays 25
def bank4826 : Fin 2 → Cell := twoBank p4826 ray4826
theorem signs4826 : ∀ j, Signs p4826 (bank4826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4827 := params 26
abbrev ray4827 := rays 26
def bank4827 : Fin 2 → Cell := twoBank p4827 ray4827
theorem signs4827 : ∀ j, Signs p4827 (bank4827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4828 := params 27
abbrev ray4828 := rays 27
def bank4828 : Fin 2 → Cell := twoBank p4828 ray4828
theorem signs4828 : ∀ j, Signs p4828 (bank4828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4829 := params 28
abbrev ray4829 := rays 28
def bank4829 : Fin 2 → Cell := twoBank p4829 ray4829
theorem signs4829 : ∀ j, Signs p4829 (bank4829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4830 := params 29
abbrev ray4830 := rays 29
def bank4830 : Fin 2 → Cell := twoBank p4830 ray4830
theorem signs4830 : ∀ j, Signs p4830 (bank4830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4831 := params 30
abbrev ray4831 := rays 30
def bank4831 : Fin 2 → Cell := twoBank p4831 ray4831
theorem signs4831 : ∀ j, Signs p4831 (bank4831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4832 := params 31
abbrev ray4832 := rays 31
def bank4832 : Fin 2 → Cell := twoBank p4832 ray4832
theorem signs4832 : ∀ j, Signs p4832 (bank4832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04801_04832
