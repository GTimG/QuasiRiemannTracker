/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04833_04864
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99077952721475,99077700333961,99077447922176,99077195486120,99076943025795,99076690541202,99076438032341,99076185499214,99075932941822,99075680360166,99075427754246,99075175124064,99074922469621,99074669790918,99074417087955,99074164360734,99073911609256,99073658833522,99073406033533,99073153209290,99072900360794,99072647488045,99072394591045,99072141669795,99071888724296,99071635754549,99071382760555,99071129742315,99070876699830,99070623633101,99070370542129,99070117426915,99069864287460]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4832+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4833 := params 0
abbrev ray4833 := rays 0
def bank4833 : Fin 2 → Cell := twoBank p4833 ray4833
theorem signs4833 : ∀ j, Signs p4833 (bank4833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4834 := params 1
abbrev ray4834 := rays 1
def bank4834 : Fin 2 → Cell := twoBank p4834 ray4834
theorem signs4834 : ∀ j, Signs p4834 (bank4834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4835 := params 2
abbrev ray4835 := rays 2
def bank4835 : Fin 2 → Cell := twoBank p4835 ray4835
theorem signs4835 : ∀ j, Signs p4835 (bank4835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4836 := params 3
abbrev ray4836 := rays 3
def bank4836 : Fin 2 → Cell := twoBank p4836 ray4836
theorem signs4836 : ∀ j, Signs p4836 (bank4836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4837 := params 4
abbrev ray4837 := rays 4
def bank4837 : Fin 2 → Cell := twoBank p4837 ray4837
theorem signs4837 : ∀ j, Signs p4837 (bank4837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4838 := params 5
abbrev ray4838 := rays 5
def bank4838 : Fin 2 → Cell := twoBank p4838 ray4838
theorem signs4838 : ∀ j, Signs p4838 (bank4838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4839 := params 6
abbrev ray4839 := rays 6
def bank4839 : Fin 2 → Cell := twoBank p4839 ray4839
theorem signs4839 : ∀ j, Signs p4839 (bank4839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4840 := params 7
abbrev ray4840 := rays 7
def bank4840 : Fin 2 → Cell := twoBank p4840 ray4840
theorem signs4840 : ∀ j, Signs p4840 (bank4840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4841 := params 8
abbrev ray4841 := rays 8
def bank4841 : Fin 2 → Cell := twoBank p4841 ray4841
theorem signs4841 : ∀ j, Signs p4841 (bank4841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4842 := params 9
abbrev ray4842 := rays 9
def bank4842 : Fin 2 → Cell := twoBank p4842 ray4842
theorem signs4842 : ∀ j, Signs p4842 (bank4842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4843 := params 10
abbrev ray4843 := rays 10
def bank4843 : Fin 2 → Cell := twoBank p4843 ray4843
theorem signs4843 : ∀ j, Signs p4843 (bank4843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4844 := params 11
abbrev ray4844 := rays 11
def bank4844 : Fin 2 → Cell := twoBank p4844 ray4844
theorem signs4844 : ∀ j, Signs p4844 (bank4844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4845 := params 12
abbrev ray4845 := rays 12
def bank4845 : Fin 2 → Cell := twoBank p4845 ray4845
theorem signs4845 : ∀ j, Signs p4845 (bank4845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4846 := params 13
abbrev ray4846 := rays 13
def bank4846 : Fin 2 → Cell := twoBank p4846 ray4846
theorem signs4846 : ∀ j, Signs p4846 (bank4846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4847 := params 14
abbrev ray4847 := rays 14
def bank4847 : Fin 2 → Cell := twoBank p4847 ray4847
theorem signs4847 : ∀ j, Signs p4847 (bank4847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4848 := params 15
abbrev ray4848 := rays 15
def bank4848 : Fin 2 → Cell := twoBank p4848 ray4848
theorem signs4848 : ∀ j, Signs p4848 (bank4848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4849 := params 16
abbrev ray4849 := rays 16
def bank4849 : Fin 2 → Cell := twoBank p4849 ray4849
theorem signs4849 : ∀ j, Signs p4849 (bank4849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4850 := params 17
abbrev ray4850 := rays 17
def bank4850 : Fin 2 → Cell := twoBank p4850 ray4850
theorem signs4850 : ∀ j, Signs p4850 (bank4850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4851 := params 18
abbrev ray4851 := rays 18
def bank4851 : Fin 2 → Cell := twoBank p4851 ray4851
theorem signs4851 : ∀ j, Signs p4851 (bank4851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4852 := params 19
abbrev ray4852 := rays 19
def bank4852 : Fin 2 → Cell := twoBank p4852 ray4852
theorem signs4852 : ∀ j, Signs p4852 (bank4852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4853 := params 20
abbrev ray4853 := rays 20
def bank4853 : Fin 2 → Cell := twoBank p4853 ray4853
theorem signs4853 : ∀ j, Signs p4853 (bank4853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4854 := params 21
abbrev ray4854 := rays 21
def bank4854 : Fin 2 → Cell := twoBank p4854 ray4854
theorem signs4854 : ∀ j, Signs p4854 (bank4854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4855 := params 22
abbrev ray4855 := rays 22
def bank4855 : Fin 2 → Cell := twoBank p4855 ray4855
theorem signs4855 : ∀ j, Signs p4855 (bank4855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4856 := params 23
abbrev ray4856 := rays 23
def bank4856 : Fin 2 → Cell := twoBank p4856 ray4856
theorem signs4856 : ∀ j, Signs p4856 (bank4856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4857 := params 24
abbrev ray4857 := rays 24
def bank4857 : Fin 2 → Cell := twoBank p4857 ray4857
theorem signs4857 : ∀ j, Signs p4857 (bank4857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4858 := params 25
abbrev ray4858 := rays 25
def bank4858 : Fin 2 → Cell := twoBank p4858 ray4858
theorem signs4858 : ∀ j, Signs p4858 (bank4858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4859 := params 26
abbrev ray4859 := rays 26
def bank4859 : Fin 2 → Cell := twoBank p4859 ray4859
theorem signs4859 : ∀ j, Signs p4859 (bank4859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4860 := params 27
abbrev ray4860 := rays 27
def bank4860 : Fin 2 → Cell := twoBank p4860 ray4860
theorem signs4860 : ∀ j, Signs p4860 (bank4860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4861 := params 28
abbrev ray4861 := rays 28
def bank4861 : Fin 2 → Cell := twoBank p4861 ray4861
theorem signs4861 : ∀ j, Signs p4861 (bank4861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4862 := params 29
abbrev ray4862 := rays 29
def bank4862 : Fin 2 → Cell := twoBank p4862 ray4862
theorem signs4862 : ∀ j, Signs p4862 (bank4862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4863 := params 30
abbrev ray4863 := rays 30
def bank4863 : Fin 2 → Cell := twoBank p4863 ray4863
theorem signs4863 : ∀ j, Signs p4863 (bank4863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4864 := params 31
abbrev ray4864 := rays 31
def bank4864 : Fin 2 → Cell := twoBank p4864 ray4864
theorem signs4864 : ∀ j, Signs p4864 (bank4864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04833_04864
