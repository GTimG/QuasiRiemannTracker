/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14817_14848
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95482206364249,95481751968788,95481297557240,95480843129604,95480388685881,95479934226071,95479479750174,95479025258190,95478570750120,95478116225963,95477661685720,95477207129390,95476752556974,95476297968472,95475843363884,95475388743210,95474934106451,95474479453606,95474024784676,95473570099660,95473115398559,95472660681373,95472205948102,95471751198746,95471296433306,95470841651781,95470386854172,95469932040478,95469477210700,95469022364838,95468567502892,95468112624862,95467657730748]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14816+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14817 := params 0
abbrev ray14817 := rays 0
def bank14817 : Fin 1 → Cell := oneBank p14817 ray14817
theorem signs14817 : ∀ j, Signs p14817 (bank14817 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14818 := params 1
abbrev ray14818 := rays 1
def bank14818 : Fin 1 → Cell := oneBank p14818 ray14818
theorem signs14818 : ∀ j, Signs p14818 (bank14818 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14819 := params 2
abbrev ray14819 := rays 2
def bank14819 : Fin 1 → Cell := oneBank p14819 ray14819
theorem signs14819 : ∀ j, Signs p14819 (bank14819 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14820 := params 3
abbrev ray14820 := rays 3
def bank14820 : Fin 1 → Cell := oneBank p14820 ray14820
theorem signs14820 : ∀ j, Signs p14820 (bank14820 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14821 := params 4
abbrev ray14821 := rays 4
def bank14821 : Fin 1 → Cell := oneBank p14821 ray14821
theorem signs14821 : ∀ j, Signs p14821 (bank14821 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14822 := params 5
abbrev ray14822 := rays 5
def bank14822 : Fin 1 → Cell := oneBank p14822 ray14822
theorem signs14822 : ∀ j, Signs p14822 (bank14822 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14823 := params 6
abbrev ray14823 := rays 6
def bank14823 : Fin 1 → Cell := oneBank p14823 ray14823
theorem signs14823 : ∀ j, Signs p14823 (bank14823 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14824 := params 7
abbrev ray14824 := rays 7
def bank14824 : Fin 1 → Cell := oneBank p14824 ray14824
theorem signs14824 : ∀ j, Signs p14824 (bank14824 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14825 := params 8
abbrev ray14825 := rays 8
def bank14825 : Fin 1 → Cell := oneBank p14825 ray14825
theorem signs14825 : ∀ j, Signs p14825 (bank14825 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14826 := params 9
abbrev ray14826 := rays 9
def bank14826 : Fin 1 → Cell := oneBank p14826 ray14826
theorem signs14826 : ∀ j, Signs p14826 (bank14826 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14827 := params 10
abbrev ray14827 := rays 10
def bank14827 : Fin 1 → Cell := oneBank p14827 ray14827
theorem signs14827 : ∀ j, Signs p14827 (bank14827 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14828 := params 11
abbrev ray14828 := rays 11
def bank14828 : Fin 1 → Cell := oneBank p14828 ray14828
theorem signs14828 : ∀ j, Signs p14828 (bank14828 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14829 := params 12
abbrev ray14829 := rays 12
def bank14829 : Fin 1 → Cell := oneBank p14829 ray14829
theorem signs14829 : ∀ j, Signs p14829 (bank14829 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14830 := params 13
abbrev ray14830 := rays 13
def bank14830 : Fin 1 → Cell := oneBank p14830 ray14830
theorem signs14830 : ∀ j, Signs p14830 (bank14830 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14831 := params 14
abbrev ray14831 := rays 14
def bank14831 : Fin 1 → Cell := oneBank p14831 ray14831
theorem signs14831 : ∀ j, Signs p14831 (bank14831 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14832 := params 15
abbrev ray14832 := rays 15
def bank14832 : Fin 1 → Cell := oneBank p14832 ray14832
theorem signs14832 : ∀ j, Signs p14832 (bank14832 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14833 := params 16
abbrev ray14833 := rays 16
def bank14833 : Fin 1 → Cell := oneBank p14833 ray14833
theorem signs14833 : ∀ j, Signs p14833 (bank14833 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14834 := params 17
abbrev ray14834 := rays 17
def bank14834 : Fin 1 → Cell := oneBank p14834 ray14834
theorem signs14834 : ∀ j, Signs p14834 (bank14834 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14835 := params 18
abbrev ray14835 := rays 18
def bank14835 : Fin 1 → Cell := oneBank p14835 ray14835
theorem signs14835 : ∀ j, Signs p14835 (bank14835 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14836 := params 19
abbrev ray14836 := rays 19
def bank14836 : Fin 1 → Cell := oneBank p14836 ray14836
theorem signs14836 : ∀ j, Signs p14836 (bank14836 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14837 := params 20
abbrev ray14837 := rays 20
def bank14837 : Fin 1 → Cell := oneBank p14837 ray14837
theorem signs14837 : ∀ j, Signs p14837 (bank14837 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14838 := params 21
abbrev ray14838 := rays 21
def bank14838 : Fin 1 → Cell := oneBank p14838 ray14838
theorem signs14838 : ∀ j, Signs p14838 (bank14838 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14839 := params 22
abbrev ray14839 := rays 22
def bank14839 : Fin 1 → Cell := oneBank p14839 ray14839
theorem signs14839 : ∀ j, Signs p14839 (bank14839 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14840 := params 23
abbrev ray14840 := rays 23
def bank14840 : Fin 1 → Cell := oneBank p14840 ray14840
theorem signs14840 : ∀ j, Signs p14840 (bank14840 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14841 := params 24
abbrev ray14841 := rays 24
def bank14841 : Fin 1 → Cell := oneBank p14841 ray14841
theorem signs14841 : ∀ j, Signs p14841 (bank14841 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14842 := params 25
abbrev ray14842 := rays 25
def bank14842 : Fin 1 → Cell := oneBank p14842 ray14842
theorem signs14842 : ∀ j, Signs p14842 (bank14842 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14843 := params 26
abbrev ray14843 := rays 26
def bank14843 : Fin 1 → Cell := oneBank p14843 ray14843
theorem signs14843 : ∀ j, Signs p14843 (bank14843 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14844 := params 27
abbrev ray14844 := rays 27
def bank14844 : Fin 1 → Cell := oneBank p14844 ray14844
theorem signs14844 : ∀ j, Signs p14844 (bank14844 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14845 := params 28
abbrev ray14845 := rays 28
def bank14845 : Fin 1 → Cell := oneBank p14845 ray14845
theorem signs14845 : ∀ j, Signs p14845 (bank14845 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14846 := params 29
abbrev ray14846 := rays 29
def bank14846 : Fin 1 → Cell := oneBank p14846 ray14846
theorem signs14846 : ∀ j, Signs p14846 (bank14846 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14847 := params 30
abbrev ray14847 := rays 30
def bank14847 : Fin 1 → Cell := oneBank p14847 ray14847
theorem signs14847 : ∀ j, Signs p14847 (bank14847 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14848 := params 31
abbrev ray14848 := rays 31
def bank14848 : Fin 1 → Cell := oneBank p14848 ray14848
theorem signs14848 : ∀ j, Signs p14848 (bank14848 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14817_14848
