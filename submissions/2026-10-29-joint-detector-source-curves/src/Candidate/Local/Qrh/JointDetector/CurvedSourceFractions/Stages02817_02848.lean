/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02817_02848
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99535938687722,99535737478947,99535536243576,99535334981610,99535133693050,99534932377898,99534731036155,99534529667822,99534328272900,99534126851391,99533925403296,99533723928617,99533522427354,99533320899509,99533119345084,99532917764079,99532716156496,99532514522336,99532312861601,99532111174292,99531909460410,99531707719956,99531505952932,99531304159339,99531102339178,99530900492451,99530698619159,99530496719303,99530294792884,99530092839904,99529890860364,99529688854266,99529486821610]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2816+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2817 := params 0
abbrev ray2817 := rays 0
def bank2817 : Fin 2 → Cell := twoBank p2817 ray2817
theorem signs2817 : ∀ j, Signs p2817 (bank2817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2818 := params 1
abbrev ray2818 := rays 1
def bank2818 : Fin 2 → Cell := twoBank p2818 ray2818
theorem signs2818 : ∀ j, Signs p2818 (bank2818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2819 := params 2
abbrev ray2819 := rays 2
def bank2819 : Fin 2 → Cell := twoBank p2819 ray2819
theorem signs2819 : ∀ j, Signs p2819 (bank2819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2820 := params 3
abbrev ray2820 := rays 3
def bank2820 : Fin 2 → Cell := twoBank p2820 ray2820
theorem signs2820 : ∀ j, Signs p2820 (bank2820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2821 := params 4
abbrev ray2821 := rays 4
def bank2821 : Fin 2 → Cell := twoBank p2821 ray2821
theorem signs2821 : ∀ j, Signs p2821 (bank2821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2822 := params 5
abbrev ray2822 := rays 5
def bank2822 : Fin 2 → Cell := twoBank p2822 ray2822
theorem signs2822 : ∀ j, Signs p2822 (bank2822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2823 := params 6
abbrev ray2823 := rays 6
def bank2823 : Fin 2 → Cell := twoBank p2823 ray2823
theorem signs2823 : ∀ j, Signs p2823 (bank2823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2824 := params 7
abbrev ray2824 := rays 7
def bank2824 : Fin 2 → Cell := twoBank p2824 ray2824
theorem signs2824 : ∀ j, Signs p2824 (bank2824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2825 := params 8
abbrev ray2825 := rays 8
def bank2825 : Fin 2 → Cell := twoBank p2825 ray2825
theorem signs2825 : ∀ j, Signs p2825 (bank2825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2826 := params 9
abbrev ray2826 := rays 9
def bank2826 : Fin 2 → Cell := twoBank p2826 ray2826
theorem signs2826 : ∀ j, Signs p2826 (bank2826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2827 := params 10
abbrev ray2827 := rays 10
def bank2827 : Fin 2 → Cell := twoBank p2827 ray2827
theorem signs2827 : ∀ j, Signs p2827 (bank2827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2828 := params 11
abbrev ray2828 := rays 11
def bank2828 : Fin 2 → Cell := twoBank p2828 ray2828
theorem signs2828 : ∀ j, Signs p2828 (bank2828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2829 := params 12
abbrev ray2829 := rays 12
def bank2829 : Fin 2 → Cell := twoBank p2829 ray2829
theorem signs2829 : ∀ j, Signs p2829 (bank2829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2830 := params 13
abbrev ray2830 := rays 13
def bank2830 : Fin 2 → Cell := twoBank p2830 ray2830
theorem signs2830 : ∀ j, Signs p2830 (bank2830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2831 := params 14
abbrev ray2831 := rays 14
def bank2831 : Fin 2 → Cell := twoBank p2831 ray2831
theorem signs2831 : ∀ j, Signs p2831 (bank2831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2832 := params 15
abbrev ray2832 := rays 15
def bank2832 : Fin 2 → Cell := twoBank p2832 ray2832
theorem signs2832 : ∀ j, Signs p2832 (bank2832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2833 := params 16
abbrev ray2833 := rays 16
def bank2833 : Fin 2 → Cell := twoBank p2833 ray2833
theorem signs2833 : ∀ j, Signs p2833 (bank2833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2834 := params 17
abbrev ray2834 := rays 17
def bank2834 : Fin 2 → Cell := twoBank p2834 ray2834
theorem signs2834 : ∀ j, Signs p2834 (bank2834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2835 := params 18
abbrev ray2835 := rays 18
def bank2835 : Fin 2 → Cell := twoBank p2835 ray2835
theorem signs2835 : ∀ j, Signs p2835 (bank2835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2836 := params 19
abbrev ray2836 := rays 19
def bank2836 : Fin 2 → Cell := twoBank p2836 ray2836
theorem signs2836 : ∀ j, Signs p2836 (bank2836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2837 := params 20
abbrev ray2837 := rays 20
def bank2837 : Fin 2 → Cell := twoBank p2837 ray2837
theorem signs2837 : ∀ j, Signs p2837 (bank2837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2838 := params 21
abbrev ray2838 := rays 21
def bank2838 : Fin 2 → Cell := twoBank p2838 ray2838
theorem signs2838 : ∀ j, Signs p2838 (bank2838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2839 := params 22
abbrev ray2839 := rays 22
def bank2839 : Fin 2 → Cell := twoBank p2839 ray2839
theorem signs2839 : ∀ j, Signs p2839 (bank2839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2840 := params 23
abbrev ray2840 := rays 23
def bank2840 : Fin 2 → Cell := twoBank p2840 ray2840
theorem signs2840 : ∀ j, Signs p2840 (bank2840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2841 := params 24
abbrev ray2841 := rays 24
def bank2841 : Fin 2 → Cell := twoBank p2841 ray2841
theorem signs2841 : ∀ j, Signs p2841 (bank2841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2842 := params 25
abbrev ray2842 := rays 25
def bank2842 : Fin 2 → Cell := twoBank p2842 ray2842
theorem signs2842 : ∀ j, Signs p2842 (bank2842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2843 := params 26
abbrev ray2843 := rays 26
def bank2843 : Fin 2 → Cell := twoBank p2843 ray2843
theorem signs2843 : ∀ j, Signs p2843 (bank2843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2844 := params 27
abbrev ray2844 := rays 27
def bank2844 : Fin 2 → Cell := twoBank p2844 ray2844
theorem signs2844 : ∀ j, Signs p2844 (bank2844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2845 := params 28
abbrev ray2845 := rays 28
def bank2845 : Fin 2 → Cell := twoBank p2845 ray2845
theorem signs2845 : ∀ j, Signs p2845 (bank2845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2846 := params 29
abbrev ray2846 := rays 29
def bank2846 : Fin 2 → Cell := twoBank p2846 ray2846
theorem signs2846 : ∀ j, Signs p2846 (bank2846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2847 := params 30
abbrev ray2847 := rays 30
def bank2847 : Fin 2 → Cell := twoBank p2847 ray2847
theorem signs2847 : ∀ j, Signs p2847 (bank2847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2848 := params 31
abbrev ray2848 := rays 31
def bank2848 : Fin 2 → Cell := twoBank p2848 ray2848
theorem signs2848 : ∀ j, Signs p2848 (bank2848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02817_02848
