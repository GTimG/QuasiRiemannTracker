/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02881_02912
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99523007762145,99522804853827,99522601918995,99522398957651,99522195969797,99521992955433,99521789914561,99521586847183,99521383753299,99521180632911,99520977486020,99520774312628,99520571112735,99520367886343,99520164633454,99519961354068,99519758048187,99519554715812,99519351356945,99519147971586,99518944559737,99518741121400,99518537656575,99518334165264,99518130647468,99517927103189,99517723532428,99517519935186,99517316311464,99517112661264,99516908984587,99516705281434,99516501551807]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2880+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2881 := params 0
abbrev ray2881 := rays 0
def bank2881 : Fin 2 → Cell := twoBank p2881 ray2881
theorem signs2881 : ∀ j, Signs p2881 (bank2881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2882 := params 1
abbrev ray2882 := rays 1
def bank2882 : Fin 2 → Cell := twoBank p2882 ray2882
theorem signs2882 : ∀ j, Signs p2882 (bank2882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2883 := params 2
abbrev ray2883 := rays 2
def bank2883 : Fin 2 → Cell := twoBank p2883 ray2883
theorem signs2883 : ∀ j, Signs p2883 (bank2883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2884 := params 3
abbrev ray2884 := rays 3
def bank2884 : Fin 2 → Cell := twoBank p2884 ray2884
theorem signs2884 : ∀ j, Signs p2884 (bank2884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2885 := params 4
abbrev ray2885 := rays 4
def bank2885 : Fin 2 → Cell := twoBank p2885 ray2885
theorem signs2885 : ∀ j, Signs p2885 (bank2885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2886 := params 5
abbrev ray2886 := rays 5
def bank2886 : Fin 2 → Cell := twoBank p2886 ray2886
theorem signs2886 : ∀ j, Signs p2886 (bank2886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2887 := params 6
abbrev ray2887 := rays 6
def bank2887 : Fin 2 → Cell := twoBank p2887 ray2887
theorem signs2887 : ∀ j, Signs p2887 (bank2887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2888 := params 7
abbrev ray2888 := rays 7
def bank2888 : Fin 2 → Cell := twoBank p2888 ray2888
theorem signs2888 : ∀ j, Signs p2888 (bank2888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2889 := params 8
abbrev ray2889 := rays 8
def bank2889 : Fin 2 → Cell := twoBank p2889 ray2889
theorem signs2889 : ∀ j, Signs p2889 (bank2889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2890 := params 9
abbrev ray2890 := rays 9
def bank2890 : Fin 2 → Cell := twoBank p2890 ray2890
theorem signs2890 : ∀ j, Signs p2890 (bank2890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2891 := params 10
abbrev ray2891 := rays 10
def bank2891 : Fin 2 → Cell := twoBank p2891 ray2891
theorem signs2891 : ∀ j, Signs p2891 (bank2891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2892 := params 11
abbrev ray2892 := rays 11
def bank2892 : Fin 2 → Cell := twoBank p2892 ray2892
theorem signs2892 : ∀ j, Signs p2892 (bank2892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2893 := params 12
abbrev ray2893 := rays 12
def bank2893 : Fin 2 → Cell := twoBank p2893 ray2893
theorem signs2893 : ∀ j, Signs p2893 (bank2893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2894 := params 13
abbrev ray2894 := rays 13
def bank2894 : Fin 2 → Cell := twoBank p2894 ray2894
theorem signs2894 : ∀ j, Signs p2894 (bank2894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2895 := params 14
abbrev ray2895 := rays 14
def bank2895 : Fin 2 → Cell := twoBank p2895 ray2895
theorem signs2895 : ∀ j, Signs p2895 (bank2895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2896 := params 15
abbrev ray2896 := rays 15
def bank2896 : Fin 2 → Cell := twoBank p2896 ray2896
theorem signs2896 : ∀ j, Signs p2896 (bank2896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2897 := params 16
abbrev ray2897 := rays 16
def bank2897 : Fin 2 → Cell := twoBank p2897 ray2897
theorem signs2897 : ∀ j, Signs p2897 (bank2897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2898 := params 17
abbrev ray2898 := rays 17
def bank2898 : Fin 2 → Cell := twoBank p2898 ray2898
theorem signs2898 : ∀ j, Signs p2898 (bank2898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2899 := params 18
abbrev ray2899 := rays 18
def bank2899 : Fin 2 → Cell := twoBank p2899 ray2899
theorem signs2899 : ∀ j, Signs p2899 (bank2899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2900 := params 19
abbrev ray2900 := rays 19
def bank2900 : Fin 2 → Cell := twoBank p2900 ray2900
theorem signs2900 : ∀ j, Signs p2900 (bank2900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2901 := params 20
abbrev ray2901 := rays 20
def bank2901 : Fin 2 → Cell := twoBank p2901 ray2901
theorem signs2901 : ∀ j, Signs p2901 (bank2901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2902 := params 21
abbrev ray2902 := rays 21
def bank2902 : Fin 2 → Cell := twoBank p2902 ray2902
theorem signs2902 : ∀ j, Signs p2902 (bank2902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2903 := params 22
abbrev ray2903 := rays 22
def bank2903 : Fin 2 → Cell := twoBank p2903 ray2903
theorem signs2903 : ∀ j, Signs p2903 (bank2903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2904 := params 23
abbrev ray2904 := rays 23
def bank2904 : Fin 2 → Cell := twoBank p2904 ray2904
theorem signs2904 : ∀ j, Signs p2904 (bank2904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2905 := params 24
abbrev ray2905 := rays 24
def bank2905 : Fin 2 → Cell := twoBank p2905 ray2905
theorem signs2905 : ∀ j, Signs p2905 (bank2905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2906 := params 25
abbrev ray2906 := rays 25
def bank2906 : Fin 2 → Cell := twoBank p2906 ray2906
theorem signs2906 : ∀ j, Signs p2906 (bank2906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2907 := params 26
abbrev ray2907 := rays 26
def bank2907 : Fin 2 → Cell := twoBank p2907 ray2907
theorem signs2907 : ∀ j, Signs p2907 (bank2907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2908 := params 27
abbrev ray2908 := rays 27
def bank2908 : Fin 2 → Cell := twoBank p2908 ray2908
theorem signs2908 : ∀ j, Signs p2908 (bank2908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2909 := params 28
abbrev ray2909 := rays 28
def bank2909 : Fin 2 → Cell := twoBank p2909 ray2909
theorem signs2909 : ∀ j, Signs p2909 (bank2909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2910 := params 29
abbrev ray2910 := rays 29
def bank2910 : Fin 2 → Cell := twoBank p2910 ray2910
theorem signs2910 : ∀ j, Signs p2910 (bank2910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2911 := params 30
abbrev ray2911 := rays 30
def bank2911 : Fin 2 → Cell := twoBank p2911 ray2911
theorem signs2911 : ∀ j, Signs p2911 (bank2911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2912 := params 31
abbrev ray2912 := rays 31
def bank2912 : Fin 2 → Cell := twoBank p2912 ray2912
theorem signs2912 : ∀ j, Signs p2912 (bank2912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02881_02912
