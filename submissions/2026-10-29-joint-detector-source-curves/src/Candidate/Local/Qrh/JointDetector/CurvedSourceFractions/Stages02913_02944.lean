/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02913_02944
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99516501551807,99516297795706,99516094013133,99515890204090,99515686368577,99515482506596,99515278618149,99515074703236,99514870761859,99514666794019,99514462799718,99514258778956,99514054731735,99513850658056,99513646557921,99513442431331,99513238278287,99513034098790,99512829892842,99512625660444,99512421401597,99512217116303,99512012804563,99511808466378,99511604101749,99511399710678,99511195293166,99510990849214,99510786378824,99510581881996,99510377358732,99510172809034,99509968232903]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2912+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2913 := params 0
abbrev ray2913 := rays 0
def bank2913 : Fin 2 → Cell := twoBank p2913 ray2913
theorem signs2913 : ∀ j, Signs p2913 (bank2913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2914 := params 1
abbrev ray2914 := rays 1
def bank2914 : Fin 2 → Cell := twoBank p2914 ray2914
theorem signs2914 : ∀ j, Signs p2914 (bank2914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2915 := params 2
abbrev ray2915 := rays 2
def bank2915 : Fin 2 → Cell := twoBank p2915 ray2915
theorem signs2915 : ∀ j, Signs p2915 (bank2915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2916 := params 3
abbrev ray2916 := rays 3
def bank2916 : Fin 2 → Cell := twoBank p2916 ray2916
theorem signs2916 : ∀ j, Signs p2916 (bank2916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2917 := params 4
abbrev ray2917 := rays 4
def bank2917 : Fin 2 → Cell := twoBank p2917 ray2917
theorem signs2917 : ∀ j, Signs p2917 (bank2917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2918 := params 5
abbrev ray2918 := rays 5
def bank2918 : Fin 2 → Cell := twoBank p2918 ray2918
theorem signs2918 : ∀ j, Signs p2918 (bank2918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2919 := params 6
abbrev ray2919 := rays 6
def bank2919 : Fin 2 → Cell := twoBank p2919 ray2919
theorem signs2919 : ∀ j, Signs p2919 (bank2919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2920 := params 7
abbrev ray2920 := rays 7
def bank2920 : Fin 2 → Cell := twoBank p2920 ray2920
theorem signs2920 : ∀ j, Signs p2920 (bank2920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2921 := params 8
abbrev ray2921 := rays 8
def bank2921 : Fin 2 → Cell := twoBank p2921 ray2921
theorem signs2921 : ∀ j, Signs p2921 (bank2921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2922 := params 9
abbrev ray2922 := rays 9
def bank2922 : Fin 2 → Cell := twoBank p2922 ray2922
theorem signs2922 : ∀ j, Signs p2922 (bank2922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2923 := params 10
abbrev ray2923 := rays 10
def bank2923 : Fin 2 → Cell := twoBank p2923 ray2923
theorem signs2923 : ∀ j, Signs p2923 (bank2923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2924 := params 11
abbrev ray2924 := rays 11
def bank2924 : Fin 2 → Cell := twoBank p2924 ray2924
theorem signs2924 : ∀ j, Signs p2924 (bank2924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2925 := params 12
abbrev ray2925 := rays 12
def bank2925 : Fin 2 → Cell := twoBank p2925 ray2925
theorem signs2925 : ∀ j, Signs p2925 (bank2925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2926 := params 13
abbrev ray2926 := rays 13
def bank2926 : Fin 2 → Cell := twoBank p2926 ray2926
theorem signs2926 : ∀ j, Signs p2926 (bank2926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2927 := params 14
abbrev ray2927 := rays 14
def bank2927 : Fin 2 → Cell := twoBank p2927 ray2927
theorem signs2927 : ∀ j, Signs p2927 (bank2927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2928 := params 15
abbrev ray2928 := rays 15
def bank2928 : Fin 2 → Cell := twoBank p2928 ray2928
theorem signs2928 : ∀ j, Signs p2928 (bank2928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2929 := params 16
abbrev ray2929 := rays 16
def bank2929 : Fin 2 → Cell := twoBank p2929 ray2929
theorem signs2929 : ∀ j, Signs p2929 (bank2929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2930 := params 17
abbrev ray2930 := rays 17
def bank2930 : Fin 2 → Cell := twoBank p2930 ray2930
theorem signs2930 : ∀ j, Signs p2930 (bank2930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2931 := params 18
abbrev ray2931 := rays 18
def bank2931 : Fin 2 → Cell := twoBank p2931 ray2931
theorem signs2931 : ∀ j, Signs p2931 (bank2931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2932 := params 19
abbrev ray2932 := rays 19
def bank2932 : Fin 2 → Cell := twoBank p2932 ray2932
theorem signs2932 : ∀ j, Signs p2932 (bank2932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2933 := params 20
abbrev ray2933 := rays 20
def bank2933 : Fin 2 → Cell := twoBank p2933 ray2933
theorem signs2933 : ∀ j, Signs p2933 (bank2933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2934 := params 21
abbrev ray2934 := rays 21
def bank2934 : Fin 2 → Cell := twoBank p2934 ray2934
theorem signs2934 : ∀ j, Signs p2934 (bank2934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2935 := params 22
abbrev ray2935 := rays 22
def bank2935 : Fin 2 → Cell := twoBank p2935 ray2935
theorem signs2935 : ∀ j, Signs p2935 (bank2935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2936 := params 23
abbrev ray2936 := rays 23
def bank2936 : Fin 2 → Cell := twoBank p2936 ray2936
theorem signs2936 : ∀ j, Signs p2936 (bank2936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2937 := params 24
abbrev ray2937 := rays 24
def bank2937 : Fin 2 → Cell := twoBank p2937 ray2937
theorem signs2937 : ∀ j, Signs p2937 (bank2937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2938 := params 25
abbrev ray2938 := rays 25
def bank2938 : Fin 2 → Cell := twoBank p2938 ray2938
theorem signs2938 : ∀ j, Signs p2938 (bank2938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2939 := params 26
abbrev ray2939 := rays 26
def bank2939 : Fin 2 → Cell := twoBank p2939 ray2939
theorem signs2939 : ∀ j, Signs p2939 (bank2939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2940 := params 27
abbrev ray2940 := rays 27
def bank2940 : Fin 2 → Cell := twoBank p2940 ray2940
theorem signs2940 : ∀ j, Signs p2940 (bank2940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2941 := params 28
abbrev ray2941 := rays 28
def bank2941 : Fin 2 → Cell := twoBank p2941 ray2941
theorem signs2941 : ∀ j, Signs p2941 (bank2941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2942 := params 29
abbrev ray2942 := rays 29
def bank2942 : Fin 2 → Cell := twoBank p2942 ray2942
theorem signs2942 : ∀ j, Signs p2942 (bank2942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2943 := params 30
abbrev ray2943 := rays 30
def bank2943 : Fin 2 → Cell := twoBank p2943 ray2943
theorem signs2943 : ∀ j, Signs p2943 (bank2943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2944 := params 31
abbrev ray2944 := rays 31
def bank2944 : Fin 2 → Cell := twoBank p2944 ray2944
theorem signs2944 : ∀ j, Signs p2944 (bank2944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02913_02944
