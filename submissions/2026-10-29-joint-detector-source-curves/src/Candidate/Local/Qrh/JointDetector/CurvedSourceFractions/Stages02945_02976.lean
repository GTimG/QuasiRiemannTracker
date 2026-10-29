/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02945_02976
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99509968232903,99509763630339,99509559001345,99509354345921,99509149664069,99508944955790,99508740221085,99508535459956,99508330672404,99508125858430,99507921018036,99507716151223,99507511257992,99507306338344,99507101392281,99506896419803,99506691420913,99506486395611,99506281343899,99506076265778,99505871161249,99505666030314,99505460872974,99505255689230,99505050479083,99504845242535,99504639979587,99504434690240,99504229374496,99504024032356,99503818663821,99503613268892,99503407847571]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2944+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2945 := params 0
abbrev ray2945 := rays 0
def bank2945 : Fin 2 → Cell := twoBank p2945 ray2945
theorem signs2945 : ∀ j, Signs p2945 (bank2945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2946 := params 1
abbrev ray2946 := rays 1
def bank2946 : Fin 2 → Cell := twoBank p2946 ray2946
theorem signs2946 : ∀ j, Signs p2946 (bank2946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2947 := params 2
abbrev ray2947 := rays 2
def bank2947 : Fin 2 → Cell := twoBank p2947 ray2947
theorem signs2947 : ∀ j, Signs p2947 (bank2947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2948 := params 3
abbrev ray2948 := rays 3
def bank2948 : Fin 2 → Cell := twoBank p2948 ray2948
theorem signs2948 : ∀ j, Signs p2948 (bank2948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2949 := params 4
abbrev ray2949 := rays 4
def bank2949 : Fin 2 → Cell := twoBank p2949 ray2949
theorem signs2949 : ∀ j, Signs p2949 (bank2949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2950 := params 5
abbrev ray2950 := rays 5
def bank2950 : Fin 2 → Cell := twoBank p2950 ray2950
theorem signs2950 : ∀ j, Signs p2950 (bank2950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2951 := params 6
abbrev ray2951 := rays 6
def bank2951 : Fin 2 → Cell := twoBank p2951 ray2951
theorem signs2951 : ∀ j, Signs p2951 (bank2951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2952 := params 7
abbrev ray2952 := rays 7
def bank2952 : Fin 2 → Cell := twoBank p2952 ray2952
theorem signs2952 : ∀ j, Signs p2952 (bank2952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2953 := params 8
abbrev ray2953 := rays 8
def bank2953 : Fin 2 → Cell := twoBank p2953 ray2953
theorem signs2953 : ∀ j, Signs p2953 (bank2953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2954 := params 9
abbrev ray2954 := rays 9
def bank2954 : Fin 2 → Cell := twoBank p2954 ray2954
theorem signs2954 : ∀ j, Signs p2954 (bank2954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2955 := params 10
abbrev ray2955 := rays 10
def bank2955 : Fin 2 → Cell := twoBank p2955 ray2955
theorem signs2955 : ∀ j, Signs p2955 (bank2955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2956 := params 11
abbrev ray2956 := rays 11
def bank2956 : Fin 2 → Cell := twoBank p2956 ray2956
theorem signs2956 : ∀ j, Signs p2956 (bank2956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2957 := params 12
abbrev ray2957 := rays 12
def bank2957 : Fin 2 → Cell := twoBank p2957 ray2957
theorem signs2957 : ∀ j, Signs p2957 (bank2957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2958 := params 13
abbrev ray2958 := rays 13
def bank2958 : Fin 2 → Cell := twoBank p2958 ray2958
theorem signs2958 : ∀ j, Signs p2958 (bank2958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2959 := params 14
abbrev ray2959 := rays 14
def bank2959 : Fin 2 → Cell := twoBank p2959 ray2959
theorem signs2959 : ∀ j, Signs p2959 (bank2959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2960 := params 15
abbrev ray2960 := rays 15
def bank2960 : Fin 2 → Cell := twoBank p2960 ray2960
theorem signs2960 : ∀ j, Signs p2960 (bank2960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2961 := params 16
abbrev ray2961 := rays 16
def bank2961 : Fin 2 → Cell := twoBank p2961 ray2961
theorem signs2961 : ∀ j, Signs p2961 (bank2961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2962 := params 17
abbrev ray2962 := rays 17
def bank2962 : Fin 2 → Cell := twoBank p2962 ray2962
theorem signs2962 : ∀ j, Signs p2962 (bank2962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2963 := params 18
abbrev ray2963 := rays 18
def bank2963 : Fin 2 → Cell := twoBank p2963 ray2963
theorem signs2963 : ∀ j, Signs p2963 (bank2963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2964 := params 19
abbrev ray2964 := rays 19
def bank2964 : Fin 2 → Cell := twoBank p2964 ray2964
theorem signs2964 : ∀ j, Signs p2964 (bank2964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2965 := params 20
abbrev ray2965 := rays 20
def bank2965 : Fin 2 → Cell := twoBank p2965 ray2965
theorem signs2965 : ∀ j, Signs p2965 (bank2965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2966 := params 21
abbrev ray2966 := rays 21
def bank2966 : Fin 2 → Cell := twoBank p2966 ray2966
theorem signs2966 : ∀ j, Signs p2966 (bank2966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2967 := params 22
abbrev ray2967 := rays 22
def bank2967 : Fin 2 → Cell := twoBank p2967 ray2967
theorem signs2967 : ∀ j, Signs p2967 (bank2967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2968 := params 23
abbrev ray2968 := rays 23
def bank2968 : Fin 2 → Cell := twoBank p2968 ray2968
theorem signs2968 : ∀ j, Signs p2968 (bank2968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2969 := params 24
abbrev ray2969 := rays 24
def bank2969 : Fin 2 → Cell := twoBank p2969 ray2969
theorem signs2969 : ∀ j, Signs p2969 (bank2969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2970 := params 25
abbrev ray2970 := rays 25
def bank2970 : Fin 2 → Cell := twoBank p2970 ray2970
theorem signs2970 : ∀ j, Signs p2970 (bank2970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2971 := params 26
abbrev ray2971 := rays 26
def bank2971 : Fin 2 → Cell := twoBank p2971 ray2971
theorem signs2971 : ∀ j, Signs p2971 (bank2971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2972 := params 27
abbrev ray2972 := rays 27
def bank2972 : Fin 2 → Cell := twoBank p2972 ray2972
theorem signs2972 : ∀ j, Signs p2972 (bank2972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2973 := params 28
abbrev ray2973 := rays 28
def bank2973 : Fin 2 → Cell := twoBank p2973 ray2973
theorem signs2973 : ∀ j, Signs p2973 (bank2973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2974 := params 29
abbrev ray2974 := rays 29
def bank2974 : Fin 2 → Cell := twoBank p2974 ray2974
theorem signs2974 : ∀ j, Signs p2974 (bank2974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2975 := params 30
abbrev ray2975 := rays 30
def bank2975 : Fin 2 → Cell := twoBank p2975 ray2975
theorem signs2975 : ∀ j, Signs p2975 (bank2975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2976 := params 31
abbrev ray2976 := rays 31
def bank2976 : Fin 2 → Cell := twoBank p2976 ray2976
theorem signs2976 : ∀ j, Signs p2976 (bank2976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02945_02976
