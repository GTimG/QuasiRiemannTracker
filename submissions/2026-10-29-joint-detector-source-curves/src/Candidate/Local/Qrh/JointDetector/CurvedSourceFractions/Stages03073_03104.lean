/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03073_03104
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99483564711818,99483356736490,99483148734895,99482940707033,99482732652906,99482524572515,99482316465861,99482108332945,99481900173769,99481691988334,99481483776641,99481275538692,99481067274488,99480858984030,99480650667319,99480442324356,99480233955143,99480025559681,99479817137972,99479608690016,99479400215815,99479191715370,99478983188683,99478774635754,99478566056585,99478357451177,99478148819532,99477940161650,99477731477533,99477522767183,99477314030600,99477105267786,99476896478742]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3072+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3073 := params 0
abbrev ray3073 := rays 0
def bank3073 : Fin 2 → Cell := twoBank p3073 ray3073
theorem signs3073 : ∀ j, Signs p3073 (bank3073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3074 := params 1
abbrev ray3074 := rays 1
def bank3074 : Fin 2 → Cell := twoBank p3074 ray3074
theorem signs3074 : ∀ j, Signs p3074 (bank3074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3075 := params 2
abbrev ray3075 := rays 2
def bank3075 : Fin 2 → Cell := twoBank p3075 ray3075
theorem signs3075 : ∀ j, Signs p3075 (bank3075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3076 := params 3
abbrev ray3076 := rays 3
def bank3076 : Fin 2 → Cell := twoBank p3076 ray3076
theorem signs3076 : ∀ j, Signs p3076 (bank3076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3077 := params 4
abbrev ray3077 := rays 4
def bank3077 : Fin 2 → Cell := twoBank p3077 ray3077
theorem signs3077 : ∀ j, Signs p3077 (bank3077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3078 := params 5
abbrev ray3078 := rays 5
def bank3078 : Fin 2 → Cell := twoBank p3078 ray3078
theorem signs3078 : ∀ j, Signs p3078 (bank3078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3079 := params 6
abbrev ray3079 := rays 6
def bank3079 : Fin 2 → Cell := twoBank p3079 ray3079
theorem signs3079 : ∀ j, Signs p3079 (bank3079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3080 := params 7
abbrev ray3080 := rays 7
def bank3080 : Fin 2 → Cell := twoBank p3080 ray3080
theorem signs3080 : ∀ j, Signs p3080 (bank3080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3081 := params 8
abbrev ray3081 := rays 8
def bank3081 : Fin 2 → Cell := twoBank p3081 ray3081
theorem signs3081 : ∀ j, Signs p3081 (bank3081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3082 := params 9
abbrev ray3082 := rays 9
def bank3082 : Fin 2 → Cell := twoBank p3082 ray3082
theorem signs3082 : ∀ j, Signs p3082 (bank3082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3083 := params 10
abbrev ray3083 := rays 10
def bank3083 : Fin 2 → Cell := twoBank p3083 ray3083
theorem signs3083 : ∀ j, Signs p3083 (bank3083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3084 := params 11
abbrev ray3084 := rays 11
def bank3084 : Fin 2 → Cell := twoBank p3084 ray3084
theorem signs3084 : ∀ j, Signs p3084 (bank3084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3085 := params 12
abbrev ray3085 := rays 12
def bank3085 : Fin 2 → Cell := twoBank p3085 ray3085
theorem signs3085 : ∀ j, Signs p3085 (bank3085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3086 := params 13
abbrev ray3086 := rays 13
def bank3086 : Fin 2 → Cell := twoBank p3086 ray3086
theorem signs3086 : ∀ j, Signs p3086 (bank3086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3087 := params 14
abbrev ray3087 := rays 14
def bank3087 : Fin 2 → Cell := twoBank p3087 ray3087
theorem signs3087 : ∀ j, Signs p3087 (bank3087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3088 := params 15
abbrev ray3088 := rays 15
def bank3088 : Fin 2 → Cell := twoBank p3088 ray3088
theorem signs3088 : ∀ j, Signs p3088 (bank3088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3089 := params 16
abbrev ray3089 := rays 16
def bank3089 : Fin 2 → Cell := twoBank p3089 ray3089
theorem signs3089 : ∀ j, Signs p3089 (bank3089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3090 := params 17
abbrev ray3090 := rays 17
def bank3090 : Fin 2 → Cell := twoBank p3090 ray3090
theorem signs3090 : ∀ j, Signs p3090 (bank3090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3091 := params 18
abbrev ray3091 := rays 18
def bank3091 : Fin 2 → Cell := twoBank p3091 ray3091
theorem signs3091 : ∀ j, Signs p3091 (bank3091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3092 := params 19
abbrev ray3092 := rays 19
def bank3092 : Fin 2 → Cell := twoBank p3092 ray3092
theorem signs3092 : ∀ j, Signs p3092 (bank3092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3093 := params 20
abbrev ray3093 := rays 20
def bank3093 : Fin 2 → Cell := twoBank p3093 ray3093
theorem signs3093 : ∀ j, Signs p3093 (bank3093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3094 := params 21
abbrev ray3094 := rays 21
def bank3094 : Fin 2 → Cell := twoBank p3094 ray3094
theorem signs3094 : ∀ j, Signs p3094 (bank3094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3095 := params 22
abbrev ray3095 := rays 22
def bank3095 : Fin 2 → Cell := twoBank p3095 ray3095
theorem signs3095 : ∀ j, Signs p3095 (bank3095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3096 := params 23
abbrev ray3096 := rays 23
def bank3096 : Fin 2 → Cell := twoBank p3096 ray3096
theorem signs3096 : ∀ j, Signs p3096 (bank3096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3097 := params 24
abbrev ray3097 := rays 24
def bank3097 : Fin 2 → Cell := twoBank p3097 ray3097
theorem signs3097 : ∀ j, Signs p3097 (bank3097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3098 := params 25
abbrev ray3098 := rays 25
def bank3098 : Fin 2 → Cell := twoBank p3098 ray3098
theorem signs3098 : ∀ j, Signs p3098 (bank3098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3099 := params 26
abbrev ray3099 := rays 26
def bank3099 : Fin 2 → Cell := twoBank p3099 ray3099
theorem signs3099 : ∀ j, Signs p3099 (bank3099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3100 := params 27
abbrev ray3100 := rays 27
def bank3100 : Fin 2 → Cell := twoBank p3100 ray3100
theorem signs3100 : ∀ j, Signs p3100 (bank3100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3101 := params 28
abbrev ray3101 := rays 28
def bank3101 : Fin 2 → Cell := twoBank p3101 ray3101
theorem signs3101 : ∀ j, Signs p3101 (bank3101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3102 := params 29
abbrev ray3102 := rays 29
def bank3102 : Fin 2 → Cell := twoBank p3102 ray3102
theorem signs3102 : ∀ j, Signs p3102 (bank3102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3103 := params 30
abbrev ray3103 := rays 30
def bank3103 : Fin 2 → Cell := twoBank p3103 ray3103
theorem signs3103 : ∀ j, Signs p3103 (bank3103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3104 := params 31
abbrev ray3104 := rays 31
def bank3104 : Fin 2 → Cell := twoBank p3104 ray3104
theorem signs3104 : ∀ j, Signs p3104 (bank3104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03073_03104
