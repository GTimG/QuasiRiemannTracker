/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03009_03040
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99496820437774,99496614146222,99496407828321,99496201484072,99495995113476,99495788716535,99495582293250,99495375843623,99495169367654,99494962865345,99494756336698,99494549781713,99494343200392,99494136592736,99493929958746,99493723298424,99493516611771,99493309898788,99493103159476,99492896393837,99492689601872,99492482783582,99492275938968,99492069068032,99491862170775,99491655247198,99491448297303,99491241321090,99491034318562,99490827289719,99490620234562,99490413153093,99490206045313]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3008+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3009 := params 0
abbrev ray3009 := rays 0
def bank3009 : Fin 2 → Cell := twoBank p3009 ray3009
theorem signs3009 : ∀ j, Signs p3009 (bank3009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3010 := params 1
abbrev ray3010 := rays 1
def bank3010 : Fin 2 → Cell := twoBank p3010 ray3010
theorem signs3010 : ∀ j, Signs p3010 (bank3010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3011 := params 2
abbrev ray3011 := rays 2
def bank3011 : Fin 2 → Cell := twoBank p3011 ray3011
theorem signs3011 : ∀ j, Signs p3011 (bank3011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3012 := params 3
abbrev ray3012 := rays 3
def bank3012 : Fin 2 → Cell := twoBank p3012 ray3012
theorem signs3012 : ∀ j, Signs p3012 (bank3012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3013 := params 4
abbrev ray3013 := rays 4
def bank3013 : Fin 2 → Cell := twoBank p3013 ray3013
theorem signs3013 : ∀ j, Signs p3013 (bank3013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3014 := params 5
abbrev ray3014 := rays 5
def bank3014 : Fin 2 → Cell := twoBank p3014 ray3014
theorem signs3014 : ∀ j, Signs p3014 (bank3014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3015 := params 6
abbrev ray3015 := rays 6
def bank3015 : Fin 2 → Cell := twoBank p3015 ray3015
theorem signs3015 : ∀ j, Signs p3015 (bank3015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3016 := params 7
abbrev ray3016 := rays 7
def bank3016 : Fin 2 → Cell := twoBank p3016 ray3016
theorem signs3016 : ∀ j, Signs p3016 (bank3016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3017 := params 8
abbrev ray3017 := rays 8
def bank3017 : Fin 2 → Cell := twoBank p3017 ray3017
theorem signs3017 : ∀ j, Signs p3017 (bank3017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3018 := params 9
abbrev ray3018 := rays 9
def bank3018 : Fin 2 → Cell := twoBank p3018 ray3018
theorem signs3018 : ∀ j, Signs p3018 (bank3018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3019 := params 10
abbrev ray3019 := rays 10
def bank3019 : Fin 2 → Cell := twoBank p3019 ray3019
theorem signs3019 : ∀ j, Signs p3019 (bank3019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3020 := params 11
abbrev ray3020 := rays 11
def bank3020 : Fin 2 → Cell := twoBank p3020 ray3020
theorem signs3020 : ∀ j, Signs p3020 (bank3020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3021 := params 12
abbrev ray3021 := rays 12
def bank3021 : Fin 2 → Cell := twoBank p3021 ray3021
theorem signs3021 : ∀ j, Signs p3021 (bank3021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3022 := params 13
abbrev ray3022 := rays 13
def bank3022 : Fin 2 → Cell := twoBank p3022 ray3022
theorem signs3022 : ∀ j, Signs p3022 (bank3022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3023 := params 14
abbrev ray3023 := rays 14
def bank3023 : Fin 2 → Cell := twoBank p3023 ray3023
theorem signs3023 : ∀ j, Signs p3023 (bank3023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3024 := params 15
abbrev ray3024 := rays 15
def bank3024 : Fin 2 → Cell := twoBank p3024 ray3024
theorem signs3024 : ∀ j, Signs p3024 (bank3024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3025 := params 16
abbrev ray3025 := rays 16
def bank3025 : Fin 2 → Cell := twoBank p3025 ray3025
theorem signs3025 : ∀ j, Signs p3025 (bank3025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3026 := params 17
abbrev ray3026 := rays 17
def bank3026 : Fin 2 → Cell := twoBank p3026 ray3026
theorem signs3026 : ∀ j, Signs p3026 (bank3026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3027 := params 18
abbrev ray3027 := rays 18
def bank3027 : Fin 2 → Cell := twoBank p3027 ray3027
theorem signs3027 : ∀ j, Signs p3027 (bank3027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3028 := params 19
abbrev ray3028 := rays 19
def bank3028 : Fin 2 → Cell := twoBank p3028 ray3028
theorem signs3028 : ∀ j, Signs p3028 (bank3028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3029 := params 20
abbrev ray3029 := rays 20
def bank3029 : Fin 2 → Cell := twoBank p3029 ray3029
theorem signs3029 : ∀ j, Signs p3029 (bank3029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3030 := params 21
abbrev ray3030 := rays 21
def bank3030 : Fin 2 → Cell := twoBank p3030 ray3030
theorem signs3030 : ∀ j, Signs p3030 (bank3030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3031 := params 22
abbrev ray3031 := rays 22
def bank3031 : Fin 2 → Cell := twoBank p3031 ray3031
theorem signs3031 : ∀ j, Signs p3031 (bank3031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3032 := params 23
abbrev ray3032 := rays 23
def bank3032 : Fin 2 → Cell := twoBank p3032 ray3032
theorem signs3032 : ∀ j, Signs p3032 (bank3032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3033 := params 24
abbrev ray3033 := rays 24
def bank3033 : Fin 2 → Cell := twoBank p3033 ray3033
theorem signs3033 : ∀ j, Signs p3033 (bank3033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3034 := params 25
abbrev ray3034 := rays 25
def bank3034 : Fin 2 → Cell := twoBank p3034 ray3034
theorem signs3034 : ∀ j, Signs p3034 (bank3034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3035 := params 26
abbrev ray3035 := rays 26
def bank3035 : Fin 2 → Cell := twoBank p3035 ray3035
theorem signs3035 : ∀ j, Signs p3035 (bank3035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3036 := params 27
abbrev ray3036 := rays 27
def bank3036 : Fin 2 → Cell := twoBank p3036 ray3036
theorem signs3036 : ∀ j, Signs p3036 (bank3036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3037 := params 28
abbrev ray3037 := rays 28
def bank3037 : Fin 2 → Cell := twoBank p3037 ray3037
theorem signs3037 : ∀ j, Signs p3037 (bank3037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3038 := params 29
abbrev ray3038 := rays 29
def bank3038 : Fin 2 → Cell := twoBank p3038 ray3038
theorem signs3038 : ∀ j, Signs p3038 (bank3038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3039 := params 30
abbrev ray3039 := rays 30
def bank3039 : Fin 2 → Cell := twoBank p3039 ray3039
theorem signs3039 : ∀ j, Signs p3039 (bank3039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3040 := params 31
abbrev ray3040 := rays 31
def bank3040 : Fin 2 → Cell := twoBank p3040 ray3040
theorem signs3040 : ∀ j, Signs p3040 (bank3040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03009_03040
