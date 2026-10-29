/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03041_03072
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99490206045313,99489998911224,99489791750827,99489584564123,99489377351113,99489170111798,99488962846180,99488755554260,99488548236039,99488340891519,99488133520701,99487926123586,99487718700175,99487511250470,99487303774471,99487096272181,99486888743600,99486681188730,99486473607572,99486266000127,99486058366396,99485850706381,99485643020083,99485435307503,99485227568643,99485019803504,99484812012087,99484604194393,99484396350424,99484188480180,99483980583664,99483772660876,99483564711818]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3040+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3041 := params 0
abbrev ray3041 := rays 0
def bank3041 : Fin 2 → Cell := twoBank p3041 ray3041
theorem signs3041 : ∀ j, Signs p3041 (bank3041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3042 := params 1
abbrev ray3042 := rays 1
def bank3042 : Fin 2 → Cell := twoBank p3042 ray3042
theorem signs3042 : ∀ j, Signs p3042 (bank3042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3043 := params 2
abbrev ray3043 := rays 2
def bank3043 : Fin 2 → Cell := twoBank p3043 ray3043
theorem signs3043 : ∀ j, Signs p3043 (bank3043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3044 := params 3
abbrev ray3044 := rays 3
def bank3044 : Fin 2 → Cell := twoBank p3044 ray3044
theorem signs3044 : ∀ j, Signs p3044 (bank3044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3045 := params 4
abbrev ray3045 := rays 4
def bank3045 : Fin 2 → Cell := twoBank p3045 ray3045
theorem signs3045 : ∀ j, Signs p3045 (bank3045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3046 := params 5
abbrev ray3046 := rays 5
def bank3046 : Fin 2 → Cell := twoBank p3046 ray3046
theorem signs3046 : ∀ j, Signs p3046 (bank3046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3047 := params 6
abbrev ray3047 := rays 6
def bank3047 : Fin 2 → Cell := twoBank p3047 ray3047
theorem signs3047 : ∀ j, Signs p3047 (bank3047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3048 := params 7
abbrev ray3048 := rays 7
def bank3048 : Fin 2 → Cell := twoBank p3048 ray3048
theorem signs3048 : ∀ j, Signs p3048 (bank3048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3049 := params 8
abbrev ray3049 := rays 8
def bank3049 : Fin 2 → Cell := twoBank p3049 ray3049
theorem signs3049 : ∀ j, Signs p3049 (bank3049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3050 := params 9
abbrev ray3050 := rays 9
def bank3050 : Fin 2 → Cell := twoBank p3050 ray3050
theorem signs3050 : ∀ j, Signs p3050 (bank3050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3051 := params 10
abbrev ray3051 := rays 10
def bank3051 : Fin 2 → Cell := twoBank p3051 ray3051
theorem signs3051 : ∀ j, Signs p3051 (bank3051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3052 := params 11
abbrev ray3052 := rays 11
def bank3052 : Fin 2 → Cell := twoBank p3052 ray3052
theorem signs3052 : ∀ j, Signs p3052 (bank3052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3053 := params 12
abbrev ray3053 := rays 12
def bank3053 : Fin 2 → Cell := twoBank p3053 ray3053
theorem signs3053 : ∀ j, Signs p3053 (bank3053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3054 := params 13
abbrev ray3054 := rays 13
def bank3054 : Fin 2 → Cell := twoBank p3054 ray3054
theorem signs3054 : ∀ j, Signs p3054 (bank3054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3055 := params 14
abbrev ray3055 := rays 14
def bank3055 : Fin 2 → Cell := twoBank p3055 ray3055
theorem signs3055 : ∀ j, Signs p3055 (bank3055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3056 := params 15
abbrev ray3056 := rays 15
def bank3056 : Fin 2 → Cell := twoBank p3056 ray3056
theorem signs3056 : ∀ j, Signs p3056 (bank3056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3057 := params 16
abbrev ray3057 := rays 16
def bank3057 : Fin 2 → Cell := twoBank p3057 ray3057
theorem signs3057 : ∀ j, Signs p3057 (bank3057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3058 := params 17
abbrev ray3058 := rays 17
def bank3058 : Fin 2 → Cell := twoBank p3058 ray3058
theorem signs3058 : ∀ j, Signs p3058 (bank3058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3059 := params 18
abbrev ray3059 := rays 18
def bank3059 : Fin 2 → Cell := twoBank p3059 ray3059
theorem signs3059 : ∀ j, Signs p3059 (bank3059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3060 := params 19
abbrev ray3060 := rays 19
def bank3060 : Fin 2 → Cell := twoBank p3060 ray3060
theorem signs3060 : ∀ j, Signs p3060 (bank3060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3061 := params 20
abbrev ray3061 := rays 20
def bank3061 : Fin 2 → Cell := twoBank p3061 ray3061
theorem signs3061 : ∀ j, Signs p3061 (bank3061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3062 := params 21
abbrev ray3062 := rays 21
def bank3062 : Fin 2 → Cell := twoBank p3062 ray3062
theorem signs3062 : ∀ j, Signs p3062 (bank3062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3063 := params 22
abbrev ray3063 := rays 22
def bank3063 : Fin 2 → Cell := twoBank p3063 ray3063
theorem signs3063 : ∀ j, Signs p3063 (bank3063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3064 := params 23
abbrev ray3064 := rays 23
def bank3064 : Fin 2 → Cell := twoBank p3064 ray3064
theorem signs3064 : ∀ j, Signs p3064 (bank3064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3065 := params 24
abbrev ray3065 := rays 24
def bank3065 : Fin 2 → Cell := twoBank p3065 ray3065
theorem signs3065 : ∀ j, Signs p3065 (bank3065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3066 := params 25
abbrev ray3066 := rays 25
def bank3066 : Fin 2 → Cell := twoBank p3066 ray3066
theorem signs3066 : ∀ j, Signs p3066 (bank3066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3067 := params 26
abbrev ray3067 := rays 26
def bank3067 : Fin 2 → Cell := twoBank p3067 ray3067
theorem signs3067 : ∀ j, Signs p3067 (bank3067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3068 := params 27
abbrev ray3068 := rays 27
def bank3068 : Fin 2 → Cell := twoBank p3068 ray3068
theorem signs3068 : ∀ j, Signs p3068 (bank3068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3069 := params 28
abbrev ray3069 := rays 28
def bank3069 : Fin 2 → Cell := twoBank p3069 ray3069
theorem signs3069 : ∀ j, Signs p3069 (bank3069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3070 := params 29
abbrev ray3070 := rays 29
def bank3070 : Fin 2 → Cell := twoBank p3070 ray3070
theorem signs3070 : ∀ j, Signs p3070 (bank3070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3071 := params 30
abbrev ray3071 := rays 30
def bank3071 : Fin 2 → Cell := twoBank p3071 ray3071
theorem signs3071 : ∀ j, Signs p3071 (bank3071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3072 := params 31
abbrev ray3072 := rays 31
def bank3072 : Fin 2 → Cell := twoBank p3072 ray3072
theorem signs3072 : ∀ j, Signs p3072 (bank3072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03041_03072
